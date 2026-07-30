/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WP.HeadReducedNotMem
import «Adic spaces».FJP.CDVFDichotomy

/-!
# Head-localization reducedness through maximal ideals

([hrw-decomposition] block D: the maximal-only rewire, per the L3
adjudication — the all-primes forms need Rees's analytically-unramified
theorem and stay parked; the consumer only needs contractions of maximals.)

`headLocsReduced'` re-proves the `HeadLocsReduced` hypothesis through the
maximal-ideal route: contractions of `QHead`-maximals are maximal
(`comap_headToQ_isMaximal`, WIP: residue finiteness through the
`T_N⟨T⟩`-tower), and the completed locals of the head at maximals are
reduced — the `W ∉ 𝔭` case is fully proven
(`head_completedLocal_reduced_of_isMaximal_of_wa_notMem`), the `W ∈ 𝔭`
quadratic-tower case is the remaining deep leaf.
-/

@[expose] public section

namespace WeightedParity

open ValuationSpectrum FiniteJetOver IsLocalRing

open scoped NormedField Valued

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]
variable (w : ℕ → ℕ) (N : ℕ)

section FiniteEmbedding

/-- The fibre of the zero-weight head over a head-maximal is Artinian. -/
theorem isArtinianRing_zeroHead_fibre (𝔪 : Ideal (WPHead K w N))
    [h𝔪 : 𝔪.IsMaximal] :
    letI : Algebra (WPHead K w N) (WPHead K (fun _ => 0) N) :=
      (headToZeroHead w N).toAlgebra
    IsArtinianRing (WPHead K (fun _ => 0) N ⧸
      Ideal.map (headToZeroHead w N) 𝔪) := by
  classical
  letI : Algebra (WPHead K w N) (WPHead K (fun _ => 0) N) :=
    (headToZeroHead w N).toAlgebra
  letI : Field (WPHead K w N ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  haveI hfin : Module.Finite (WPHead K w N) (WPHead K (fun _ => 0) N) :=
    module_finite_zero_head (K := K) (w := w) N
  letI : Algebra (WPHead K w N ⧸ 𝔪)
      (WPHead K (fun _ => 0) N ⧸ Ideal.map (headToZeroHead w N) 𝔪) :=
    (Ideal.quotientMap (Ideal.map (headToZeroHead w N) 𝔪)
      (headToZeroHead w N) Ideal.le_comap_map).toAlgebra
  haveI h2 : Module.Finite (WPHead K w N ⧸ 𝔪)
      (WPHead K (fun _ => 0) N ⧸ Ideal.map (headToZeroHead w N) 𝔪) := by
    obtain ⟨T, hT⟩ := hfin.fg_top
    refine ⟨⟨T.image (Ideal.Quotient.mk
      (Ideal.map (headToZeroHead w N) 𝔪)), ?_⟩⟩
    rw [eq_top_iff]
    intro z _
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hb : b ∈ Submodule.span (WPHead K w N) (T : Set _) := by
      rw [hT]
      exact Submodule.mem_top
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hb
    · intro t ht
      exact Submodule.subset_span (Finset.mem_coe.mpr
        (Finset.mem_image_of_mem _ ht))
    · rw [_root_.map_zero]
      exact Submodule.zero_mem _
    · intro u v _ _ hu hv
      rw [_root_.map_add]
      exact Submodule.add_mem _ hu hv
    · intro a x _ hx
      have h5 : Ideal.Quotient.mk (Ideal.map (headToZeroHead w N) 𝔪)
          (a • x) = (Ideal.Quotient.mk 𝔪 a) •
            (Ideal.Quotient.mk (Ideal.map (headToZeroHead w N) 𝔪) x) := by
        show Ideal.Quotient.mk _ (headToZeroHead w N a * x) = _
        rw [map_mul]
        rfl
      rw [h5]
      exact Submodule.smul_mem _ _ hx
  exact IsArtinianRing.of_finite (WPHead K w N ⧸ 𝔪)
    (WPHead K (fun _ => 0) N ⧸ Ideal.map (headToZeroHead w N) 𝔪)

/-- Maximals of the zero-weight head over the pushed maximal contract to it. -/
theorem comap_eq_of_le_map (𝔪 : Ideal (WPHead K w N)) [h𝔪 : 𝔪.IsMaximal]
    (𝔫 : Ideal (WPHead K (fun _ => 0) N)) (h𝔫 : 𝔫.IsMaximal)
    (hge : Ideal.map (headToZeroHead w N) 𝔪 ≤ 𝔫) :
    Ideal.comap (headToZeroHead w N) 𝔫 = 𝔪 := by
  have h1 : 𝔪 ≤ Ideal.comap (headToZeroHead w N) 𝔫 :=
    le_trans Ideal.le_comap_map (Ideal.comap_mono hge)
  have h2 : Ideal.comap (headToZeroHead w N) 𝔫 ≠ ⊤ := by
    intro htop
    have h3 : (1 : WPHead K w N) ∈ Ideal.comap (headToZeroHead w N) 𝔫 := by
      rw [htop]
      exact Submodule.mem_top
    rw [Ideal.mem_comap, map_one] at h3
    exact h𝔫.ne_top (Ideal.eq_top_of_isUnit_mem _ h3 isUnit_one)
  exact (h𝔪.eq_of_le h2 h1).symm

/-- **Artin–Rees pullback**: an element of the head whose image lies in a
deep power of the extended ideal lies in a controlled power of the ideal. -/
theorem exists_artinRees_pullback (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (𝔪 : Ideal (WPHead K w N)) :
    ∃ k : ℕ, ∀ n, ∀ a : WPHead K w N,
      headToZeroHead w N a ∈ (Ideal.map (headToZeroHead w N) 𝔪) ^ (n + k) →
      a ∈ 𝔪 ^ n := by
  classical
  letI : Algebra (WPHead K w N) (WPHead K (fun _ => 0) N) :=
    (headToZeroHead w N).toAlgebra
  haveI hfin : Module.Finite (WPHead K w N) (WPHead K (fun _ => 0) N) :=
    module_finite_zero_head (K := K) (w := w) N
  haveI hstr : IsStronglyNoetherian (WPHead K w N) :=
    isStronglyNoetherian_WPHead (w := w) (N := N) ϖ hK₀
  haveI hnoeth : IsNoetherianRing (WPHead K w N) :=
    IsStronglyNoetherian.isNoetherianRing (WPHead K w N)
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (I := 𝔪)
    (M := WPHead K (fun _ => 0) N)
    (LinearMap.range (Algebra.linearMap (WPHead K w N)
      (WPHead K (fun _ => 0) N)))
  refine ⟨k, fun n a ha => ?_⟩
  have h1 : headToZeroHead w N a ∈
      (𝔪 ^ (n + k) • ⊤ : Submodule (WPHead K w N)
        (WPHead K (fun _ => 0) N)) := by
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem,
      Ideal.map_pow]
    exact ha
  have h2 : headToZeroHead w N a ∈
      ((𝔪 ^ (n + k) • ⊤ : Submodule (WPHead K w N)
        (WPHead K (fun _ => 0) N)) ⊓
        LinearMap.range (Algebra.linearMap (WPHead K w N)
          (WPHead K (fun _ => 0) N))) :=
    ⟨h1, ⟨a, rfl⟩⟩
  rw [hk (n + k) (Nat.le_add_left k n), Nat.add_sub_cancel] at h2
  have h3 : headToZeroHead w N a ∈
      (𝔪 ^ n • LinearMap.range (Algebra.linearMap (WPHead K w N)
        (WPHead K (fun _ => 0) N)) : Submodule (WPHead K w N)
          (WPHead K (fun _ => 0) N)) :=
    Submodule.smul_mono le_rfl inf_le_right h2
  rw [LinearMap.range_eq_map, ← Submodule.map_smul''] at h3
  obtain ⟨y, hy, hya⟩ := h3
  have hy2 : y ∈ 𝔪 ^ n := by
    have hle : (𝔪 ^ n • ⊤ : Submodule (WPHead K w N) (WPHead K w N)) ≤
        Submodule.restrictScalars (WPHead K w N) (𝔪 ^ n) := by
      refine Submodule.smul_le.mpr fun r hr x _ => ?_
      exact Ideal.mul_mem_right x _ hr
    exact hle hy
  have hae : a = y := headToZeroHead_injective w N hya.symm
  rw [hae]
  exact hy2

end FiniteEmbedding

/-- **L3.b at maximals — the deep leaf** ([WP] §6 quadratic tower;
[hrw-decomposition] L3.b): the completed local ring of the head at a maximal
ideal containing `W`.  WIP frontier. -/
theorem head_completedLocal_reduced_of_isMaximal_of_wa_mem
    (ϖ : Uniformizer K) [hdvr : IsDiscreteValuationRing 𝒪[K]]
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (𝔭 : Ideal (WPHead K w N)) (h𝔭 : 𝔭.IsMaximal)
    (hW : WaHead K w N ∈ 𝔭) :
    haveI := h𝔭.isPrime
    IsReduced (completedLocal (WPHead K w N) 𝔭) := by
  sorry

/-- **L3 at maximals**: every completed local ring of the head at a maximal
ideal is reduced. -/
theorem head_completedLocal_reduced_of_isMaximal
    (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (𝔭 : Ideal (WPHead K w N)) (h𝔭 : 𝔭.IsMaximal) :
    haveI := h𝔭.isPrime
    IsReduced (completedLocal (WPHead K w N) 𝔭) := by
  haveI hdvr : IsDiscreteValuationRing 𝒪[K] :=
    ϖ.isDiscreteValuationRing hK₀
  by_cases hW : WaHead K w N ∈ 𝔭
  · exact head_completedLocal_reduced_of_isMaximal_of_wa_mem
      w N ϖ hK₀ 𝔭 h𝔭 hW
  · exact head_completedLocal_reduced_of_isMaximal_of_wa_notMem
      w N ϖ hK₀ 𝔭 h𝔭 hW

/-- **D-prep — contraction maximality** ([hrw-decomposition]): the
contraction of a `QHead`-maximal to the head is maximal (residue finiteness
through the `T_N⟨T⟩`-tower Nullstellensatz).  WIP frontier. -/
theorem comap_headToQ_isMaximal (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational)
    (𝔮 : Ideal (QHead DH)) (h𝔮 : 𝔮.IsMaximal) :
    (𝔮.comap (headToQ DH)).IsMaximal := by
  sorry

/-- **L4 through maximals**: the head-localization reducedness hypothesis,
by the maximal-ideal route. -/
theorem headLocsReduced' (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    HeadLocsReduced K w := by
  intro N DH hDH
  haveI hQnoeth : IsNoetherianRing (QHead DH) :=
    isNoetherianRing_qHead ϖ hK₀ hDH
  suffices h : IsReduced (QHead DH) by
    exact isReduced_of_injective
      (headLocEquiv ϖ hK₀ DH hDH).toRingHom
      (headLocEquiv ϖ hK₀ DH hDH).injective
  refine isReduced_of_forall_completedLocal_reduced _ ?_
  intro 𝔮 h𝔮
  haveI := h𝔮.isPrime
  haveI hcm : (𝔮.comap (headToQ DH)).IsMaximal :=
    comap_headToQ_isMaximal w N ϖ hK₀ DH hDH 𝔮 h𝔮
  haveI hcp : (𝔮.comap (headToQ DH)).IsPrime := hcm.isPrime
  obtain ⟨e⟩ := qHead_completedLocal_comparison ϖ hK₀ DH hDH 𝔮 h𝔮
  haveI : IsReduced
      (completedLocal (WPHead K w N) (𝔮.comap (headToQ DH))) :=
    head_completedLocal_reduced_of_isMaximal w N ϖ hK₀ _ hcm
  exact isReduced_of_injective e.symm.toRingHom e.symm.injective

end WeightedParity
