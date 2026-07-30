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
