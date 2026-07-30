/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WP.HeadReducedMaximal
import «Adic spaces».WedhornBanachTheorem

/-!
# The trivial special fibre of the graph model (BETA)

([hrw-decomposition] BETA, adjudicated route R1′.)  This file builds the
bricks for the level-one bijectivity `A/𝔭 ≅ Q/𝔭Q` of the graph model at a
maximal contraction: closedness of ideals in normed noetherian Tate rings
(the faithful Wedhorn 6.17 engine), the residue-field package, the bounded
evaluation, and the closed-plus-dense argument.
-/

@[expose] public section

namespace WeightedParity

open FiniteJetOver

/-- **Wedhorn 6.17, faithful, normed form**: every ideal of a complete
normed noetherian Tate ring is closed. -/
theorem isClosed_ideal_of_noetherian_normed {C : Type*} [NormedCommRing C]
    [CompleteSpace C] [IsTateRing C] [IsNoetherianRing C]
    (J : Ideal C) : IsClosed (J : Set C) := by
  haveI : ContinuousSMul C C := ⟨continuous_mul⟩
  refine ValuationSpectrum.fg_topologicalClosure_isClosed J ?_
  have hfg : (Submodule.topologicalClosure J).FG :=
    IsNoetherian.noetherian _
  exact Module.Finite.iff_fg.mpr hfg

/-- Bounded sets push forward along continuous open ring homomorphisms. -/
theorem TopologicalRing.IsBounded.image_of_isOpenMap {A B : Type*}
    [CommRing A] [TopologicalSpace A] [CommRing B] [TopologicalSpace B]
    (φ : A →+* B) (hcont : Continuous φ) (hopen : IsOpenMap φ)
    {S : Set A} (hS : TopologicalRing.IsBounded S) :
    TopologicalRing.IsBounded (⇑φ '' S) := by
  intro U' hU'
  have hpre : φ ⁻¹' U' ∈ nhds (0 : A) := by
    have h0 : φ 0 = 0 := map_zero φ
    exact ContinuousAt.preimage_mem_nhds hcont.continuousAt (h0 ▸ hU')
  obtain ⟨V, hV, hSV⟩ := hS (φ ⁻¹' U') hpre
  refine ⟨⇑φ '' V, ?_, ?_⟩
  · have h1 := hopen.image_mem_nhds hV
    rwa [map_zero φ] at h1
  · rintro z hz
    obtain ⟨y, ⟨x, hxS, rfl⟩, w, ⟨v, hvV, rfl⟩, rfl⟩ := Set.mem_mul.mp hz
    have h2 : x * v ∈ φ ⁻¹' U' := hSV (Set.mul_mem_mul hxS hvV)
    rw [← map_mul]
    exact h2

/-- Power-bounded elements push forward along continuous open ring
homomorphisms. -/
theorem TopologicalRing.IsPowerBounded.image_of_isOpenMap {A B : Type*}
    [CommRing A] [TopologicalSpace A] [CommRing B] [TopologicalSpace B]
    (φ : A →+* B) (hcont : Continuous φ) (hopen : IsOpenMap φ)
    {x : A} (hx : TopologicalRing.IsPowerBounded x) :
    TopologicalRing.IsPowerBounded (φ x) := by
  have hrange : Set.range ((φ x) ^ · : ℕ → B) =
      ⇑φ '' Set.range (x ^ · : ℕ → A) := by
    ext y
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨x ^ n, ⟨n, rfl⟩, map_pow φ x n⟩
    · rintro ⟨-, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, (map_pow φ x n).symm⟩
  show TopologicalRing.IsBounded (Set.range ((φ x) ^ · : ℕ → B))
  rw [hrange]
  exact TopologicalRing.IsBounded.image_of_isOpenMap φ hcont hopen hx

end WeightedParity
