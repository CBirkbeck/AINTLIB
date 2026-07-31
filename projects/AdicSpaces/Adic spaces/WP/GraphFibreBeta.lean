/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WP.HeadReducedMaximal
import «Adic spaces».WP.KappaResidue
import «Adic spaces».FJP.SpectralExtension
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

section KappaBridge

open FiniteJet.SpectralExtension

open scoped NormedField Valued

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]
variable (w : ℕ → ℕ) (N : ℕ)

set_option maxHeartbeats 1600000 in
/-- **BETA brick (ii), the continuity bridge**: the residue map of the head
onto the spectral residue field `κ(𝔭)` is continuous.  (Factor through the
quotient topology: the projection is continuous, and the identity onto the
spectral side is `K`-linear from a finite-dimensional Hausdorff space.) -/
theorem continuous_mkKappaP (ϖ : Uniformizer K)
    [hdvr : IsDiscreteValuationRing 𝒪[K]]
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (𝔭 : Ideal (WPHead K w N)) [h𝔭 : 𝔭.IsMaximal] :
    haveI : FiniteDimensional K (KappaP w N 𝔭) :=
      module_finite_residue_head w N ϖ hK₀ 𝔭
    letI := extNormedField K (KappaP w N 𝔭)
    Continuous (mkKappaP w N 𝔭) := by
  haveI hfd : FiniteDimensional K (KappaP w N 𝔭) :=
    module_finite_residue_head w N ϖ hK₀ 𝔭
  letI nfκ : NormedField (KappaP w N 𝔭) := extNormedField K (KappaP w N 𝔭)
  classical
  haveI hNoeth : IsNoetherianRing (WPHead K w N) :=
    isNoetherianRing_WPHead w N ϖ hK₀
  haveI hclosed : IsClosed ((𝔭 : Ideal (WPHead K w N)) : Set (WPHead K w N)) :=
    isClosed_ideal_of_noetherian_normed 𝔭
  letI : Algebra K (WPHead K w N ⧸ 𝔭) :=
    ((Ideal.Quotient.mk 𝔭).comp (constHead K w N)).toAlgebra
  have hconst : Continuous (⇑(constHead K w N)) :=
    AddMonoidHomClass.continuous_of_bound (constHead K w N) 1
      fun c => by rw [one_mul]; exact norm_constHead_le w N c
  haveI hsmulQ : ContinuousSMul K (WPHead K w N ⧸ 𝔭) := by
    refine ⟨?_⟩
    have halg : Continuous (fun c : K =>
        ((Ideal.Quotient.mk 𝔭) (constHead K w N c) : WPHead K w N ⧸ 𝔭)) :=
      continuous_quot_mk.comp hconst
    have hmul : (fun p : K × (WPHead K w N ⧸ 𝔭) => p.1 • p.2) =
        fun p : K × (WPHead K w N ⧸ 𝔭) =>
          (Ideal.Quotient.mk 𝔭) (constHead K w N p.1) * p.2 := by
      funext p
      exact Algebra.smul_def p.1 p.2
    rw [hmul]
    exact (halg.comp continuous_fst).mul continuous_snd
  haveI hug : IsUniformAddGroup (KappaP w N 𝔭) :=
    SeminormedAddCommGroup.to_isUniformAddGroup
  haveI htag : IsTopologicalAddGroup (KappaP w N 𝔭) :=
    SeminormedAddCommGroup.toIsTopologicalAddGroup
  haveI hcs : ContinuousSMul K (KappaP w N 𝔭) :=
    extContinuousSMul K (KappaP w N 𝔭)
  haveI hfd' : FiniteDimensional K (WPHead K w N ⧸ 𝔭) := hfd
  set ι : (WPHead K w N ⧸ 𝔭) →ₗ[K] KappaP w N 𝔭 :=
    { toFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } with hιdef
  have hbridge : Continuous ι := LinearMap.continuous_of_finiteDimensional ι
  have hmk : Continuous (fun a : WPHead K w N =>
      ((Ideal.Quotient.mk 𝔭) a : WPHead K w N ⧸ 𝔭)) := continuous_quot_mk
  exact hbridge.comp hmk

end KappaBridge

end WeightedParity
