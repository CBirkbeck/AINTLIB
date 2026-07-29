/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WP.CoeffLocalization
import «Adic spaces».WP.Reduced
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.LocalProperties.Basic

/-!
# Head-localization reducedness — the BGR 7.3.2/10 sub-campaign

Discharges the quarantined `HeadLocsReduced` hypothesis of the reducedness
endpoints: every rational localization of every affinoid head of the
weighted-parity algebra is reduced.  Classical source: [BGR, Corollary 7.3.2/10]
via completed-local comparison and analytic unramifiedness; the head-specific
route follows the 2026-07-28 plan review
(`.mathlib-quality/wp-reduced/chatgpt-review-2026-07-28.md` and
`hrw-decomposition.md`):

* `isReduced_of_forall_completedLocal_reduced` (L2, mathlib-grade): a noetherian
  ring whose completed local rings at all maximal ideals are reduced is reduced
  (Krull intersection + locality of vanishing);
* `headToQ` and `qHead_completedLocal_comparison` (L1): the completed local rings
  of the graph model `QHead` agree with those of the head at contracted primes
  (finite-level graph evaluation + inverse limits);
* `head_completedLocal_reduced` (L3, the frontier), split into the `W ∉ 𝔭`
  Z-elimination case (reduces to Tate-algebra completed locals) and the `W ∈ 𝔭`
  quadratic-tower case;
* `headLocsReduced` (L4): assembly through `headLocEquiv`.
-/

@[expose] public section

set_option maxSynthPendingDepth 8

namespace WeightedParity

open ValuationSpectrum FiniteJetOver IsLocalRing

/-! ### L2 — reducedness from reduced completed local rings (mathlib-grade) -/

/-- The completed local ring of `R` at a prime `𝔭`: the maximal-adic completion of
the localization. -/
noncomputable abbrev completedLocal (R : Type*) [CommRing R] (𝔭 : Ideal R)
    [𝔭.IsPrime] : Type _ :=
  AdicCompletion (maximalIdeal (Localization.AtPrime 𝔭)) (Localization.AtPrime 𝔭)

/-- **L2**: a noetherian commutative ring whose completed local rings at all maximal
ideals are reduced is reduced ([hrw-decomposition] L2: Krull intersection makes
`R_𝔪 → (R_𝔪)^` injective; vanishing at all maximal localizations is vanishing). -/
theorem isReduced_of_forall_completedLocal_reduced (R : Type*) [CommRing R]
    [IsNoetherianRing R]
    (h : ∀ (𝔪 : Ideal R) (_ : 𝔪.IsMaximal), IsReduced (completedLocal R 𝔪)) :
    IsReduced R := by
  refine ⟨fun x hx => ?_⟩
  have hloc : ∀ (𝔪 : Ideal R) (_ : 𝔪.IsMaximal),
      algebraMap R (Localization.AtPrime 𝔪) x = 0 := by
    intro 𝔪 h𝔪
    haveI := h𝔪
    haveI : IsNoetherianRing (Localization.AtPrime 𝔪) :=
      IsLocalization.isNoetherianRing 𝔪.primeCompl (Localization.AtPrime 𝔪)
        inferInstance
    set L := Localization.AtPrime 𝔪 with hL
    set I : Ideal L := maximalIdeal L with hI
    set y : L := algebraMap R L x with hy_def
    have hy : IsNilpotent y := hx.map (algebraMap R L)
    have hz : IsNilpotent (algebraMap L (AdicCompletion I L) y) :=
      hy.map (algebraMap L (AdicCompletion I L))
    haveI := h 𝔪 h𝔪
    have hz0 : algebraMap L (AdicCompletion I L) y = 0 := hz.eq_zero
    have hmem : y ∈ (⊥ : Submodule L L) := by
      rw [← Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (I := I) (M := L)
        (IsLocalRing.maximalIdeal.isMaximal L).ne_top]
      rw [Submodule.mem_iInf]
      intro n
      have hev := congrArg (AdicCompletion.eval I L n) hz0
      rw [show algebraMap L (AdicCompletion I L) y = AdicCompletion.of I L y from rfl,
        AdicCompletion.eval_of, map_zero] at hev
      exact (Submodule.Quotient.mk_eq_zero _).mp hev
    simpa using hmem
  have hbot : x ∈ (⊥ : Ideal R) := by
    refine Ideal.mem_of_localization_maximal fun P hP => ?_
    rw [Ideal.map_bot, Ideal.mem_bot]
    exact hloc P hP
  simpa using hbot

/-! ### L1 — the completed-local comparison for the graph model -/

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (w : ℕ → ℕ) (N : ℕ)

variable {K w N} in
/-- The canonical homomorphism from the head into its graph model (constants into
`𝒜_N⟨T⟩`, then the quotient). -/
noncomputable def headToQ (DH : RationalLocData (WPHead K w N)) :
    WPHead K w N →+* QHead DH :=
  (Ideal.Quotient.mk _).comp
    ((FiniteJet.GraphKoszul.polyToP (E := WPHead K w N) (m := DH.T.card)).comp
      MvPolynomial.C)

variable {K w N} in
/-- `headToQ` is the model's constant embedding (definitional identification with
the W15 layer). -/
theorem headToQ_eq_headConst (DH : RationalLocData (WPHead K w N)) :
    headToQ DH = headConst DH := rfl

variable {K w N} in
/-- **L1.a** ([hrw-decomposition], HRW-2): the denominator's image in the graph
model is a unit — the canonical-map unit transported along `headLocEquiv`
(the W16 law `headLocEquiv ∘ canonicalMap = headConst`). -/
theorem isUnit_headToQ_s (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    IsUnit (headToQ DH DH.s) := by
  haveI : HasLocLiftPowerBounded (WPHead K w N) := hasLocLiftPowerBounded_faithful
  have h1 : headToQ DH DH.s =
      headLocEquiv ϖ hK₀ DH hDH (DH.canonicalMap DH.s) := by
    rw [show headLocEquiv ϖ hK₀ DH hDH (DH.canonicalMap DH.s) =
      headLocFwd ϖ DH hDH (DH.canonicalMap DH.s) from rfl,
      show DH.canonicalMap DH.s = DH.coeRingHom
        (algebraMap (WPHead K w N) (Localization.Away DH.s) DH.s) from rfl,
      headLocFwd_coe, headLocFwdAlg_algebraMap]
    rfl
  rw [h1]
  exact (isUnit_canonicalMap_s DH DH (subset_refl _)).map
    (headLocEquiv ϖ hK₀ DH hDH)

variable {K w N} in
/-- **L1.a** (HRW-2): the denominator avoids the contraction of every proper
prime of the graph model — the fibre of the contraction lies in the localization
locus (the adversarial-note-safe primality form; maximality of the contraction
is deliberately NOT claimed). -/
theorem s_notMem_comap_headToQ (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational)
    (𝔮 : Ideal (QHead DH)) (h𝔮 : 𝔮.IsPrime) :
    DH.s ∉ 𝔮.comap (headToQ DH) := by
  intro hmem
  rw [Ideal.mem_comap] at hmem
  exact h𝔮.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem
    (isUnit_headToQ_s ϖ hK₀ DH hDH))

variable {K w N} in
/-- **L1** ([hrw-decomposition]): for a maximal ideal `𝔮` of the graph model, the
completed local ring of the head at the contraction agrees with that of the model
at `𝔮`.  (Finite-level: mod every power of `𝔮` the graph variables evaluate
uniquely since the denominator is a unit; then pass to inverse limits.) -/
theorem qHead_completedLocal_comparison (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational)
    (𝔮 : Ideal (QHead DH)) (h𝔮 : 𝔮.IsMaximal) :
    haveI : (𝔮.comap (headToQ DH)).IsPrime := 𝔮.comap_isPrime (headToQ DH)
    Nonempty
      (completedLocal (WPHead K w N) (𝔮.comap (headToQ DH)) ≃+*
        completedLocal (QHead DH) 𝔮) := by sorry

/-! ### L3 — reducedness of the head's completed local rings (the frontier) -/

variable {K w N} in
/-- **L3.a** (`W` invertible — the smooth chart): after inverting `W` the `Z`'s are
eliminated (`Z_i = W^{−2wᵢ}Y_i²`) and the head agrees with the full Tate algebra
`K⟨W, U_{≤N}⟩`; its completed local rings are reduced (classical Tate-algebra
regularity — its own sub-decomposition when reached). -/
theorem head_completedLocal_reduced_of_wa_notMem (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (𝔭 : Ideal (WPHead K w N)) (h𝔭 : 𝔭.IsPrime) (hW : WaHead K w N ∉ 𝔭) :
    haveI := h𝔭
    IsReduced (completedLocal (WPHead K w N) 𝔭) := by sorry

variable {K w N} in
/-- **L3.b** (`W ∈ 𝔭` — the singular point): all `Y_i ∈ 𝔭`, and the completed
quadratic tower must be analyzed through the formal relations directly
(characteristic-free; the deepest leaf of the campaign — see
[hrw-decomposition] L3.b for the planned Φ-style formal-domain embedding). -/
theorem head_completedLocal_reduced_of_wa_mem (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (𝔭 : Ideal (WPHead K w N)) (h𝔭 : 𝔭.IsPrime) (hW : WaHead K w N ∈ 𝔭) :
    haveI := h𝔭
    IsReduced (completedLocal (WPHead K w N) 𝔭) := by sorry

variable {K w N} in
/-- **L3**: every completed local ring of the head at a prime is reduced. -/
theorem head_completedLocal_reduced (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (𝔭 : Ideal (WPHead K w N)) (h𝔭 : 𝔭.IsPrime) :
    haveI := h𝔭
    IsReduced (completedLocal (WPHead K w N) 𝔭) := by
  by_cases hW : WaHead K w N ∈ 𝔭
  · exact head_completedLocal_reduced_of_wa_mem ϖ hK₀ 𝔭 h𝔭 hW
  · exact head_completedLocal_reduced_of_wa_notMem ϖ hK₀ 𝔭 h𝔭 hW

/-! ### L4 — assembly -/

variable {K w} in
/-- L4-prep: the graph model is noetherian (transport of the faithful
strongly-noetherian localization along `headLocEquiv`). -/
theorem isNoetherianRing_qHead (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) {N : ℕ}
    {DH : RationalLocData (WPHead K w N)} (hDH : DH.IsRational) :
    IsNoetherianRing (QHead DH) := by
  haveI := isStronglyNoetherian_WPHead (w := w) (N := N) ϖ hK₀
  haveI : IsNoetherianRing (WPHead K w N) :=
    IsStronglyNoetherian.isNoetherianRing (WPHead K w N)
  haveI : IsNoetherianRing (presheafValue DH) :=
    presheafValue_isNoetherianRing_faithful DH
  exact isNoetherianRing_of_surjective (presheafValue DH) (QHead DH)
    (headLocEquiv ϖ hK₀ DH hDH).toRingHom
    (headLocEquiv ϖ hK₀ DH hDH).surjective

variable {K} in
theorem headLocsReduced (ϖ : Uniformizer K)
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
  haveI hcp : (𝔮.comap (headToQ DH)).IsPrime :=
    𝔮.comap_isPrime (headToQ DH)
  obtain ⟨e⟩ := qHead_completedLocal_comparison ϖ hK₀ DH hDH 𝔮 h𝔮
  haveI : IsReduced
      (completedLocal (WPHead K w N) (𝔮.comap (headToQ DH))) :=
    head_completedLocal_reduced ϖ hK₀ _ hcp
  exact isReduced_of_injective e.symm.toRingHom e.symm.injective

end WeightedParity
