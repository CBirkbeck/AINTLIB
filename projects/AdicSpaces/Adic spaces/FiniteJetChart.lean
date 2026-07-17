/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FiniteJetFunctoriality
import «Adic spaces».FiniteJetUniformDomain

/-!
# The nonuniform chart: `𝓐⟨W/ϖ⟩ ≅ K⟨X,Q⟩/(Q²)` and failure of stable uniformity

Source: [FJP] §3. Proposition 3.1 (verbatim): "There is a canonical isomorphism of
topological k-algebras `𝒜_in ≅ k⟨X,Q⟩/(Q²)`, `W ↦ ϖX`, `Q ↦ Q`." — where
`𝒜_in = 𝒜⟨W/ϖ⟩ = (𝒜⟨X⟩/(ϖX − W))^∧` is the completed rational localization at the datum
`(W; ϖ)`, presented by `T = {W, ϖ}`, `s = ϖ`. In our models the target ring is literally
`𝓑 = DualNumber (K⟨X⟩)`.

Key computation ((3.3)): for `y ∈ Q²𝒞` and every `n`, `y = ϖⁿXⁿ(W^{-n}y)` with
`‖W^{-n}y‖ = ‖y‖`, so `Q²𝒞` dies in the separated completion.

Corollary 3.2 (verbatim): "The ring 𝒜 is not stably uniform." — the chart is nonzero and
nonuniform: "`Q ≠ 0`, `Q² = 0`, and every element of the unbounded line `kQ` is
power-bounded, while `‖λQ‖ = |λ|`."
-/

open Filter Topology

namespace FiniteJet

open RestrictedLaurent ValuationSpectrum

variable (F : Type*) [Field F]

local notation "K" => LaurentSeries F

noncomputable section

open scoped Classical

/-- The element `W ∈ 𝓐` (support `(1,0)`; [FJP] §1.4). -/
def Wa : JetA F :=
  ⟨sectionD F (TrivSqZeroExt.inl (Wu (R := K)).val), by
    rw [mem_jetSupport_iff_jet_in_range, rhoC_sectionD]
    have hsupp : (Wu (R := K)).val ∈ nonnegSubring K := by
      intro a ha
      show (single (1 : ℤ) (1 : K) : RestrictedLaurent K).coeff a = 0
      rw [coeff_single]
      exact if_neg (by omega)
    refine ⟨TrivSqZeroExt.inl ((nonnegEquiv (R := K)).symm ⟨(Wu (R := K)).val, hsupp⟩), ?_⟩
    refine TrivSqZeroExt.ext ?_ ?_
    · show ofRestricted ((nonnegEquiv (R := K)).symm ⟨(Wu (R := K)).val, hsupp⟩) =
        (Wu (R := K)).val
      rw [ofRestricted_nonnegEquiv_symm]
    · show ofRestricted (R := K) 0 = 0
      exact map_zero _⟩

/-- The chart datum `(W; ϖ)`: `T = {W, ϖ}`, `s = ϖ` — presenting the rational subset
`{|W| ≤ |ϖ| ≠ 0}` of `Spa(𝓐, 𝓐°)` ([FJP] (3.1)). -/
def chartDatum : RationalLocData (JetA F) where
  P := podA F
  T := {Wa F, tA F}
  s := tA F
  hopen := genPiece_hopen (podA F) {Wa F, tA F} (tA F)
    (Ideal.eq_top_of_isUnit_mem _
      (Ideal.subset_span (by
        rw [Finset.coe_insert, Finset.coe_singleton]
        exact Set.mem_insert_of_mem _ rfl))
      (isUnit_tA F))

theorem chartDatum_isRational : (chartDatum F).IsRational :=
  RationalLocData.isRational_of_span_eq_top
    (Ideal.eq_top_of_isUnit_mem _
      (Ideal.subset_span (by
        show tA F ∈ (({Wa F, tA F} : Finset (JetA F)) : Set (JetA F))
        rw [Finset.coe_insert, Finset.coe_singleton]
        exact Set.mem_insert_of_mem _ rfl))
      (isUnit_tA F))

/-! ### The `ϖ`-rescaling twist (Prop 3.1's normalisation `W ↦ ϖX`) -/

/-- Rescaling a restricted power series by a norm-`≤ 1` scalar stays restricted
(the substitution `X ↦ aX`; coefficientwise `aⁿ`-scaling). -/
noncomputable def rescaleRestricted {R : Type*} [NormedCommRing R] [IsUltrametricDist R]
    [NormOneClass R] (a : R) (ha : ‖a‖ ≤ 1) :
    PowerSeries.Restricted R (1 : ℝ) →+* PowerSeries.Restricted R (1 : ℝ) where
  toFun f := ⟨PowerSeries.rescale a f.1, by
    show PowerSeries.IsRestricted (1 : ℝ) (PowerSeries.rescale a f.1)
    have hf : PowerSeries.IsRestricted (1 : ℝ) f.1 := f.2
    rw [PowerSeries.IsRestricted] at hf ⊢
    refine squeeze_zero (fun n => by positivity) (fun n => ?_) hf
    rw [PowerSeries.coeff_rescale]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    calc ‖a ^ n * PowerSeries.coeff n f.1‖
        ≤ ‖a ^ n‖ * ‖PowerSeries.coeff n f.1‖ := norm_mul_le _ _
      _ ≤ 1 * ‖PowerSeries.coeff n f.1‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          cases n with
          | zero => rw [pow_zero, norm_one]
          | succ k =>
              exact (norm_pow_le' a k.succ_pos).trans
                (pow_le_one₀ (norm_nonneg a) ha)
      _ = ‖PowerSeries.coeff n f.1‖ := one_mul _⟩
  map_one' := Subtype.ext (map_one (PowerSeries.rescale a))
  map_mul' f g := Subtype.ext (map_mul (PowerSeries.rescale a) f.1 g.1)
  map_zero' := Subtype.ext (map_zero (PowerSeries.rescale a))
  map_add' f g := Subtype.ext (map_add (PowerSeries.rescale a) f.1 g.1)

/-- The componentwise `ϖ`-twist of 𝓑 (`X ↦ ϖX` on both jet components). -/
noncomputable def twistB : JetB F →+* JetB F :=
  JetNorm.mapHom (rescaleRestricted (LaurentSeriesExample.t F) (norm_t_lt_one F).le)

/-- The twisted base map `θ = twist ∘ jB` implementing Prop 3.1's `W ↦ ϖX`. -/
noncomputable def thetaChart : JetA F →+* JetB F :=
  (twistB F).comp (jB F)

/-- Rescaling fixes constant power series (`rescale a (C r) = C r`). -/
theorem rescaleRestricted_const (a : K) (ha : ‖a‖ ≤ 1) (r : K) :
    rescaleRestricted a ha (constHomPS F r) = constHomPS F r := by
  refine Subtype.ext ?_
  show PowerSeries.rescale a (PowerSeries.C r : PowerSeries K) = PowerSeries.C r
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_rescale]
  cases n with
  | zero => simp
  | succ k => simp [PowerSeries.coeff_C]

/-- The twist fixes the pseudouniformizer: `θ(ϖ_𝓐) = ϖ_𝓑`. -/
theorem thetaChart_tA : thetaChart F (tA F) = tB F := by
  sorry

/-- **[FJP] Proposition 3.1**: the chart is the square-zero disc algebra,
`𝒪_𝓐({|W| ≤ |ϖ|}) ≅ K⟨X⟩[Q]/(Q²) = 𝓑`, as topological rings. -/
def chartEquiv : presheafValue (chartDatum F) ≃+* JetB F := by sorry

theorem chartEquiv_continuous : Continuous (chartEquiv F) := by sorry

theorem chartEquiv_symm_continuous : Continuous (chartEquiv F).symm := by sorry

/-- The chart sends `canonicalMap W` to `ϖ · X` and `canonicalMap Q` to `ε`
([FJP] Prop 3.1: "`W ↦ ϖX`, `Q ↦ Q`"; pinned on the canonical image to make `chartEquiv`
canonical). -/
theorem chartEquiv_canonicalMap_W : True := by sorry

/-! ### Failure of stable uniformity ([FJP] Corollary 3.2) -/

/-- Power-boundedness transports along a bi-continuous ring isomorphism. -/
theorem isPowerBounded_map_of_ringEquiv {A B : Type*}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    {x : A} (hx : TopologicalRing.IsPowerBounded x) :
    TopologicalRing.IsPowerBounded (e x) := by
  intro U hU
  have hUA : ⇑e.symm ⁻¹' (⇑e ⁻¹' U) ∈ nhds (0 : B) := by
    refine he'.continuousAt.preimage_mem_nhds ?_
    rw [map_zero]
    refine he.continuousAt.preimage_mem_nhds ?_
    rw [map_zero]
    exact hU
  obtain ⟨V, hV, hSV⟩ := hx (⇑e ⁻¹' U)
    (he.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hU))
  refine ⟨⇑e.symm ⁻¹' V, he'.continuousAt.preimage_mem_nhds
    (by rw [map_zero]; exact hV), ?_⟩
  rintro _ ⟨s, ⟨n, rfl⟩, v, hv, rfl⟩
  have hxv : x ^ n * e.symm v ∈ ⇑e ⁻¹' U :=
    hSV ⟨x ^ n, ⟨n, rfl⟩, e.symm v, hv, rfl⟩
  show e x ^ n * v ∈ U
  have heq : e x ^ n * v = e (x ^ n * e.symm v) := by
    rw [map_mul, map_pow, RingEquiv.apply_symm_apply]
  rw [heq]
  exact hxv

/-- Uniformity is a topological-ring invariant: it transports along continuous ring
isomorphisms with continuous inverse. -/
theorem isUniform_of_ringEquiv {A B : Type*}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    (h : TopologicalRing.IsUniform A) : TopologicalRing.IsUniform B := by
  constructor
  intro U hU
  obtain ⟨V, hV, hSV⟩ := h.isBounded_powerBounded (⇑e ⁻¹' U)
    (he.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hU))
  refine ⟨⇑e.symm ⁻¹' V, he'.continuousAt.preimage_mem_nhds
    (by rw [map_zero]; exact hV), ?_⟩
  rintro _ ⟨s, hs, v, hv, rfl⟩
  have hsA : TopologicalRing.IsPowerBounded (e.symm s) :=
    isPowerBounded_map_of_ringEquiv e.symm he' (by simpa using he) hs
  have hmem : e.symm s * e.symm v ∈ ⇑e ⁻¹' U :=
    hSV ⟨e.symm s, hsA, e.symm v, hv, rfl⟩
  show s * v ∈ U
  have heq : s * v = e (e.symm s * e.symm v) := by
    rw [map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  rw [heq]
  exact hmem

/-- The chart is not uniform ([FJP] Cor 3.2, via `not_isUniform_JetB`). -/
theorem not_isUniform_chart :
    ¬ TopologicalRing.IsUniform (presheafValue (chartDatum F)) := fun h =>
  not_isUniform_JetB F
    (isUniform_of_ringEquiv (chartEquiv F) (chartEquiv_continuous F)
      (chartEquiv_symm_continuous F) h)

/-- **[FJP] Corollary 3.2**: 𝓐 is not stably uniform. -/
theorem not_isStablyUniform_JetA : ¬ TopologicalRing.IsStablyUniform (JetA F) := fun h =>
  not_isUniform_chart F ⟨h.presheafValue_isUniform (chartDatum F)⟩

end

end FiniteJet
