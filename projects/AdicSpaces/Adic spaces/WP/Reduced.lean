/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WP.CoeffLocalization
import «Adic spaces».Vendored.XiaMvPowerSeriesEquiv
import «Adic spaces».AuditCleanWrappers

/-!
# Rational stable reducedness ([WP] §6.6)

Three layers:

1. **`lem:formal-series-reduced`**: `MvPowerSeries J P` over a reduced `P` is reduced,
   for an ARBITRARY index `J` — via the injection of a reduced ring into the product
   of its prime quotients, the coefficientwise product decomposition of
   `MvPowerSeries` over a product ring, and mathlib's
   `NoZeroDivisors (MvPowerSeries σ R)` (arbitrary `σ`).  Mathlib-grade statements.

2. **The descent mechanism** ([WP] thm:parity-rationally-reduced, proof): every
   rational localization `E` of `𝒜` is a `TailC0` over a head localization `P`
   (`nonempty_headModelData`); the twist element (image of `W`) is REGULAR on `P`
   because `W` is a nonzerodivisor of the head domain and the head localization is
   FLAT (Wedhorn 8.30, delivered as `prop_8_30_flat_clean_proof`); therefore the
   embedding `Φ` of `WP/Tail.lean` lands `E` in the reduced ring `ℱ_J(P)`.

3. **The head-reducedness wall** (BGR 7.3.2/10 for the heads): quarantined as the
   predicate `HeadLocsReduced`; endpoint (3) is delivered conditionally on it, and the
   predicate's own discharge is a separate sub-campaign (see
   `.mathlib-quality/wp-reduced/decomposition.md` § HRW).

"Finite iterated rational localization" is formalized by the chain recursion
`ChainReduced` (the project has no iterated-localization composition theorem; the
induction step re-applies `nonempty_headModelData` through the model transport).
-/

@[expose] public section

namespace WeightedParity

open ValuationSpectrum FiniteJetOver

/-! ### `lem:formal-series-reduced` (mathlib-grade) -/

/-- `MvPowerSeries` over a product ring is the product of the `MvPowerSeries`
(coefficientwise). -/
noncomputable def mvPowerSeriesPi (J : Type*) {ι : Type*} (R : ι → Type*)
    [∀ i, CommRing (R i)] :
    MvPowerSeries J (∀ i, R i) ≃+* ∀ i, MvPowerSeries J (R i) where
  toFun f i := MvPowerSeries.map (Pi.evalRingHom R i) f
  invFun g t i := g i t
  left_inv f := rfl
  right_inv g := rfl
  map_add' f g := by
    funext i
    exact map_add (MvPowerSeries.map (Pi.evalRingHom R i)) f g
  map_mul' f g := by
    funext i
    exact map_mul (MvPowerSeries.map (Pi.evalRingHom R i)) f g

/-- A reduced commutative ring embeds into the product of its prime quotients
(kernel = nilradical = 0; `nilradical_eq_sInf`). -/
theorem exists_injective_pi_quotient (P : Type*) [CommRing P] [IsReduced P] :
    ∃ f : P →+* ∀ I : {I : Ideal P // I.IsPrime}, P ⧸ I.1,
      Function.Injective f := by
  classical
  refine ⟨RingHom.pi fun I => Ideal.Quotient.mk I.1, ?_⟩
  rw [injective_iff_map_eq_zero]
  intro a ha
  have hmem : ∀ I : {I : Ideal P // I.IsPrime}, a ∈ I.1 := fun I =>
    Ideal.Quotient.eq_zero_iff_mem.mp (congrFun ha I)
  have hnil : a ∈ nilradical P := by
    rw [nilradical_eq_sInf, Ideal.mem_sInf]
    intro I hI
    exact hmem ⟨I, hI⟩
  rwa [nilradical_eq_zero, Ideal.zero_eq_bot, Ideal.mem_bot] at hnil

/-- **`lem:formal-series-reduced`** ([WP] lines 1241–1261): formal power series in
arbitrarily many variables over a reduced commutative ring form a reduced ring. -/
theorem isReduced_mvPowerSeries (J : Type*) (P : Type*) [CommRing P] [IsReduced P] :
    IsReduced (MvPowerSeries J P) := by
  classical
  obtain ⟨f, hf⟩ := exists_injective_pi_quotient P
  haveI hred : ∀ I : {I : Ideal P // I.IsPrime},
      IsReduced (MvPowerSeries J (P ⧸ I.1)) := fun I => by
    haveI := I.2
    infer_instance
  have hmap : Function.Injective
      (MvPowerSeries.map (σ := J) f :
        MvPowerSeries J P → MvPowerSeries J (∀ I : {I : Ideal P // I.IsPrime}, P ⧸ I.1)) :=
    MvPowerSeries.map_injective hf
  have hcomp : Function.Injective
      (((mvPowerSeriesPi J
          (fun I : {I : Ideal P // I.IsPrime} => P ⧸ I.1)) :
        MvPowerSeries J (∀ I : {I : Ideal P // I.IsPrime}, P ⧸ I.1) ≃+*
          ∀ I : {I : Ideal P // I.IsPrime}, MvPowerSeries J (P ⧸ I.1)).toRingHom.comp
        (MvPowerSeries.map f)) := by
    rw [RingHom.coe_comp]
    exact (mvPowerSeriesPi J _).injective.comp hmap
  exact isReduced_of_injective _ hcomp

/-! ### `W`-regularity of head localizations ([WP] thm:parity-rationally-reduced:
"Affinoid rational localization is algebraically flat … multiplication by `W` is
injective on `P`") -/

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (w : ℕ → ℕ)

variable {K w} in
/-- The twist element of the head model is regular: `W` is a nonzerodivisor of the
head (a domain), head localization is flat (Wedhorn 8.30,
`prop_8_30_flat_clean_proof`), and flatness preserves injectivity of multiplication
(`Module.Flat.rTensor_preserves_injective_linearMap`). -/
theorem rhoQ_regular {N : ℕ} (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    ∀ x : QHead DH, (rhoQ DH).val * x = 0 → x = 0 := by sorry

/-! ### The quarantined head-reducedness input (BGR 7.3.2/10) -/

/-- **The head-reducedness predicate** (the classical input BGR 7.3.2/10 at the
heads): every rational localization of every head is reduced.  [WP]
thm:parity-rationally-reduced cites: "A rational localization of a reduced affinoid
algebra is reduced [BGR, Corollary 7.3.2/10]; see also [KedlayaAWS, Remark 1.2.16].
Thus `P` is reduced."  Its discharge is a separate sub-campaign. -/
def HeadLocsReduced : Prop :=
  ∀ (N : ℕ) (DH : RationalLocData (WPHead K w N)), DH.IsRational →
    IsReduced (presheafValue DH)

/-! ### The conditional reducedness endpoints -/

variable {K w} in
/-- **Single-step reducedness** ([WP] thm:parity-rationally-reduced, single
localization): every rational localization of `𝒜` is reduced, conditionally on the
head input.  Route: finite-head model + `Φ`-embedding + `rhoQ_regular` +
`isReduced_mvPowerSeries`. -/
theorem isReduced_presheafValue_WPA (hred : HeadLocsReduced K w)
    (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (D : RationalLocData (WPA K w)) (hD : D.IsRational) :
    IsReduced (presheafValue D) := by sorry

/-- Finite chains of rational localizations, and reducedness all the way down
([WP] def:rationally-stably-reduced: "every finite iterated rational localization is
reduced").  `ChainReduced A n` says: `A` itself and every iterated rational
localization of depth `≤ n` is reduced (cumulative successor form per the 2026-07-28
ChatGPT-5.6 plan review, so each level records all shallower depths too). -/
def ChainReduced : (A : Type _) → [inst : CommRing A] → [inst : TopologicalSpace A] →
    [inst : IsTopologicalRing A] → ℕ → Prop
  | A, _, _, _, 0 => IsReduced A
  | A, _, _, _, (n + 1) => IsReduced A ∧ ∀ D : RationalLocData A, D.IsRational →
      ChainReduced (presheafValue D) n

variable {K w} in
/-- **Rational stable reducedness of `𝒜`, conditionally on the head input**
([WP] thm:rationally-reduced-example (3): "The ring `𝒜` is rationally stably
reduced").  The induction re-applies the finite-head machinery at every stage: each
localization is again a `TailC0` over a (further localized) head. -/
theorem chainReduced_WPA (hred : HeadLocsReduced K w) (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) (n : ℕ) :
    ChainReduced (WPA K w) n := by sorry

end WeightedParity
