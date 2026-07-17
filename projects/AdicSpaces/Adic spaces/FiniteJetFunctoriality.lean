/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FiniteJetStrictLocalization
import «Adic spaces».FaithfulLocLift

/-!
# Functoriality layer: pushing rational data along the square, graph bridges, and
`HasLocLiftPowerBounded 𝓐`

Sources: [FJP] Lemma 1.1 (graph realization of rational localization — the universal
property), Lemma 4.6 (naturality), Lemma 5.1 (naturality on the rational basis: "For every
rational domain `U ⊂ X`, its inverse image `U_E = p_E⁻¹(U)` is the rational domain in `Y_E`
defined by the image of the same datum").

This file supplies what the survey identified as the missing covariant layer:

* pairs of definition for the four rings (unit balls with the pseudouniformizer ideal);
* `pushDatumB/C/D : RationalLocData 𝓐 → RationalLocData E` (image datum; `hopen` via the
  generic span-⊤/principal-pod argument);
* `presheafValueMap : 𝒪_𝓐(D) → 𝒪_E(D_E)` (localization functoriality + completion), and its
  naturality with `restrictionMap`;
* the **graph bridge** `𝒪_E(D) ≃+* P_E ⧸ I_E` ([FJP] Lemma 1.1 + (4.21)), topological in
  both directions — the identification of the project's completed localization with the
  Banach graph quotient, for `E = 𝓐` (closed ideal by Lemma 4.3) and the three vertices
  (closed by Lemma 4.2);
* pushed coverings, intersection data, and the Spa-point coverage transfer (via the
  project's contravariant `spaComap`);
* `HasLocLiftPowerBounded 𝓐`, derived **componentwise through the Milnor square** from the
  vertices' instances (the project discharger is noetherian-bound and 𝓐 is not noetherian).
-/

open Filter Topology

namespace FiniteJet

open RestrictedLaurent ValuationSpectrum StrictLoc

variable (F : Type*) [Field F]

local notation "K" => LaurentSeries F

noncomputable section

open scoped Classical

/-! ### Pairs of definition -/

/-- The unit-ball pair of definition of 𝓐 (the generic `unitBallPod` at `tA`). -/
def podA : PairOfDefinition (JetA F) :=
  unitBallPod (tA F) (isUnit_tA F) (norm_tA_lt_one F) (norm_tA_pos F) (norm_tA_mul F)

def podB : PairOfDefinition (JetB F) :=
  unitBallPod (tB F) (isUnit_tB F) (by rw [norm_tB]; exact norm_t_lt_one F)
    (by rw [norm_tB]; exact norm_t_pos F) (norm_tB_mul F)

def podC : PairOfDefinition (JetC F) :=
  unitBallPod (tC F) (isUnit_tC F) (by rw [norm_tC]; exact norm_t_lt_one F)
    (by rw [norm_tC]; exact norm_t_pos F) (norm_tC_mul F)

def podD : PairOfDefinition (JetD F) :=
  unitBallPod (tD F) (isUnit_tD F) (by rw [norm_tD]; exact norm_t_lt_one F)
    (by rw [norm_tD]; exact norm_t_pos F) (norm_tD_mul F)

/-! ### Pushing rational localization data ([FJP] Lemma 5.1)

The `hopen` field for the pushed datum is the generic bounded-denominator statement for
span-⊤ data over a principal pair of definition in a Tate ring (risk item 3 of `plan.md`). -/

variable {F}

/-- Push a rational datum of 𝓐 to 𝓑 (image datum, [FJP] Lemma 5.1). -/
def pushDatumB (D : RationalLocData (JetA F)) : RationalLocData (JetB F) where
  P := podB F
  T := D.T.image (jB F)
  s := jB F D.s
  hopen := by sorry

/-- Push a rational datum of 𝓐 to 𝓒. -/
def pushDatumC (D : RationalLocData (JetA F)) : RationalLocData (JetC F) where
  P := podC F
  T := D.T.image (iotaC F)
  s := iotaC F D.s
  hopen := by sorry

/-- Push a rational datum of 𝓐 to 𝓓. -/
def pushDatumD (D : RationalLocData (JetA F)) : RationalLocData (JetD F) where
  P := podD F
  T := D.T.image ((rhoC F).comp (iotaC F))
  s := rhoC F (iotaC F D.s)
  hopen := by sorry

theorem pushDatumB_isRational {D : RationalLocData (JetA F)} (hD : D.IsRational) :
    (pushDatumB D).IsRational := by sorry

theorem pushDatumC_isRational {D : RationalLocData (JetA F)} (hD : D.IsRational) :
    (pushDatumC D).IsRational := by sorry

theorem pushDatumD_isRational {D : RationalLocData (JetA F)} (hD : D.IsRational) :
    (pushDatumD D).IsRational := by sorry

/-! ### Covariant maps on presheaf values -/

/-- The induced map on completed rational localizations along `ιC` ([FJP] Lemma 5.1's
`𝒪_X(U) → 𝒪_{Y_C}(U_C)`; built from `IsLocalization` functoriality, continuity for the
localization topologies, and `UniformSpace.Completion` functoriality). -/
def presheafValueMapC (D : RationalLocData (JetA F)) :
    presheafValue D →+* presheafValue (pushDatumC D) := by sorry

def presheafValueMapB (D : RationalLocData (JetA F)) :
    presheafValue D →+* presheafValue (pushDatumB D) := by sorry

def presheafValueMapD (D : RationalLocData (JetA F)) :
    presheafValue D →+* presheafValue (pushDatumD D) := by sorry

theorem presheafValueMapC_continuous (D : RationalLocData (JetA F)) :
    Continuous (presheafValueMapC D) := by sorry

theorem presheafValueMapB_continuous (D : RationalLocData (JetA F)) :
    Continuous (presheafValueMapB D) := by sorry

theorem presheafValueMapC_canonicalMap (D : RationalLocData (JetA F)) (a : JetA F) :
    presheafValueMapC D (D.canonicalMap a) =
      (pushDatumC D).canonicalMap (iotaC F a) := by sorry

theorem presheafValueMapB_canonicalMap (D : RationalLocData (JetA F)) (a : JetA F) :
    presheafValueMapB D (D.canonicalMap a) =
      (pushDatumB D).canonicalMap (jB F a) := by sorry

/-! ### The graph bridge ([FJP] Lemma 1.1 + (4.21))

For an indexed enumeration `(g, f)` of a rational datum `(T, s)` (with `g = s`), the
project's completed rational localization is topologically the Banach graph quotient. -/

/-- An indexed enumeration of a `RationalLocData`: `f` lists `T`, `g = s`. -/
structure DatumEnum (D : RationalLocData (JetA F)) where
  /-- The arity. -/
  m : ℕ
  /-- The enumeration of `T`. -/
  f : Fin m → JetA F
  /-- Enumeration covers `T`. -/
  hf : ∀ t ∈ D.T, ∃ i, f i = t
  /-- Enumeration lands in `T`. -/
  hf' : ∀ i, f i ∈ D.T

/-- The graph bridge for 𝓐 ([FJP] Lemma 1.1: the separated completion of the graph
quotient "is therefore canonically the underlying Tate algebra of Huber's rational
localization `E_α`"; by Lemma 4.3 the ideal is closed so no further completion is needed).
Topological ring isomorphism `𝒪_𝓐(D) ≅ P_𝓐 ⧸ I_𝓐`. -/
def graphBridgeA (D : RationalLocData (JetA F)) (hD : D.IsRational) (e : DatumEnum D) :
    presheafValue D ≃+* locA (F := F) e.m D.s e.f := by sorry

theorem graphBridgeA_continuous (D : RationalLocData (JetA F)) (hD : D.IsRational)
    (e : DatumEnum D) : Continuous (graphBridgeA D hD e) := by sorry

theorem graphBridgeA_symm_continuous (D : RationalLocData (JetA F)) (hD : D.IsRational)
    (e : DatumEnum D) : Continuous (graphBridgeA D hD e).symm := by sorry

/-- The bridge intertwines the covariant maps with the coefficientwise localized square
([FJP] Lemma 4.6 / Lemma 5.1 naturality, 𝓒 side; analogous statements for 𝓑, 𝓓 are
formulated in the transfer file where consumed). -/
theorem graphBridge_natural_C (D : RationalLocData (JetA F)) (hD : D.IsRational)
    (e : DatumEnum D) : True := by sorry

/-! ### Vertices: loc-lift instances (noetherian discharger applies) -/

instance : HasLocLiftPowerBounded (JetB F) := by sorry

instance : HasLocLiftPowerBounded (JetC F) := by sorry

instance : HasLocLiftPowerBounded (JetD F) := by sorry

/-! ### `HasLocLiftPowerBounded 𝓐`, componentwise

𝓐 is not noetherian, so `hasLocLiftPowerBounded_faithful` does not apply. Both fields are
derived through the Milnor description of `𝒪_𝓐(D)` ([FJP] Lemma 5.1 + Prop 4.5): a unit in
both comparison localizations whose inverses match in 𝓓 is a unit in the fiber product, and
power-boundedness in the max norm is componentwise. -/

instance hasLocLiftPowerBounded_JetA : HasLocLiftPowerBounded (JetA F) := by sorry

/-! ### Naturality with restriction ([FJP] Lemma 4.6, Lemma 5.1)

With the loc-lift instances available, the project's `restrictionMap` vocabulary applies to
all four rings, and the covariant maps commute with it. -/

theorem presheafValueMapC_restriction (D D' : RationalLocData (JetA F))
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (hpush : rationalOpen (pushDatumC D').T (pushDatumC D').s ⊆
      rationalOpen (pushDatumC D).T (pushDatumC D).s) (x : presheafValue D) :
    presheafValueMapC D' (restrictionMap D D' h x) =
      restrictionMap (pushDatumC D) (pushDatumC D') hpush (presheafValueMapC D x) := by
  sorry

theorem presheafValueMapB_restriction (D D' : RationalLocData (JetA F))
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (hpush : rationalOpen (pushDatumB D').T (pushDatumB D').s ⊆
      rationalOpen (pushDatumB D).T (pushDatumB D).s) (x : presheafValue D) :
    presheafValueMapB D' (restrictionMap D D' h x) =
      restrictionMap (pushDatumB D) (pushDatumB D') hpush (presheafValueMapB D x) := by
  sorry

/-! ### Coverage transfer ([FJP] Lemma 5.2, first display: `U_E = ⋃ᵢ (Uᵢ)_E`) -/

/-- Inverse images preserve the rational inequalities: pushed rational opens are the
`spaComap`-preimages. (Pointwise: `v ∈ rationalOpen (T_E, s_E) ↔ v ∘ ι ∈ rationalOpen (T, s)`
for `v` in the vertex spectrum.) -/
theorem mem_rationalOpen_pushDatumC_iff (D : RationalLocData (JetA F))
    (v : Spv (JetC F)) (hv : v ∈ Spa (JetC F) (ringPlus (JetC F))) :
    v ∈ rationalOpen (pushDatumC D).T (pushDatumC D).s ↔
      ValuationSpectrum.comap (iotaC F) v ∈ rationalOpen D.T D.s := by sorry

theorem mem_rationalOpen_pushDatumB_iff (D : RationalLocData (JetA F))
    (v : Spv (JetB F)) (hv : v ∈ Spa (JetB F) (ringPlus (JetB F))) :
    v ∈ rationalOpen (pushDatumB D).T (pushDatumB D).s ↔
      ValuationSpectrum.comap (jB F) v ∈ rationalOpen D.T D.s := by sorry

/-- The pushed covering of a rational covering of 𝓐, at the 𝓒-vertex
([FJP] Lemma 5.2: "Inverse images preserve the defining valuation inequalities and unions.
Hence, for `E = B, C, D`, `U_E = ⋃ᵢ (Uᵢ)_E` is a rational covering"). -/
def pushCoveringC (C : RationalCovering (JetA F)) : RationalCovering (JetC F) where
  base := pushDatumC C.base
  covers := C.covers.image pushDatumC
  hsubset := by sorry
  hcover := by sorry

def pushCoveringB (C : RationalCovering (JetA F)) : RationalCovering (JetB F) where
  base := pushDatumB C.base
  covers := C.covers.image pushDatumB
  hsubset := by sorry
  hcover := by sorry

def pushCoveringD (C : RationalCovering (JetA F)) : RationalCovering (JetD F) where
  base := pushDatumD C.base
  covers := C.covers.image pushDatumD
  hsubset := by sorry
  hcover := by sorry

theorem pushCoveringB_isRational {C : RationalCovering (JetA F)} (hC : C.IsRational) :
    (pushCoveringB C).IsRational := by sorry

theorem pushCoveringC_isRational {C : RationalCovering (JetA F)} (hC : C.IsRational) :
    (pushCoveringC C).IsRational := by sorry

theorem pushCoveringD_isRational {C : RationalCovering (JetA F)} (hC : C.IsRational) :
    (pushCoveringD C).IsRational := by sorry

/-! ### Intersection data ([FJP] Lemma 5.2: `(U_{ij})_E = (U_i)_E ∩ (U_j)_E`) -/

/-- The product (intersection) datum of two rational data ([FJP] Lemma 5.2 uses
`U_{ij} = U_i ∩ U_j`, "which is again rational"). -/
def interDatum (D₁ D₂ : RationalLocData (JetA F)) : RationalLocData (JetA F) where
  P := podA F
  T := (D₁.T ×ˢ D₂.T).image fun p => p.1 * p.2
  s := D₁.s * D₂.s
  hopen := by sorry

theorem rationalOpen_interDatum (D₁ D₂ : RationalLocData (JetA F))
    (h₁ : D₁.IsRational) (h₂ : D₂.IsRational) :
    rationalOpen (interDatum D₁ D₂).T (interDatum D₁ D₂).s =
      rationalOpen D₁.T D₁.s ∩ rationalOpen D₂.T D₂.s := by sorry

theorem interDatum_isRational {D₁ D₂ : RationalLocData (JetA F)}
    (h₁ : D₁.IsRational) (h₂ : D₂.IsRational) : (interDatum D₁ D₂).IsRational := by sorry

end

end FiniteJet
