/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FiniteJetFunctoriality

/-!
# Sheafiness of 𝓐 by Milnor transfer ([FJP] Lemma 5.2 and Theorem 5.3)

Source: [FJP] Lemma 5.2 (topological sheaf transfer for a strictly localizing Milnor
square, verbatim conclusion): "If the Huber pairs `(B,B⁺), (C,C⁺), (D,D⁺)` are sheafy as
complete topological rings, then `(R,R⁺)` is sheafy as a complete topological ring." and
Theorem 5.3: "The structure presheaf on `X = Spa(𝒜, 𝒜°)` is a sheaf of complete topological
rings; equivalently, `(𝒜, 𝒜°)` is sheafy."

Retargeted at the project's `ValuationSpectrum.IsSheafy` (rational coverings; the paper's
arbitrary-opens upgrade (5.9) is not part of the project's class and is not formalised).

Gluing chain (paper's proof, p. 19–20): push the matching family to the vertices; matching
persists on pairwise intersections (`interDatum` + naturality); vertices' `IsSheafy.gluing`
produce `b ∈ B_U`, `c ∈ C_U`; their 𝓓-images agree after restriction to every piece, hence
agree by 𝓓-separatedness; exactness of the localized Milnor row ([FJP] Prop 4.5 via the
graph bridges) produces the unique `x ∈ 𝒪_𝓐(U)`; its restrictions are recovered by
injectivity of the localized rows on the pieces.

Embedding: the range of `productRestrictionSub` is the closed `sectionEqualizer` (project
generic), and the σ-compact-free Tate open mapping route
(`productRestrictionSub_isInducing_via_equalizer` pattern, [FJP] Thm 5.3's "the Banach open
mapping theorem makes the continuous bijection onto that image a homeomorphism") applies once
gluing and injectivity are in hand.
-/

open Filter Topology

namespace FiniteJet

open RestrictedLaurent ValuationSpectrum

variable (F : Type*) [Field F]

/-! ### Ingredients of the gluing transfer -/

variable {F}

/-- Injectivity (separation) for 𝓐: the localized Milnor rows are jointly injective on
every rational piece ([FJP] Lemma 5.2: "It equals `J r_R`. Since `J` is itself an
embedding …"; algebraic part). -/
theorem productRestrictionSub_injective_JetA (C : RationalCovering (JetA F))
    (hC : C.IsRational) :
    Function.Injective (productRestrictionSub (JetA F) C) := by sorry

/-- The gluing transfer ([FJP] Lemma 5.2, gluing half). -/
theorem gluing_JetA (C : RationalCovering (JetA F)) (hC : C.IsRational)
    (f : ∀ D : ↥C.covers, presheafValue D.1)
    (hcompat : ∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData (JetA F))
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
      restrictionMap D₁.1 D₃ h₃₁ (f D₁) = restrictionMap D₂.1 D₃ h₃₂ (f D₂)) :
    ∃ x : presheafValue C.base, ∀ D : ↥C.covers,
      restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D := by sorry

/-- The embedding transfer ([FJP] Lemma 5.2, topological half; Theorem 5.3's OMT step). -/
theorem productRestrictionSub_isEmbedding_JetA (C : RationalCovering (JetA F))
    (hC : C.IsRational) :
    Topology.IsEmbedding (productRestrictionSub (JetA F) C) := by sorry

variable (F)

/-- **The finite-jet pinching algebra is sheafy** ([FJP] Theorem 5.3). This is the
priority theorem of the campaign. -/
theorem isSheafy_JetA : ValuationSpectrum.IsSheafy (JetA F) where
  embedding := fun C hC => productRestrictionSub_isEmbedding_JetA C hC
  gluing := fun C hC f hcompat => gluing_JetA C hC f hcompat

end FiniteJet
