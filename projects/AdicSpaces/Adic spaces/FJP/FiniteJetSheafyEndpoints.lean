/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FJP.FiniteJetMain
import «Adic spaces».StructurePresheafBundled
import «Adic spaces».StandardDescent

/-!
# FJP: the literature-facing sheafiness endpoints (WO5)

Corollaries of the fixed-pair headline `finiteJet_isSheafy` ([FJP] Theorem 1.3)
through the generic bridges — **no FJP-specific re-proof of anything**:

* `finiteJet_isSheafyFor` — pair-level sheafiness in the public vocabulary: the
  genuine all-open projective-limit structure presheaf of `Spa (𝓐, 𝓐⁺)` is a sheaf
  of topological rings (`IsSheafyFor`, via the C5 equivalence).
* `finiteJet_isSheafOfTopologicalRings` — **Wedhorn Remark 8.20's own formulation**:
  for every topological commutative ring `T`, `V ↦ Hom_cont(T, 𝒪_X(V))` is a sheaf
  of sets.
* `finiteJet_structurePresheaf_isSheaf` / `finiteJet_structureSheaf` — the bundled
  public structure presheaf satisfies mathlib's categorical sheaf condition; the
  sheaf object. The topology is the projective-limit topology — nothing discrete.
* `finiteJet_standardSheafCondition` — the `A⁺`-free standard sheaf condition
  (Kedlaya Remark 1.6.9's `A⁺`-independent middle term) holds for `𝓐`
  unconditionally, through the single-pair transfer
  `standardSheafCondition_of_isSheafyFor`. Note `𝓐` is **not** noetherian
  ([FJP] Thm 1.3), so this is *not* obtainable from the strongly noetherian route —
  it is the genuine transfer from the proved pair.
* `finiteJet_isSheafyComplete_of_hasStandardRefinements` — sheafiness at **every**
  valid ring of integral elements, conditional on exactly the descent input
  (Kedlaya Lemma 1.6.8's conclusion, `HasStandardRefinements`; see
  `StandardDescent.lean` for the precise blocked dependencies). Stated conditionally
  and honestly: `𝓐` is non-noetherian, so no unconditional route to all pairs exists
  in the project yet.

All original FJP headline endpoints are untouched (regression-protected).
-/

noncomputable section

namespace FiniteJet

open ValuationSpectrum

universe u

variable (F : Type u) [Field F]

/-- The canonical valid pair of the pinching algebra: its maximal plus ring,
bundled. -/
def finiteJetPlus : RingOfIntegralElements (JetA F) :=
  ⟨((JetA F)⁺ : Subring (JetA F)), inferInstance⟩

/-- **Pair-level sheafiness of the pinching algebra, public form**: the genuine
all-open projective-limit structure presheaf of `Spa (𝓐, 𝓐⁺)` is a sheaf of
topological rings. Corollary of `finiteJet_isSheafy` through the C5 equivalence. -/
theorem finiteJet_isSheafyFor : IsSheafyFor (JetA F) (finiteJetPlus F) := by
  classical
  letI := (finiteJetPlus F).toPlusSubring
  haveI : IsRingOfIntegralElements ((JetA F)⁺ : Subring (JetA F)) :=
    (finiteJetPlus F).2
  haveI : HasLocLiftPowerBounded (JetA F) := hasLocLiftPowerBounded_faithful
  haveI : IsSheafy (JetA F) := finiteJet_isSheafy F
  show IsLimitSheaf (JetA F)
  exact isLimitSheaf_of_isSheafy

/-- **The pinching algebra's structure presheaf is a sheaf of topological rings in
Wedhorn's own sense** (Remark 8.20): for every topological commutative ring `T`,
`V ↦ Hom_cont(T, 𝒪_X(V))` is a sheaf of sets on `Spa (𝓐, 𝓐⁺)`. -/
theorem finiteJet_isSheafOfTopologicalRings :
    IsSheafOfTopologicalRings (JetA F) := by
  classical
  refine (isSheafOfTopologicalRings_iff_isLimitSheaf).mpr ?_
  haveI : IsSheafy (JetA F) := finiteJet_isSheafy F
  exact isLimitSheaf_of_isSheafy

/-- **The bundled public structure presheaf of the pinching algebra satisfies the
categorical sheaf condition** ([Stacks 00VR] `Hom`-by-`Hom` form). -/
theorem finiteJet_structurePresheaf_isSheaf :
    (ValuationSpectrum.structurePresheaf (JetA F)).IsSheaf := by
  classical
  refine structurePresheaf_isSheaf (JetA F) ?_
  haveI : IsSheafy (JetA F) := finiteJet_isSheafy F
  exact isLimitSheaf_of_isSheafy

/-- The structure sheaf of the pinching algebra, as a sheaf object valued in the
(coherent) category of complete separated topological commutative rings. -/
def finiteJet_structureSheaf :
    TopCat.Sheaf CompleteTopCommRingCat.{u} (SpaTop (JetA F)) :=
  ⟨ValuationSpectrum.structurePresheaf (JetA F), finiteJet_structurePresheaf_isSheaf F⟩

/-- **The `A⁺`-free standard sheaf condition holds for the pinching algebra,
unconditionally** — through the genuine single-pair transfer
(`standardSheafCondition_of_isSheafyFor`, Kedlaya Remark 1.6.9's mechanism). Since
`𝓐` is not noetherian, this is *not* an instance of the strongly noetherian
theorems: it is the transfer from the proved pair `(𝓐, 𝓐⁺)`. -/
theorem finiteJet_standardSheafCondition : StandardSheafCondition (JetA F) :=
  standardSheafCondition_of_isSheafyFor (finiteJetPlus F) (finiteJet_isSheafyFor F)

/-- **Sheafiness of the pinching algebra at every valid ring of integral elements**,
conditional on exactly the descent input (Kedlaya Lemma 1.6.8's conclusion) at each
pair — the honest form: `𝓐` is non-noetherian, so the unconditional all-pairs
statement awaits the descent branch (see `HasStandardRefinements`). -/
theorem finiteJet_isSheafyComplete_of_hasStandardRefinements
    (hall : ∀ Bplus : RingOfIntegralElements (JetA F),
      Bplus.HasStandardRefinements (JetA F)) :
    IsSheafyComplete (JetA F) :=
  (isSheafyFor_iff_isSheafyComplete (finiteJetPlus F) hall).mp
    (finiteJet_isSheafyFor F)

end FiniteJet
