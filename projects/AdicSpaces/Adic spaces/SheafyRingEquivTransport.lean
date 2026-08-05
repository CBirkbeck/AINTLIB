/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».RingEquivPresheafTransport
import «Adic spaces».SheafyRing

/-!
# Public transport of sheafiness along a bicontinuous ring equivalence (T7)

The literature-facing endpoints of the ring-equivalence transport: for an
isomorphism of complete Tate topological rings `e : A ≃+* B` (a ring equivalence
continuous in both directions),

* `isSheafyFor_mapRingEquiv` — pair-level sheafiness pushes forward:
  `IsSheafyFor A Aplus → IsSheafyFor B (Aplus.map e)`;
* `isSheafyFor_equiv` — the two-sided form, an `↔` (via the plus-ring
  roundtrip `RingOfIntegralElements.map_symm_map`);
* `isSheafyComplete_congr` — ring-level sheafiness (every valid ring of
  integral elements) is invariant: `IsSheafyComplete A ↔ IsSheafyComplete B`.

Distinguish `isSheafyFor_equiv` from `isSheafyFor_congr`
(`RelativeStandardRefinement.lean`): the latter changes only the plus ring on
one fixed underlying ring; this file changes the ring itself.

The signatures carry only the two complete-Tate topological stacks and the
bicontinuous ring equivalence — no `PlusSubring`, no ambient
`IsRingOfIntegralElements` instance, no `HasLocLiftPowerBounded`, no
`CompatiblePlusSubring`, no `DecidableEq`, no noetherian hypotheses. The proofs
route through the internal criterion (`isSheafy_iff_isLimitSheaf` and the T6
transport `isSheafy_mapRingEquiv`); every legacy instance is installed `letI`/
`haveI`-locally inside the proof bodies.

This module sits *above* `SheafyRing.lean` — the low-level transport file
(`RingEquivPresheafTransport.lean`) deliberately does not import the sheafy-pair
layer, avoiding a foundational import cycle.
-/

noncomputable section

namespace ValuationSpectrum

universe u v

variable {A : Type u} {B : Type v}
  [CommRing A] [TopologicalSpace A] [IsTateRing A] [T2Space A]
  [NonarchimedeanRing A]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
  [CommRing B] [TopologicalSpace B] [IsTateRing B] [T2Space B]
  [NonarchimedeanRing B]
  [letI : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B; CompleteSpace B]

/-- **Pair-level sheafiness pushes forward along a bicontinuous ring
equivalence** (T7): if the genuine all-open structure presheaf of
`Spa (A, Aplus)` is a sheaf of topological rings, so is that of
`Spa (B, Aplus.map e)`. -/
theorem isSheafyFor_mapRingEquiv (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) (Aplus : RingOfIntegralElements A)
    (h : IsSheafyFor A Aplus) :
    IsSheafyFor B (RingOfIntegralElements.map e he he' Aplus) := by
  classical
  -- 1–2: install the source pair and the mapped target pair
  letI := Aplus.toPlusSubring
  have : IsRingOfIntegralElements (A⁺ : Subring A) := Aplus.2
  letI := (Aplus.map e he he').toPlusSubring
  have : IsRingOfIntegralElements (B⁺ : Subring B) := (Aplus.map e he he').2
  -- 3: both faithful restriction-map packages, locally
  have : HasLocLiftPowerBounded A := hasLocLiftPowerBounded_faithful
  have : HasLocLiftPowerBounded B := hasLocLiftPowerBounded_faithful
  -- 4: convert `IsLimitSheaf` to the internal criterion
  have : IsSheafy A := isSheafy_of_isLimitSheaf h
  -- 5: the T6 transport (the mapped plus ring is definitionally the image)
  have : IsSheafy B := isSheafy_mapRingEquiv e he he' rfl
  -- 6: convert back
  exact isLimitSheaf_of_isSheafy

/-- **Pair-level sheafiness transports as an equivalence** (T7): sheafiness of
`(A, Aplus)` is equivalent to sheafiness of `(B, Aplus.map e)`. -/
theorem isSheafyFor_equiv (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    (Aplus : RingOfIntegralElements A) :
    IsSheafyFor A Aplus ↔ IsSheafyFor B (RingOfIntegralElements.map e he he' Aplus) :=
  -- both directions are the one-way transport; the backward direction is normalized
  -- with the plus-ring roundtrip `RingOfIntegralElements.map_symm_map`
  ⟨isSheafyFor_mapRingEquiv e he he' Aplus, fun h ↦
    RingOfIntegralElements.map_symm_map e he he' Aplus ▸
      isSheafyFor_mapRingEquiv e.symm he' he _ h⟩

/-- **Ring-level sheafiness is invariant under bicontinuous ring equivalences**
(T7): a complete Tate ring is sheafy for every valid ring of integral elements
iff its isomorphic image is. -/
theorem isSheafyComplete_congr (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm) :
    IsSheafyComplete A ↔ IsSheafyComplete B :=
  -- each direction is the `mpr` of the pair-level equivalence (along `e.symm` resp. `e`)
  -- at the plus ring pulled back to the sheafy side
  ⟨fun h Bplus ↦ (isSheafyFor_equiv e.symm he' he Bplus).mpr (h _),
    fun h Aplus ↦ (isSheafyFor_equiv e he he' Aplus).mpr (h _)⟩

end ValuationSpectrum
