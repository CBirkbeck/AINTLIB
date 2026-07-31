/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB AI workers
-/
import «Adic spaces».SpaRationalOpenHomeomorph

/-!
# The Wedhorn 8.2 homeomorphism over a Huber (non-Tate) base

Primed variants of the openness half of Wedhorn Proposition 8.2(2), with the
`[IsTateRing A]` hypothesis replaced by its actual content: a topologically
nilpotent **unit of the completion** `presheafValue D`, supplied as a
parameter. This makes the chart homeomorphism available over the non-Tate
base `A_inf` of the Fargues–Fontaine curve, whose Big-window chart rings are
Tate even though the base is not (the unit is the image of `p`).

* (`ValuationSpectrum.exists_A_level_open_presentation'` now lives
  upstream in `SpaRationalOpenHomeomorph`, next to the Tate corollary
  it generalises.)
* `ValuationSpectrum.spaPresheafValueEquivRationalOpen_isOpenMap'`
* `ValuationSpectrum.spaPresheafValueHomeomorphRationalOpen'`

The proofs are verbatim those of `SpaRationalOpenHomeomorph.lean` minus the
`presheafValue_topNilUnit` extraction (Huber's approximation argument never
uses the base unit, only the completion one).
-/

noncomputable section

open Filter Topology

open scoped Classical

set_option linter.overlappingInstances false

namespace ValuationSpectrum

universe u v

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A]

/-- **Openness of the Wedhorn 8.2 comparison map**: the forward map of
`spaPresheafValueEquivRationalOpen` is an open map. -/

theorem spaPresheafValueEquivRationalOpen_isOpenMap'
    [IsRingOfIntegralElements (A⁺ : Subring A)] (D : RationalLocData A)
    (u : (presheafValue D)ˣ)
    (hu : IsTopologicallyNilpotent ((u : (presheafValue D)ˣ) : presheafValue D)) :
    IsOpenMap (spaPresheafValueEquivRationalOpen D) := by
  classical
  intro Uopen hUopen
  rw [isOpen_iff_forall_mem_open]
  rintro y ⟨w, hwU, rfl⟩
  obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.mp hUopen
  have hbasis := TopologicalSpace.isTopologicalBasis_of_subbasis
    (t := (instTopologicalSpace : TopologicalSpace (Spv (presheafValue D))))
    (s := {U : Set (Spv (presheafValue D)) | ∃ f s, U = basicOpen f s}) rfl
  have hwV : (w : Spv (presheafValue D)) ∈ V := hwU
  obtain ⟨t, ht, hwt, htV⟩ := hbasis.exists_subset_of_mem_open hwV hV
  obtain ⟨fam₀, ⟨hfam₀_fin, hfam₀_sub⟩, rfl⟩ := ht
  -- choose parameters for each member of the finite family
  have hFG : ∀ e : Set (Spv (presheafValue D)),
      ∃ p : presheafValue D × presheafValue D, e ∈ fam₀ →
        e = basicOpen p.1 p.2 := by
    intro e
    by_cases he : e ∈ fam₀
    · obtain ⟨f, s, rfl⟩ := hfam₀_sub he
      exact ⟨(f, s), fun _ => rfl⟩
    · exact ⟨(0, 0), fun hc => absurd hc he⟩
  choose P hP using hFG
  have hmem : ∀ e ∈ hfam₀_fin.toFinset,
      (w : Spv (presheafValue D)) ∈ basicOpen (P e).1 (P e).2 := by
    intro e he
    rw [← hP e ((Set.Finite.mem_toFinset _).mp he)]
    exact hwt _ ((Set.Finite.mem_toFinset _).mp he)
  obtain ⟨W, hW_open, hW_mem, hW_capture⟩ := exists_A_level_open_presentation' D u hu w.2
    (fam := hfam₀_fin.toFinset) (F := fun e => (P e).1) (G := fun e => (P e).2) hmem
  refine ⟨Subtype.val ⁻¹' W, ?_, hW_open.preimage continuous_subtype_val, hW_mem⟩
  intro z hz
  refine ⟨(spaPresheafValueEquivRationalOpen D).symm z, ?_,
    Equiv.apply_symm_apply _ z⟩
  have hspa := ((spaPresheafValueEquivRationalOpen D).symm z).2
  have hcm : comap D.canonicalMap
      (((spaPresheafValueEquivRationalOpen D).symm z :
        ↥(Spa (presheafValue D) (presheafValue D)⁺)) : Spv (presheafValue D)) =
      (z : Spv A) :=
    congrArg Subtype.val
      (Equiv.apply_symm_apply (spaPresheafValueEquivRationalOpen D) z)
  have hin := hW_capture _ hspa (by rw [hcm]; exact hz)
  show (((spaPresheafValueEquivRationalOpen D).symm z : _) : Spv (presheafValue D)) ∈ V
  refine htV ?_
  rw [Set.mem_sInter]
  intro e he
  rw [hP e he]
  exact hin e ((Set.Finite.mem_toFinset _).mpr he)

/-- **Wedhorn Proposition 8.2(2), the homeomorphism, non-Tate-base form**:
under a supplied topologically nilpotent unit of the completion,
`Spa (presheafValue D) ((presheafValue D)⁺) ≃ₜ R(T/s) ∩ Spa (A, A⁺)`. -/
def spaPresheafValueHomeomorphRationalOpen'
    [IsRingOfIntegralElements (A⁺ : Subring A)] (D : RationalLocData A)
    (u : (presheafValue D)ˣ)
    (hu : IsTopologicallyNilpotent ((u : (presheafValue D)ˣ) : presheafValue D)) :
    ↥(Spa (presheafValue D) (presheafValue D)⁺) ≃ₜ
      ↥(rationalOpen D.T D.s ∩ Spa A A⁺ : Set (Spv A)) :=
  (spaPresheafValueEquivRationalOpen D).toHomeomorphOfContinuousOpen
    (spaPresheafValueEquivRationalOpen_continuous D)
    (spaPresheafValueEquivRationalOpen_isOpenMap' D u hu)

/-- **Rational subsets pull back along the canonical map** (the forward half of
Wedhorn 8.2(2)'s subset correspondence, pointwise form — Huber-base generic):
for a Spa-point `w` of the completed localization, `comap w` lies in
`R(T'/s')` iff `w` lies in the rational subset with the image parameters. -/
theorem comap_canonicalMap_mem_rationalOpen_iff
    {D : RationalLocData A} [DecidableEq (presheafValue D)]
    {w : Spv (presheafValue D)}
    (hw : w ∈ Spa (presheafValue D) (presheafValue D)⁺)
    (T' : Finset A) (s' : A) :
    comap D.canonicalMap w ∈ rationalOpen T' s'
      ↔ w ∈ rationalOpen (T'.image D.canonicalMap) (D.canonicalMap s') := by
  constructor
  · rintro ⟨-, hT, hs⟩
    refine ⟨hw, ?_, ?_⟩
    · intro t ht
      obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp ht
      exact (comap_vle D.canonicalMap w t' s').mp (hT t' ht')
    · intro hcon
      refine hs ?_
      rw [comap_vle, map_zero] at *
      exact hcon
  · rintro ⟨-, hT, hs⟩
    refine ⟨comap_canonicalMap_mem_spa D ⟨w, hw⟩, ?_, ?_⟩
    · intro t ht
      exact (comap_vle D.canonicalMap w t s').mpr
        (hT _ (Finset.mem_image_of_mem _ ht))
    · intro hcon
      refine hs ?_
      have := (comap_vle D.canonicalMap w s' 0).mp hcon
      rwa [map_zero] at this

end ValuationSpectrum

end
