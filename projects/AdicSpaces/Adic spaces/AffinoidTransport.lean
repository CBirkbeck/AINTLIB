/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».SheafyFoundations

/-!
# Transport of affinoid data along bicontinuous ring equivalences (P2.12)

Bounded sets, power-bounded elements, and rings of integral elements transport
along a ring equivalence that is continuous in both directions (an isomorphism
of topological rings):

* `TopologicalRing.IsBounded.image` — the image of a bounded set is bounded.
* `TopologicalRing.IsPowerBounded.ringEquiv` — power-boundedness transports.
  (The general `IsPowerBounded.map` along a *mere continuous ring hom* is
  **false** — see its docstring in `Presheaf.lean`; continuity of the inverse
  is what makes the image-neighborhood argument work. This file does not use
  that sorried statement.)
* `ValuationSpectrum.IsRingOfIntegralElements.map` — Wedhorn Definition 7.14(1)
  is invariant: openness via the inverse's continuity, integral closedness by
  pulling monic witnesses back through the inverse, power-boundedness by the
  transport above.
* `ValuationSpectrum.RingOfIntegralElements.map` / `.congr` — the bundled form
  and the induced equivalence of the types of rings of integral elements
  (`comap` along `e` is `map` along `e.symm`, i.e. `(congr e he he').symm`).

## Reference

Wedhorn, *Adic Spaces*: Definition 5.27, Definition 7.14, Remark 7.15.
-/

noncomputable section

open Filter Topology Pointwise

namespace TopologicalRing

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [CommRing B]
  [TopologicalSpace B]

/-- The image of a bounded set under a bicontinuous ring equivalence is bounded
(Wedhorn Definition 5.27 is invariant under isomorphisms of topological rings). -/
theorem IsBounded.image {S : Set A} (hS : IsBounded S) (e : A ≃+* B)
    (he : Continuous e) (he' : Continuous e.symm) :
    IsBounded (⇑e '' S) := by
  intro U' hU'
  have hU : ⇑e ⁻¹' U' ∈ 𝓝 (0 : A) :=
    he.continuousAt.preimage_mem_nhds ((map_zero e).symm ▸ hU')
  obtain ⟨V, hV, hSV⟩ := hS _ hU
  refine ⟨⇑e '' V, ?_, ?_⟩
  · rw [show ⇑e '' V = ⇑e.symm ⁻¹' V from e.toEquiv.image_eq_preimage_symm V]
    exact he'.continuousAt.preimage_mem_nhds ((map_zero e.symm).symm ▸ hV)
  · rw [← Set.image_mul e]
    exact (Set.image_mono hSV).trans (Set.image_preimage_subset _ _)

/-- Power-boundedness transports along a bicontinuous ring equivalence. -/
theorem IsPowerBounded.ringEquiv {a : A} (ha : IsPowerBounded a) (e : A ≃+* B)
    (he : Continuous e) (he' : Continuous e.symm) :
    IsPowerBounded (e a) := by
  show IsBounded (Set.range ((e a) ^ · : ℕ → B))
  have himg : Set.range ((e a) ^ · : ℕ → B) = ⇑e '' Set.range (a ^ · : ℕ → A) := by
    rw [← Set.range_comp]
    exact congrArg _ (funext fun n => (map_pow e a n).symm)
  rw [himg]
  exact TopologicalRing.IsBounded.image ha e he he'

end TopologicalRing

namespace ValuationSpectrum

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [CommRing B]
  [TopologicalSpace B]

/-- **Wedhorn Definition 7.14(1) is invariant under bicontinuous ring
equivalences**: the image of a ring of integral elements is a ring of integral
elements. -/
theorem IsRingOfIntegralElements.map {P : Subring A}
    (hP : IsRingOfIntegralElements P) (e : A ≃+* B)
    (he : Continuous e) (he' : Continuous e.symm) :
    IsRingOfIntegralElements (P.map e.toRingHom) where
  isOpen := by
    rw [Subring.coe_map, show ⇑e.toRingHom '' (P : Set A) = ⇑e.symm ⁻¹' (P : Set A)
      from e.toEquiv.image_eq_preimage_symm _]
    exact hP.isOpen.preimage he'
  isIntegrallyClosed := by
    intro b hb
    obtain ⟨p, hmonic, heval⟩ := hb
    -- pull the monic witness back through the inverse
    set ψ : ↥(P.map e.toRingHom) →+* ↥P :=
      RingHom.codRestrict (e.symm.toRingHom.comp (P.map e.toRingHom).subtype) P
        (fun x => by
          obtain ⟨a, haP, hax⟩ := x.2
          have hax' : e a = (x : B) := hax
          show e.symm (x : B) ∈ P
          rw [← hax', e.symm_apply_apply]
          exact haP) with hψ
    have hcomp : (algebraMap ↥P A).comp ψ =
        e.symm.toRingHom.comp (algebraMap ↥(P.map e.toRingHom) B) :=
      RingHom.ext fun x => rfl
    have hpush := Polynomial.hom_eval₂ p
      (algebraMap ↥(P.map e.toRingHom) B) e.symm.toRingHom b
    rw [heval, map_zero] at hpush
    have hint : IsIntegral ↥P (e.symm.toRingHom b) := by
      refine ⟨p.map ψ, hmonic.map ψ, ?_⟩
      rw [Polynomial.eval₂_map, hcomp]
      exact hpush.symm
    exact Subring.mem_map.mpr
      ⟨e.symm b, hP.isIntegrallyClosed _ hint, e.apply_symm_apply b⟩
  subset_powerBounded := by
    rintro _ ⟨a, haP, rfl⟩
    exact TopologicalRing.IsPowerBounded.ringEquiv
      (hP.subset_powerBounded haP) e he he'

namespace RingOfIntegralElements

/-- The bundled transport of a ring of integral elements along a bicontinuous
ring equivalence (P2.12). -/
def map (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    (Aplus : RingOfIntegralElements A) : RingOfIntegralElements B :=
  ⟨(Aplus : Subring A).map e.toRingHom, Aplus.2.map e he he'⟩

@[simp] theorem coe_map (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    (Aplus : RingOfIntegralElements A) :
    ((map e he he' Aplus : RingOfIntegralElements B) : Subring B) =
      (Aplus : Subring A).map e.toRingHom := rfl

/-- Mapping forward and back along the inverse recovers the original. -/
theorem map_symm_map (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    (Aplus : RingOfIntegralElements A) :
    map e.symm he' he (map e he he' Aplus) = Aplus := by
  refine ext ?_
  show ((Aplus : Subring A).map e.toRingHom).map e.symm.toRingHom = (Aplus : Subring A)
  rw [Subring.map_map, show e.symm.toRingHom.comp e.toRingHom = RingHom.id A from
    RingHom.ext fun a => e.symm_apply_apply a, Subring.map_id]

/-- **The equivalence of the types of rings of integral elements** induced by a
bicontinuous ring equivalence (P2.12); the pull-back (`comap`) direction is
`.symm`. -/
def congr (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm) :
    RingOfIntegralElements A ≃ RingOfIntegralElements B where
  toFun := map e he he'
  invFun := map e.symm he' he
  left_inv := map_symm_map e he he'
  right_inv := fun Bplus => by
    refine ext ?_
    show ((Bplus : Subring B).map e.symm.toRingHom).map e.toRingHom = (Bplus : Subring B)
    rw [Subring.map_map, show e.toRingHom.comp e.symm.toRingHom = RingHom.id B from
      RingHom.ext fun b => e.apply_symm_apply b, Subring.map_id]

end RingOfIntegralElements

end ValuationSpectrum
