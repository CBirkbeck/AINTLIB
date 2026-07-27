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

* `ValuationSpectrum.exists_A_level_open_presentation'`
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

theorem exists_A_level_open_presentation'
    [IsRingOfIntegralElements (A⁺ : Subring A)] (D : RationalLocData A)
    (u : (presheafValue D)ˣ)
    (hu : IsTopologicallyNilpotent ((u : (presheafValue D)ˣ) : presheafValue D))
    {w : Spv (presheafValue D)}
    (hw : w ∈ Spa (presheafValue D) (presheafValue D)⁺)
    {ι : Type v} [DecidableEq ι] {fam : Finset ι} {F G : ι → presheafValue D}
    (hmem : ∀ i ∈ fam, w ∈ basicOpen (F i) (G i)) :
    ∃ W : Set (Spv A), IsOpen W ∧ comap D.canonicalMap w ∈ W ∧
      ∀ w' : Spv (presheafValue D),
        w' ∈ Spa (presheafValue D) (presheafValue D)⁺ →
        comap D.canonicalMap w' ∈ W →
        ∀ i ∈ fam, w' ∈ basicOpen (F i) (G i) := by
  classical
  have hϖ_unit : IsUnit ((u : (presheafValue D)ˣ) : presheafValue D) := u.isUnit
  -- Step 1: spanning presentation inside the intersection
  obtain ⟨f, g, hspan, hw_mem, hsubset⟩ :=
    exists_spanning_presentation_of_mem_basicOpens hϖ_unit hu hw hmem
  set idx : Finset (Option ι) := insert none (fam.image some) with hidx_def
  -- Step 2: uniform bound + density approximation into the localization image
  obtain ⟨M, hM⟩ :=
    exists_uniform_bound_insert hu (s := idx) (f := f) (g := g) hspan
  have hdense : DenseRange (⇑(D.coeRingHom)) := fun y =>
    @UniformSpace.Completion.denseRange_coe _ D.uniformSpace y
  have hcoset : ∀ x : presheafValue D, ∃ l : Localization.Away D.s,
      ∃ b ∈ ((presheafValue D)⁺ : Subring (presheafValue D)),
        D.coeRingHom l = x + (u : presheafValue D) ^ (M + 1) * b := by
    intro x
    obtain ⟨u', hu'⟩ := (hϖ_unit.pow (M + 1)).exists_left_inv
    have hplus : IsOpen (((presheafValue D)⁺ :
        Subring (presheafValue D)) : Set (presheafValue D)) :=
      (inferInstance : IsRingOfIntegralElements
        ((presheafValue D)⁺ : Subring (presheafValue D))).isOpen
    have hO_open : IsOpen ((fun y => u' * (y - x)) ⁻¹'
        (((presheafValue D)⁺ : Subring (presheafValue D)) :
          Set (presheafValue D))) :=
      hplus.preimage (continuous_const.mul (continuous_id.sub continuous_const))
    have hxO : x ∈ (fun y => u' * (y - x)) ⁻¹'
        (((presheafValue D)⁺ : Subring (presheafValue D)) :
          Set (presheafValue D)) := by
      simp only [Set.mem_preimage, sub_self, mul_zero, SetLike.mem_coe]
      exact Subring.zero_mem _
    obtain ⟨l, hl⟩ := hdense.exists_mem_open hO_open ⟨x, hxO⟩
    refine ⟨l, u' * (D.coeRingHom l - x), hl, ?_⟩
    have hcalc : (u : presheafValue D) ^ (M + 1) * (u' * (D.coeRingHom l - x)) =
        D.coeRingHom l - x := by
      rw [← mul_assoc, mul_comm ((u : presheafValue D) ^ (M + 1)) u', hu', one_mul]
    rw [hcalc]
    ring
  choose lf bf hbf hlf using fun o => hcoset (f o)
  obtain ⟨lg, bg, hbg, hlg⟩ := hcoset g
  have hpert : indexedRationalSet (presheafValue D) idx f g =
      indexedRationalSet (presheafValue D) idx
        (fun o => D.coeRingHom (lf o)) (D.coeRingHom lg) :=
    indexedRationalSet_perturb_eq hϖ_unit hu hM
      (fun o _ => ⟨bf o, hbf o, hlf o⟩) ⟨bg, hbg, hlg⟩
  -- Step 3: clear denominators — scale by the unit `canonicalMap b`
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples
    (Submonoid.powers D.s) (insert none (idx.image some))
    (fun o : Option (Option ι) => o.elim lg lf)
  have hbg' : IsLocalization.IsInteger A ((b : A) • lg) :=
    hb none (Finset.mem_insert_self _ _)
  have hbf' : ∀ o : Option ι, ∃ a : A, o ∈ idx →
      algebraMap A (Localization.Away D.s) a = (b : A) • lf o := by
    intro o
    by_cases ho : o ∈ idx
    · obtain ⟨a, ha⟩ := hb (some o)
        (Finset.mem_insert_of_mem (Finset.mem_image_of_mem some ho))
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun hc => absurd hc ho⟩
  choose hA hhA using hbf'
  obtain ⟨q, hq⟩ := hbg'
  set U : presheafValue D :=
    D.coeRingHom (algebraMap A (Localization.Away D.s) (b : A)) with hU_def
  have hU_unit : IsUnit U :=
    (IsLocalization.map_units (Localization.Away D.s) b).map D.coeRingHom
  have hqparam : D.canonicalMap q = U * D.coeRingHom lg := by
    have hstep := congrArg D.coeRingHom hq
    rw [Algebra.smul_def, map_mul] at hstep
    exact hstep
  have hparam : ∀ o ∈ idx, D.canonicalMap (hA o) = U * D.coeRingHom (lf o) := by
    intro o ho
    have hstep := congrArg D.coeRingHom (hhA o ho)
    rw [Algebra.smul_def, map_mul] at hstep
    exact hstep
  have hset' : indexedRationalSet (presheafValue D) idx
      (fun o => D.canonicalMap (hA o)) (D.canonicalMap q) =
      indexedRationalSet (presheafValue D) idx
        (fun o => D.coeRingHom (lf o)) (D.coeRingHom lg) := by
    have hstep : indexedRationalSet (presheafValue D) idx
        (fun o => D.canonicalMap (hA o)) (D.canonicalMap q) =
        indexedRationalSet (presheafValue D) idx
          (fun o => U * D.coeRingHom (lf o)) (U * D.coeRingHom lg) := by
      ext v
      simp only [indexedRationalSet, Set.mem_setOf_eq]
      refine and_congr_right fun hv => ?_
      rw [hqparam]
      constructor
      · rintro ⟨hT, h0⟩
        exact ⟨fun o ho => by rw [← hparam o ho]; exact hT o ho, h0⟩
      · rintro ⟨hT, h0⟩
        exact ⟨fun o ho => by rw [hparam o ho]; exact hT o ho, h0⟩
    rw [hstep, indexedRationalSet_unit_mul_eq hU_unit]
  have hchain : indexedRationalSet (presheafValue D) idx f g =
      indexedRationalSet (presheafValue D) idx
        (fun o => D.canonicalMap (hA o)) (D.canonicalMap q) :=
    hpert.trans hset'.symm
  -- Step 4: the downstairs open and the transfer
  refine ⟨⋂ o ∈ idx, basicOpen (hA o) q, ?_, ?_, ?_⟩
  · exact isOpen_biInter_finset fun o _ =>
      TopologicalSpace.isOpen_generateFrom_of_mem ⟨hA o, q, rfl⟩
  · have hw_mem' : w ∈ indexedRationalSet (presheafValue D) idx
        (fun o => D.canonicalMap (hA o)) (D.canonicalMap q) := hchain ▸ hw_mem
    obtain ⟨-, hT, h0⟩ := hw_mem'
    simp only [Set.mem_iInter]
    intro o ho
    exact ⟨hT o ho, by rwa [comap_vle, map_zero]⟩
  · intro w' hw' hWmem
    simp only [Set.mem_iInter] at hWmem
    have hmem' : w' ∈ indexedRationalSet (presheafValue D) idx
        (fun o => D.canonicalMap (hA o)) (D.canonicalMap q) := by
      refine ⟨hw', fun o ho => (hWmem o ho).1, ?_⟩
      have := (hWmem none (Finset.mem_insert_self _ _)).2
      rwa [comap_vle, map_zero] at this
    rw [← hchain] at hmem'
    have hfinal := hsubset hmem'
    simp only [Set.mem_iInter] at hfinal
    exact hfinal

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

end ValuationSpectrum

end
