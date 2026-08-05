/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FarguesFontaine.ChartSpa
import «Adic spaces».FarguesFontaine.ChartBIQ
import «Adic spaces».NonTateRationalOpenHomeomorph
import «Adic spaces».RelativeDescent
import «Adic spaces».HuberLocLift

/-!
# The chart-rational index layer of `𝒴` (E-track, E1)

The enlarged basis for the Y-structure sheaf: indices are valid rational
data over the Big-window chart rings `B_n` (uniform over the window sign
through `windowUnif`), with traces on the valuation spectrum through the
chart homeomorphisms. See the board's E-track plan (E1–E6).
-/

open TopologicalRing ValuationSpectrum WittVector NNReal

set_option linter.overlappingInstances false

noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type*) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)

/-- One-is-less-than-`p` for the ambient prime. -/
theorem one_lt_p : 1 < p := Nat.Prime.one_lt (Fact.out : Nat.Prime p)

/-- **The window uniformizer**: the `p^n`-th Frobenius root for `n ≥ 0`, the
`p^{|n|}`-th power for `n < 0`. -/
def windowUnif : ℤ → PseudoUniformizer F
  | .ofNat k => PseudoUniformizer.frobRoot p F ϖ k
  | .negSucc m => PseudoUniformizer.pPow F ϖ (p ^ (m + 1))
      (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) (m + 1))

/-- **The window chart ring** `B_n`: the presheaf value of the Big-window
datum in the window uniformizer. -/
def windowRing (n : ℤ) : Type _ :=
  presheafValue (chartData p F (windowUnif p F ϖ n) 1 1 p 1)

noncomputable instance (n : ℤ) : CommRing (windowRing p F ϖ n) :=
  inferInstanceAs (CommRing (presheafValue
    (chartData p F (windowUnif p F ϖ n) 1 1 p 1)))

noncomputable instance (n : ℤ) : TopologicalSpace (windowRing p F ϖ n) :=
  inferInstanceAs (TopologicalSpace (presheafValue
    (chartData p F (windowUnif p F ϖ n) 1 1 p 1)))

instance (n : ℤ) : IsTopologicalRing (windowRing p F ϖ n) :=
  inferInstanceAs (IsTopologicalRing (presheafValue
    (chartData p F (windowUnif p F ϖ n) 1 1 p 1)))

noncomputable instance (n : ℤ) : PlusSubring (windowRing p F ϖ n) :=
  inferInstanceAs (PlusSubring (presheafValue
    (chartData p F (windowUnif p F ϖ n) 1 1 p 1)))

instance (n : ℤ) : IsTateRing (windowRing p F ϖ n) :=
  isTateRing_bigWindowChart p F (windowUnif p F ϖ n)

instance (n : ℤ) : IsHuberRing (windowRing p F ϖ n) :=
  IsTateRing.toIsHuberRing

/-- **A chart-rational index**: a window number together with a valid
rational datum over its chart ring. (A `Σ`-encoding: a `structure` with
this dependent field sends the kernel through the `presheafValue`
unfolding and deterministically times out.) -/
def ChartRatIdx : Type _ :=
  Σ n : ℤ, {D : RationalLocData (windowRing p F ϖ n) // D.IsRational}

namespace ChartRatIdx

/-- The window number. -/
def n (i : ChartRatIdx p F ϖ) : ℤ := i.1

/-- The rational datum. -/
def D (i : ChartRatIdx p F ϖ) : RationalLocData (windowRing p F ϖ (i.n p F ϖ)) :=
  i.2.1

/-- Validity of the datum. -/
theorem isRational (i : ChartRatIdx p F ϖ) : (i.D p F ϖ).IsRational :=
  i.2.2

/-- The rational open of a chart-rational index inside the window's `Spa`. -/
def spaSet (i : ChartRatIdx p F ϖ) :
    Set ↥(Spa (windowRing p F ϖ (i.n p F ϖ))
      (ringPlus (windowRing p F ϖ (i.n p F ϖ)))) :=
  spaOpen (i.D p F ϖ)

/-- **The trace of a chart-rational index on the valuation spectrum**:
the image of its rational open under the window chart homeomorphism
(dispatched per window sign at the set level). -/
def trace (i : ChartRatIdx p F ϖ) : Set (Spv (Ainf p F)) :=
  match i with
  | ⟨.ofNat k, D, hD⟩ =>
      Subtype.val '' (spaChartHomeoBigWindow p F ϖ k (one_lt_p p) ''
        (spaSet p F ϖ ⟨.ofNat k, D, hD⟩))
  | ⟨.negSucc m, D, hD⟩ =>
      Subtype.val '' (spaChartHomeoBigWindowNeg p F ϖ (m + 1) (one_lt_p p) ''
        (spaSet p F ϖ ⟨.negSucc m, D, hD⟩))

end ChartRatIdx

/-- **Chart-rational traces land inside `Y`.** -/
theorem ChartRatIdx.trace_subset_Y (i : ChartRatIdx p F ϖ) :
    ChartRatIdx.trace p F ϖ i ⊆ Y p F ϖ := by
  have hcov := Y_eq_iUnion_bigWindow p F ϖ (one_lt_p p)
  obtain ⟨n, DhD⟩ := i
  match n with
  | .ofNat k =>
    rintro v ⟨w, ⟨u, -, rfl⟩, rfl⟩
    have hw : ((spaChartHomeoBigWindow p F ϖ k (one_lt_p p) u
        : ↥(bigWindow p F ϖ (k : ℤ)
          ∩ Spa (Ainf p F) (ringPlus (Ainf p F)))) : Spv (Ainf p F))
        ∈ bigWindow p F ϖ (k : ℤ)
          ∩ Spa (Ainf p F) (ringPlus (Ainf p F)) :=
      (spaChartHomeoBigWindow p F ϖ k (one_lt_p p) u).2
    rw [hcov]
    exact Set.mem_iUnion.mpr ⟨(k : ℤ), hw.1⟩
  | .negSucc m =>
    rintro v ⟨w, ⟨u, -, rfl⟩, rfl⟩
    have hw : ((spaChartHomeoBigWindowNeg p F ϖ (m + 1) (one_lt_p p) u
        : ↥(bigWindow p F ϖ (-((m + 1 : ℕ) : ℤ))
          ∩ Spa (Ainf p F) (ringPlus (Ainf p F)))) : Spv (Ainf p F))
        ∈ bigWindow p F ϖ (-((m + 1 : ℕ) : ℤ))
          ∩ Spa (Ainf p F) (ringPlus (Ainf p F)) :=
      (spaChartHomeoBigWindowNeg p F ϖ (m + 1) (one_lt_p p) u).2
    rw [hcov]
    exact Set.mem_iUnion.mpr ⟨(-((m + 1 : ℕ) : ℤ)), hw.1⟩

omit [CharP F p] in
/-- Elements of the ideal of definition are topologically nilpotent. -/
theorem isTopologicallyNilpotent_of_mem_Iinf {x : Ainf p F}
    (hx : x ∈ Iinf p F ϖ) : IsTopologicallyNilpotent x :=
  (isAdic_Iinf p F ϖ).hasBasis_nhds_zero.tendsto_right_iff.mpr fun n _ ↦
    Filter.eventually_atTop.mpr ⟨n, fun m hm ↦
      Ideal.pow_le_pow_right hm (Ideal.pow_mem_pow hx m)⟩

omit [CharP F p] in
/-- `p·[ϖ]` is topologically nilpotent in `A_inf`. -/
theorem isTopologicallyNilpotent_p_teichPi :
    IsTopologicallyNilpotent ((p : Ainf p F) * teichPi p F ϖ) := by
  refine isTopologicallyNilpotent_of_mem_Iinf p F ϖ ?_
  exact Ideal.mul_mem_right _ _
    (Ideal.subset_span (Set.mem_insert _ _))

include ϖ in
/-- **`A_inf` is separated**: distinct points are separated by cosets of a
common ideal power (cosets of a subgroup are equal or disjoint). -/
theorem t2Space_Ainf : T2Space (Ainf p F) := by
  refine ⟨fun x y hxy => ?_⟩
  have hne : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hnotall : ¬ ∀ n : ℕ, x - y ∈ (Iinf p F ϖ) ^ n := by
    intro hall
    refine hne ((isHausdorff_Iinf p F ϖ).haus (x - y) fun n => ?_)
    rw [SModEq.zero]
    simpa using hall n
  push Not at hnotall
  obtain ⟨n, hn⟩ := hnotall
  have hopen : IsOpen ((Iinf p F ϖ ^ n : Ideal (Ainf p F))
      : Set (Ainf p F)) :=
    (isAdic_iff.mp (isAdic_Iinf p F ϖ)).1 n
  refine ⟨(x + ·) '' (Iinf p F ϖ ^ n : Ideal (Ainf p F)),
    (y + ·) '' (Iinf p F ϖ ^ n : Ideal (Ainf p F)),
    (isOpenMap_add_left x) _ hopen, (isOpenMap_add_left y) _ hopen,
    ⟨0, by simp⟩,
    ⟨0, by simp⟩, ?_⟩
  rw [Set.disjoint_left]
  rintro z ⟨a, ha, rfl⟩ ⟨b, hb, hz⟩
  refine hn ?_
  have : x - y = b - a := by linear_combination -hz
  rw [this]
  exact sub_mem hb ha

/-- **Per-datum concrete Tate structure over the non-Tate base** `A_inf`
(the E2-route-(b) unblock): a valid rational datum whose rational open lies
inside `𝒴` has a Tate completed localization — the image of `p·[ϖ]` is a
topologically nilpotent unit (unit by the complete-pair Nullstellensatz
criterion, since no `Spa`-point of the completion kills `p·[ϖ]`). -/
theorem isTateRing_presheafValue_of_rationalOpen_subset_Y
    (D : RationalLocData (Ainf p F))
    (hsub : rationalOpen D.T D.s ⊆ Y p F ϖ) :
    IsTateRing (presheafValue D) := by
  have : IsRingOfIntegralElements ((Ainf p F)⁺ : Subring (Ainf p F)) :=
    isAffinoidRing_Ainf p F
  have : T2Space (Ainf p F) := t2Space_Ainf p F ϖ
  have hx_nil : IsTopologicallyNilpotent
      (D.canonicalMap ((p : Ainf p F) * teichPi p F ϖ)) :=
    (isTopologicallyNilpotent_p_teichPi p F ϖ).map
      (canonicalMap_continuous D)
  have hx_unit : IsUnit
      (D.canonicalMap ((p : Ainf p F) * teichPi p F ϖ)) := by
    letI : IsHuberRing (presheafValue D) :=
      presheafValue_isHuberRing_huber D
    have : IsAdicComplete (presheafValue_concretePair D).I
        (presheafValue_concretePair D).A₀ :=
      presheafValue_isAdicComplete D
    refine (isUnit_iff_forall_not_vle_zero_of_completePair
      (presheafValue_concretePair D) _).mpr fun w hw => ?_
    have hmem := comap_canonicalMap_mem_rationalOpen D
      (canonicalMap_continuous D) hw
    have hY := hsub hmem
    intro hcon
    exact hY.2 ((comap_vle D.canonicalMap w _ 0).mpr
      (by rwa [map_zero]))
  exact
    { exists_pairOfDefinition := ⟨presheafValue_concretePair D⟩
      exists_topologicallyNilpotent_unit :=
        ⟨hx_unit.unit, by rwa [IsUnit.unit_spec]⟩ }

include ϖ in
/-- **`A_inf` is complete for the right uniformity** (from `(p,[ϖ])`-adic
completeness through the mathlib bridge). -/
theorem completeSpace_right_Ainf :
    @CompleteSpace (Ainf p F)
      (IsTopologicalAddGroup.rightUniformSpace (Ainf p F)) := by
  letI : UniformSpace (Ainf p F) :=
    IsTopologicalAddGroup.rightUniformSpace (Ainf p F)
  have : IsUniformAddGroup (Ainf p F) := isUniformAddGroup_of_addCommGroup
  exact ((isAdic_Iinf p F ϖ).isAdicComplete_iff.mp
    (isAdicComplete_Iinf p F ϖ)).1

include ϖ in
/-- **The M8 instantiation**: the localization-lift power-boundedness
package at the ambient `A_inf`. -/
theorem hasLocLiftPowerBounded_Ainf :
    HasLocLiftPowerBounded (Ainf p F) := by
  have : IsRingOfIntegralElements ((Ainf p F)⁺ : Subring (Ainf p F)) :=
    isAffinoidRing_Ainf p F
  have : T2Space (Ainf p F) := t2Space_Ainf p F ϖ
  have := completeSpace_right_Ainf p F ϖ
  exact hasLocLiftPowerBounded_huber

end FarguesFontaine

end
