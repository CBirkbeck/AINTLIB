/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-!
# Basic-open neighborhoods of minimal primes

An element of a minimal prime can be killed, up to nilpotence, by an element outside that prime.
Consequently, a minimal prime has a basic-open neighborhood disjoint from any quasi-compact open
that does not contain it. This is [Stacks Project, Tag 00EV](https://stacks.math.columbia.edu/tag/00EV).
-/

open TopologicalSpace

universe u

variable {R : Type u} [CommSemiring R]

/-- If `x` belongs to a minimal prime `p`, some element outside `p` makes `x` nilpotent after
multiplication. -/
lemma Ideal.exists_notMem_isNilpotent_mul_of_mem_minimalPrimes
    {p : Ideal R} (hp : p ∈ minimalPrimes R) {x : R} (hx : x ∈ p) :
    ∃ y ∉ p, IsNilpotent (x * y) := by
  letI : p.IsPrime := hp.isPrime
  let A := Localization.AtPrime p
  have hradical : ((⊥ : Ideal R).map (algebraMap R A)).radical =
      p.map (algebraMap R A) :=
    IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes A p (⊥ : Ideal R) hp
  have hxA : algebraMap R A x ∈ (⊥ : Ideal A).radical := by
    rw [← Ideal.map_bot (f := algebraMap R A), hradical]
    exact Ideal.mem_map_of_mem (algebraMap R A) hx
  obtain ⟨n, hn⟩ := hxA
  rw [Ideal.mem_bot, ← map_pow] at hn
  obtain ⟨s, hs⟩ :=
    (IsLocalization.map_eq_zero_iff p.primeCompl A (x ^ n)).mp hn
  refine ⟨s, s.2, n + 1, ?_⟩
  calc
    (x * (s : R)) ^ (n + 1) = ((s : R) * x ^ n) * (x * (s : R) ^ n) := by ring
    _ = 0 := by rw [hs, zero_mul]

/-- A minimal prime has a basic-open neighborhood disjoint from any quasi-compact open that does
not contain it. -/
lemma PrimeSpectrum.exists_basicOpen_disjoint_of_mem_minimalPrimes
    (p : PrimeSpectrum R) (hp : p.asIdeal ∈ minimalPrimes R)
    (W : Opens (PrimeSpectrum R)) (hW : IsCompact (W : Set (PrimeSpectrum R)))
    (hpW : p ∉ W) :
    ∃ f : R, p ∈ PrimeSpectrum.basicOpen f ∧
      Disjoint (PrimeSpectrum.basicOpen f) W := by
  obtain ⟨s, hs, hWs⟩ :=
    (PrimeSpectrum.isBasis_basic_opens.isCompact_open_iff_eq_finite_iUnion
      PrimeSpectrum.basicOpen PrimeSpectrum.isCompact_basicOpen (W : Set (PrimeSpectrum R))).mp
      ⟨hW, W.isOpen⟩
  have hrp (r : s) : r.1 ∈ p.asIdeal := by
    by_contra hrp
    apply hpW
    change p ∈ (W : Set (PrimeSpectrum R))
    rw [hWs]
    exact Set.mem_iUnion_of_mem r.1 (Set.mem_iUnion_of_mem r.2 hrp)
  choose y hy hnil using fun r : s ↦
    Ideal.exists_notMem_isNilpotent_mul_of_mem_minimalPrimes hp (hrp r)
  letI : Finite s := hs.to_subtype
  letI : Fintype s := Fintype.ofFinite s
  let f : R := ∏ r : s, y r
  have hfp : f ∉ p.asIdeal := by
    letI : p.asIdeal.IsPrime := p.2
    intro hf
    change (∏ r : s, y r) ∈ p.asIdeal at hf
    rw [Ideal.IsPrime.prod_mem_iff] at hf
    obtain ⟨r, -, hyr⟩ := hf
    exact hy r hyr
  refine ⟨f, hfp, disjoint_iff_inf_le.mpr ?_⟩
  rw [← SetLike.coe_subset_coe]
  rintro q ⟨hqf, hqW⟩
  rw [hWs] at hqW
  obtain ⟨r, hqW⟩ := Set.mem_iUnion.mp hqW
  obtain ⟨hrS, hqr⟩ := Set.mem_iUnion.mp hqW
  let i : s := ⟨r, hrS⟩
  have hry : r * y i ∈ q.asIdeal :=
    (nilpotent_iff_mem_prime.mp (hnil i)) q.asIdeal q.2
  have hyq : y i ∈ q.asIdeal := (q.2.mem_or_mem hry).resolve_left hqr
  apply hqf
  letI : q.asIdeal.IsPrime := q.2
  change (∏ r : s, y r) ∈ q.asIdeal
  rw [Ideal.IsPrime.prod_mem_iff]
  exact ⟨i, Finset.mem_univ i, hyq⟩

namespace AlgebraicGeometry

variable {X : Scheme.{u}} {U W : X.Opens} (hU : IsAffineOpen U) {x : X}

/-- A generic point of an irreducible component corresponds to a minimal prime in every affine
open containing it. -/
lemma IsAffineOpen.primeIdealOf_mem_minimalPrimes_of_closure_mem_irreducibleComponents
    (hxU : x ∈ U) (hx : closure {x} ∈ irreducibleComponents X) :
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal ∈ minimalPrimes Γ(X, U) := by
  let xU : U := ⟨x, hxU⟩
  have hcomponentU : closure {xU} ∈ irreducibleComponents U := by
    rw [U.isOpenEmbedding'.closure_eq_preimage_closure_image, Set.image_singleton]
    exact preimage_mem_irreducibleComponents hx U.isOpenEmbedding'
      ⟨x, subset_closure rfl, xU, rfl⟩
  let e := hU.isoSpec.schemeIsoToHomeo
  have hcomponentSpec :
      closure {hU.primeIdealOf xU} ∈ irreducibleComponents (Spec Γ(X, U)) := by
    change closure {e xU} ∈ irreducibleComponents (Spec Γ(X, U))
    have hImage := image_mem_irreducibleComponents_of_isPreirreducible_fiber e e.continuous
      e.isOpenMap
      (fun _ ↦ (Set.subsingleton_singleton.preimage e.injective).isPreirreducible)
      e.surjective hcomponentU
    have heq : e '' closure ({xU} : Set U) = closure (e '' ({xU} : Set U)) :=
      e.image_closure _
    have hsingle : e '' ({xU} : Set U) = {e xU} := Set.image_singleton
    convert hImage using 1
    exact (heq.trans (congrArg closure hsingle)).symm
  rwa [← PrimeSpectrum.vanishingIdeal_singleton,
    PrimeSpectrum.vanishingIdeal_mem_minimalPrimes]

/-- Inside an affine chart, a generic point of an irreducible component has a basic-open
neighborhood disjoint from any open whose pullback to the chart is compact and omits the point. -/
lemma IsAffineOpen.exists_basicOpen_disjoint_of_closure_mem_irreducibleComponents
    (hxU : x ∈ U) (hx : closure {x} ∈ irreducibleComponents X)
    (hW : IsCompact (hU.fromSpec ⁻¹ᵁ W : Set (Spec Γ(X, U)))) (hxW : x ∉ W) :
    ∃ f : Γ(X, U), x ∈ X.basicOpen f ∧ Disjoint (X.basicOpen f) W := by
  let xU : U := ⟨x, hxU⟩
  let p := hU.primeIdealOf xU
  have hp : p.asIdeal ∈ minimalPrimes Γ(X, U) :=
    hU.primeIdealOf_mem_minimalPrimes_of_closure_mem_irreducibleComponents hxU hx
  have hpW : p ∉ hU.fromSpec ⁻¹ᵁ W := by
    intro hpW
    apply hxW
    change hU.fromSpec p ∈ W at hpW
    rwa [hU.fromSpec_primeIdealOf xU] at hpW
  obtain ⟨f, hpf, hfW⟩ :=
    PrimeSpectrum.exists_basicOpen_disjoint_of_mem_minimalPrimes p hp
      (hU.fromSpec ⁻¹ᵁ W) hW hpW
  have hxf : x ∈ X.basicOpen f := by
    have hpf₀ : hU.primeIdealOf xU ∈ PrimeSpectrum.basicOpen f := by
      simpa only [p] using hpf
    have hpf' : hU.primeIdealOf xU ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f := by
      rw [hU.fromSpec_preimage_basicOpen]
      exact hpf₀
    change hU.fromSpec (hU.primeIdealOf xU) ∈ X.basicOpen f at hpf'
    rw [hU.fromSpec_primeIdealOf xU] at hpf'
    exact hpf'
  refine ⟨f, hxf, disjoint_iff_inf_le.mpr ?_⟩
  rw [← SetLike.coe_subset_coe]
  rintro z ⟨hzf, hzW⟩
  let zU : U := ⟨z, X.basicOpen_le f hzf⟩
  let q := hU.primeIdealOf zU
  have hqf : q ∈ PrimeSpectrum.basicOpen f := by
    change hU.primeIdealOf zU ∈ PrimeSpectrum.basicOpen f
    rw [← hU.fromSpec_preimage_basicOpen]
    change hU.fromSpec (hU.primeIdealOf zU) ∈ X.basicOpen f
    rw [hU.fromSpec_primeIdealOf zU]
    exact hzf
  have hqW : q ∈ hU.fromSpec ⁻¹ᵁ W := by
    change hU.fromSpec q ∈ W
    rw [hU.fromSpec_primeIdealOf zU]
    exact hzW
  exact hfW.le_bot ⟨hqf, hqW⟩

/-- If a scheme has finitely many generic points of irreducible components, then each generic
point has an affine-open neighborhood disjoint from the closures of all the other generic points.
-/
lemma genericPoints.exists_affineOpen_disjoint_closure
    [Finite (genericPoints X)] (η : genericPoints X) :
    ∃ V : X.Opens, IsAffineOpen V ∧ η.1 ∈ V ∧
      ∀ ζ : genericPoints X, ζ ≠ η → Disjoint (V : Set X) (closure {ζ.1}) := by
  let S : Set (genericPoints X) := {ζ | ζ ≠ η}
  have hS : S.Finite := Set.toFinite S
  have hclosed : IsClosed (⋃ ζ ∈ S, closure {ζ.1}) :=
    hS.isClosed_biUnion fun _ _ ↦ isClosed_closure
  let C : X.Opens := ⟨(⋃ ζ ∈ S, closure {ζ.1})ᶜ, hclosed.isOpen_compl⟩
  have hηC : η.1 ∈ C := by
    intro hη
    simp only [Set.mem_iUnion] at hη
    obtain ⟨ζ, hζS, hηζ⟩ := hη
    have hsub : closure {η.1} ⊆ closure {ζ.1} :=
      closure_minimal (Set.singleton_subset_iff.mpr hηζ) isClosed_closure
    have heq : genericPoints.component η = genericPoints.component ζ := by
      apply Subtype.ext
      exact hsub.antisymm (η.2.2 ζ.2.1 hsub)
    exact hζS (genericPoints.component_injective heq).symm
  obtain ⟨_, ⟨V : X.Opens, hV, rfl⟩, hηV, hVC⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hηC C.isOpen
  refine ⟨V, hV, hηV, ?_⟩
  intro ζ hζ
  rw [Set.disjoint_left]
  intro x hxV hxζ
  exact hVC hxV (Set.mem_iUnion_of_mem ζ (Set.mem_iUnion_of_mem hζ hxζ))

/-- A finite set of generic points on a quasi-separated scheme admits pairwise-disjoint affine
open neighborhoods. -/
lemma genericPoints.exists_pairwise_disjoint_affineOpens
    [Finite (genericPoints X)] [QuasiSeparatedSpace X] :
    ∃ U : genericPoints X → X.Opens,
      (∀ η, IsAffineOpen (U η)) ∧
      (∀ η, η.1 ∈ U η) ∧
      Pairwise (fun η ζ ↦ Disjoint (U η) (U ζ)) := by
  choose V hV hηV hVdisj using fun η : genericPoints X ↦
    genericPoints.exists_affineOpen_disjoint_closure η
  let W : genericPoints X → X.Opens := fun η ↦
    ⨆ ζ : {ζ : genericPoints X // ζ ≠ η}, V η ⊓ V ζ.1
  have hWcompact (η : genericPoints X) : IsCompact (W η : Set X) := by
    simpa only [W, TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_inf] using
      (isCompact_iUnion fun ζ : {ζ : genericPoints X // ζ ≠ η} ↦
        (quasiSeparatedSpace_iff_forall_affineOpens.mp inferInstance)
          ⟨V η, hV η⟩ ⟨V ζ.1, hV ζ.1⟩)
  have hWle (η : genericPoints X) : W η ≤ V η :=
    iSup_le fun _ ↦ inf_le_left
  have hηW (η : genericPoints X) : η.1 ∉ W η := by
    intro hη
    obtain ⟨ζ, -, hηVζ⟩ := TopologicalSpace.Opens.mem_iSup.mp hη
    exact Set.disjoint_left.mp (hVdisj ζ.1 η ζ.2.symm) hηVζ (subset_closure rfl)
  have hWprecompact (η : genericPoints X) :
      IsCompact ((hV η).fromSpec ⁻¹ᵁ W η : Set (Spec Γ(X, V η))) := by
    apply (hV η).fromSpec.isOpenEmbedding.isInducing.isCompact_preimage' (hWcompact η)
    rw [(hV η).range_fromSpec]
    exact hWle η
  choose f hηf hfW using fun η : genericPoints X ↦
    (hV η).exists_basicOpen_disjoint_of_closure_mem_irreducibleComponents
      (hηV η) η.2 (hWprecompact η) (hηW η)
  let U : genericPoints X → X.Opens := fun η ↦ X.basicOpen (f η)
  refine ⟨U, fun η ↦ (hV η).basicOpen (f η), hηf, ?_⟩
  intro η ζ hηζ
  change Disjoint (X.basicOpen (f η)) (X.basicOpen (f ζ))
  rw [← TopologicalSpace.Opens.coe_disjoint, Set.disjoint_left]
  intro x hxη hxζ
  have hfWη := hfW η
  rw [← TopologicalSpace.Opens.coe_disjoint] at hfWη
  apply Set.disjoint_left.mp hfWη hxη
  apply TopologicalSpace.Opens.mem_iSup.mpr
  exact ⟨⟨ζ, hηζ.symm⟩, X.basicOpen_le (f η) hxη, X.basicOpen_le (f ζ) hxζ⟩

/-- A quasi-separated scheme with finitely many generic points has an affine open containing all
of them. -/
lemma genericPoints.exists_affineOpen_containing
    [Finite (genericPoints X)] [QuasiSeparatedSpace X] :
    ∃ U : X.Opens, IsAffineOpen U ∧ ∀ η : genericPoints X, η.1 ∈ U := by
  obtain ⟨U, hU, hηU, hdisj⟩ := genericPoints.exists_pairwise_disjoint_affineOpens (X := X)
  refine ⟨⨆ η, U η, IsAffineOpen.iSup_of_disjoint hU hdisj, ?_⟩
  intro η
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨η, hηU η⟩

/-- Given an arbitrary point on a quasi-separated scheme with finitely many generic points, there
is an affine open containing that point and every generic point. -/
lemma genericPoints.exists_affineOpen_containing_point
    [Finite (genericPoints X)] [QuasiSeparatedSpace X] (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      ∀ η : genericPoints X, η.1 ∈ U := by
  let B : Set (genericPoints X) := {η | x ∉ closure {η.1}}
  have hB : B.Finite := Set.toFinite B
  have hclosed : IsClosed (⋃ η ∈ B, closure {η.1}) :=
    hB.isClosed_biUnion fun _ _ ↦ isClosed_closure
  let C : X.Opens := ⟨(⋃ η ∈ B, closure {η.1})ᶜ, hclosed.isOpen_compl⟩
  have hxC : x ∈ C := by
    intro hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨η, hηB, hxη⟩ := hx
    exact hηB hxη
  obtain ⟨_, ⟨W : X.Opens, hW, rfl⟩, hxW, hWC⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxC C.isOpen
  have hWdisj (η : genericPoints X) (hηB : η ∈ B) :
      Disjoint (W : Set X) (closure {η.1}) := by
    rw [Set.disjoint_left]
    intro y hyW hyη
    exact hWC hyW (Set.mem_iUnion_of_mem η (Set.mem_iUnion_of_mem hηB hyη))
  obtain ⟨V, hV, hηV, hVpair⟩ :=
    genericPoints.exists_pairwise_disjoint_affineOpens (X := X)
  have hprecompact (η : B) :
      IsCompact ((hV η.1).fromSpec ⁻¹ᵁ W : Set (Spec Γ(X, V η.1))) := by
    change IsCompact ((hV η.1).fromSpec ⁻¹' (W : Set X))
    rw [← Set.preimage_inter_range]
    apply (hV η.1).fromSpec.isOpenEmbedding.isInducing.isCompact_preimage'
    · rw [(hV η.1).range_fromSpec]
      exact (quasiSeparatedSpace_iff_forall_affineOpens.mp inferInstance)
        ⟨W, hW⟩ ⟨V η.1, hV η.1⟩
    · exact Set.inter_subset_right
  have hηW (η : B) : η.1.1 ∉ W := by
    intro hη
    exact Set.disjoint_left.mp (hWdisj η.1 η.2) hη (subset_closure rfl)
  choose f hηf hfW using fun η : B ↦
    (hV η.1).exists_basicOpen_disjoint_of_closure_mem_irreducibleComponents
      (hηV η.1) η.1.2 (hprecompact η) (hηW η)
  let V' : B → X.Opens := fun η ↦ X.basicOpen (f η)
  have hV'aff (η : B) : IsAffineOpen (V' η) := (hV η.1).basicOpen (f η)
  have hV'pair : Pairwise (fun η ζ ↦ Disjoint (V' η) (V' ζ)) := by
    intro η ζ hηζ
    change Disjoint (X.basicOpen (f η)) (X.basicOpen (f ζ))
    rw [← TopologicalSpace.Opens.coe_disjoint, Set.disjoint_left]
    intro y hyη hyζ
    have hpair := hVpair (show η.1 ≠ ζ.1 from fun h ↦ hηζ (Subtype.ext h))
    change Disjoint (V η.1) (V ζ.1) at hpair
    rw [← TopologicalSpace.Opens.coe_disjoint, Set.disjoint_left] at hpair
    exact hpair (X.basicOpen_le (f η) hyη) (X.basicOpen_le (f ζ) hyζ)
  let A : X.Opens := ⨆ η : B, V' η
  have hA : IsAffineOpen A := IsAffineOpen.iSup_of_disjoint hV'aff hV'pair
  have hWA : Disjoint W A := by
    rw [← TopologicalSpace.Opens.coe_disjoint, Set.disjoint_left]
    intro y hyW hyA
    obtain ⟨η, hyη⟩ := TopologicalSpace.Opens.mem_iSup.mp hyA
    have hηdisj := hfW η
    rw [← TopologicalSpace.Opens.coe_disjoint, Set.disjoint_left] at hηdisj
    exact hηdisj hyη hyW
  refine ⟨W ⊔ A, hW.sup_of_disjoint hA hWA,
    TopologicalSpace.Opens.mem_sup.mpr (.inl hxW), ?_⟩
  intro η
  by_cases hηB : x ∉ closure {η.1}
  · apply TopologicalSpace.Opens.mem_sup.mpr
    right
    apply TopologicalSpace.Opens.mem_iSup.mpr
    exact ⟨⟨η, hηB⟩, hηf ⟨η, hηB⟩⟩
  · have hxη : x ∈ closure {η.1} := not_not.mp hηB
    obtain ⟨y, hyW, hyη⟩ := (mem_closure_iff.mp hxη) W W.isOpen hxW
    simp only [Set.mem_singleton_iff] at hyη
    apply TopologicalSpace.Opens.mem_sup.mpr
    left
    simpa [hyη] using hyW

end AlgebraicGeometry
