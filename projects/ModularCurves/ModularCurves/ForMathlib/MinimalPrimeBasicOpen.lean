/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
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
