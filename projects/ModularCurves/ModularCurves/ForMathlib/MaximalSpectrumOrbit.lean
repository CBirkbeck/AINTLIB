/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import Mathlib

/-!
# Finiteness of the maximal spectrum of an invariant extension

For a finite group `G` acting on a commutative ring `B` with `Algebra.IsInvariant A B G`
(e.g. `A = Bᴳ`), the extension `A ⊆ B` is integral and `G` acts transitively on the primes of
`B` over a given prime of `A` (mathlib `RingTheory/Invariant/Basic`).  Every maximal ideal of
`B` lies over a maximal ideal of `A` by integrality (`Ideal.IsMaximal.under`), so when
`MaximalSpectrum A` is finite the maximal ideals of `B` form finitely many `G`-orbits; with
`G` finite, `MaximalSpectrum B` is finite.

This is the `Finite (MaximalSpectrum L)` input of the semilocal Weierstrass-chart
normalization (`ForMathlib/SemilocalUnitCocycleSplit.exists_units_eq_mul_of_span_eq_top`)
over the semilocalization `L` of the engine's mouth core (`Moduli/EngineDescent`, Stage 3a):
there `A = Lᴳ` is local (`Unique (MaximalSpectrum A)`), and `MaximalSpectrum L` is the single
finite `G`-orbit of primes over its closed point.
-/

open Pointwise

/-- **Finiteness of the maximal spectrum of an invariant extension.**  If a finite group `G`
acts on `B` with `Algebra.IsInvariant A B G` and `A` has finitely many maximal ideals, then so
does `B`: maximal ideals of `B` lie over maximal ideals of `A` (integrality), and the primes
over a fixed prime form one `G`-orbit. -/
theorem MaximalSpectrum.finite_of_isInvariant (A B G : Type*) [CommRing A] [CommRing B]
    [Algebra A B] [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G] [Finite (MaximalSpectrum A)] :
    Finite (MaximalSpectrum B) := by
  classical
  haveI hint : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B G
  have hfin : {I : Ideal B | I.IsMaximal}.Finite := by
    have hcover : {I : Ideal B | I.IsMaximal} ⊆
        ⋃ m : MaximalSpectrum A, {I : Ideal B | I.IsMaximal ∧ I.under A = m.1} := by
      intro I hI
      haveI : I.IsMaximal := hI
      exact Set.mem_iUnion.mpr ⟨⟨I.under A, Ideal.IsMaximal.under A I⟩, hI, rfl⟩
    refine Set.Finite.subset (Set.finite_iUnion fun m => ?_) hcover
    by_cases hne : ({I : Ideal B | I.IsMaximal ∧ I.under A = m.1}).Nonempty
    · obtain ⟨Q₀, hQ₀max, hQ₀under⟩ := hne
      haveI : Q₀.IsMaximal := hQ₀max
      have horb : {I : Ideal B | I.IsMaximal ∧ I.under A = m.1} ⊆
          Set.range fun g : G => g • Q₀ := by
        rintro I ⟨hImax, hIunder⟩
        haveI : I.IsMaximal := hImax
        obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A B G Q₀ I
          (hQ₀under.trans hIunder.symm)
        exact ⟨g, hg.symm⟩
      exact Set.Finite.subset (Set.finite_range _) horb
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      exact Set.finite_empty
  haveI := hfin.to_subtype
  exact Finite.of_injective
    (fun Q : MaximalSpectrum B => (⟨Q.1, Q.2⟩ : {I : Ideal B | I.IsMaximal}))
    fun Q Q' h => MaximalSpectrum.ext (congrArg Subtype.val h)
