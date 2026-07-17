/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Units from residue-field nonvanishing ([hArb-3], unit certificates)

A ring element is a unit iff it avoids every prime — in residue-field form, iff its
image in every `κ(𝔭)` is nonzero. This is point-checkable over ARBITRARY (in
particular non-reduced) rings, unlike equational identities; the `ℰ₃`-datum unit
certificates (`a₃`, `3`, the B-locus) are supplied fibrewise through it.
-/

namespace ModularCurves

/-- An element outside every prime ideal is a unit. -/
theorem isUnit_of_forall_notMem_prime {R : Type*} [CommRing R] {f : R}
    (h : ∀ 𝔭 : PrimeSpectrum R, f ∉ 𝔭.asIdeal) : IsUnit f := by
  by_contra hf
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal (Ideal.span {f})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  exact h ⟨𝔪, h𝔪.isPrime⟩ (hle (Ideal.mem_span_singleton_self f))

/-- An element with nonzero image in every prime residue field is a unit. -/
theorem isUnit_of_forall_algebraMap_residueField_ne_zero {R : Type*} [CommRing R]
    {f : R} (h : ∀ 𝔭 : PrimeSpectrum R,
      algebraMap R 𝔭.asIdeal.ResidueField f ≠ 0) : IsUnit f :=
  isUnit_of_forall_notMem_prime fun 𝔭 h𝔭 =>
    h 𝔭 (Ideal.algebraMap_residueField_eq_zero.mpr h𝔭)

end ModularCurves
