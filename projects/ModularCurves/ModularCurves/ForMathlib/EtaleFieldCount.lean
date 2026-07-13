/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import Mathlib.RingTheory.Etale.Field
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Point count of a finite étale algebra over a separably closed field

Over a separably closed field `K`, an essentially-finite-type formally-étale `K`-algebra `A`
splits as `A ≃ₐ[K] (PrimeSpectrum A → K)` (`Algebra.FormallyEtale.equivPiOfIsSepClosed`). Hence
its prime spectrum is finite with cardinality equal to its `K`-dimension — the algebraic core of
the "reduced-fibre point count" (KM 3.7.1) used in the Y(N) `[YF-⊆]` distinctness argument.
-/

open scoped Classical

namespace Algebra.FormallyEtale

variable (K A : Type*) [Field K] [CommRing A] [Algebra K A] [EssFiniteType K A]
  [Algebra.FormallyEtale K A] [IsSepClosed K]

/-- **The point count.** For an essentially-finite-type formally-étale algebra `A` over a
separably closed field `K`, the number of primes equals the `K`-dimension. -/
theorem natCard_primeSpectrum_eq_finrank :
    Nat.card (PrimeSpectrum A) = Module.finrank K A := by
  haveI := Algebra.FormallyUnramified.finite_of_free K A
  haveI : IsArtinianRing A := isArtinian_of_tower K inferInstance
  haveI : Fintype (PrimeSpectrum A) := Fintype.ofFinite _
  rw [(equivPiOfIsSepClosed K A).toLinearEquiv.finrank_eq, Module.finrank_pi,
    Nat.card_eq_fintype_card]

end Algebra.FormallyEtale
