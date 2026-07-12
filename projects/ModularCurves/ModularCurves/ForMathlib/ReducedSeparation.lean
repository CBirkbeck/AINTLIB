/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate. Ticket T-D31.
-/
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Field-valued points separate elements of a reduced ring

In a reduced commutative ring, an element vanishing under every ring hom to a field is
zero (`IsReduced.eq_zero_of_forall_ringHom_field`), so two elements agreeing under every
ring hom to a field are equal (`IsReduced.eq_of_forall_ringHom_field`): the intersection
of the primes is the nilradical, and each prime is realised as the kernel of the map to
the fraction field of its quotient.

This is the reduce-to-geometric-points step of KM 1.9.2 ("in order that `P₁,…,P_N` form
a full set of sections … it suffices to check after base change to every residue
field"), applied there over `MvPolynomial (Fin n) R` — whose reducedness for reduced `R`
mathlib already has.

Note the family must range over homs into fields realising every *prime* (fraction
fields of quotient domains); maximal-residue fields alone would only detect the Jacobson
radical, which exceeds the nilradical in general.

Upstream candidate: mathlib has `nilpotent_iff_mem_prime` and the
`IsReduced (MvPolynomial σ R)` instance, but not this separation statement.
-/

universe u

variable {A : Type u} [CommRing A] [IsReduced A]

/-- In a reduced commutative ring, an element vanishing under every ring hom to a field
is zero. -/
theorem IsReduced.eq_zero_of_forall_ringHom_field (a : A)
    (h : ∀ (K : Type u) [Field K] (φ : A →+* K), φ a = 0) : a = 0 := by
  refine isNilpotent_iff_eq_zero.mp (nilpotent_iff_mem_prime.mpr fun J hJ => ?_)
  haveI := hJ
  have h0 := h (FractionRing (A ⧸ J))
    ((algebraMap (A ⧸ J) (FractionRing (A ⧸ J))).comp (Ideal.Quotient.mk J))
  rw [RingHom.comp_apply] at h0
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact IsFractionRing.injective (A ⧸ J) (FractionRing (A ⧸ J)) (by rw [h0, map_zero])

/-- In a reduced commutative ring, two elements agreeing under every ring hom to a field
are equal. -/
theorem IsReduced.eq_of_forall_ringHom_field {a b : A}
    (h : ∀ (K : Type u) [Field K] (φ : A →+* K), φ a = φ b) : a = b :=
  sub_eq_zero.mp <| IsReduced.eq_zero_of_forall_ringHom_field _ fun K _ φ => by
    rw [map_sub, sub_eq_zero]
    exact h K φ
