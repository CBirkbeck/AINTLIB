/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# A faithfully flat local extension with infinite residue field

Construction support for `[CHARTER-HOPF]` / `T-G3d-infra` Piece 3
(`.mathlib-quality/decomposition-hopf-crux.md`, leaf `[HG-A3]`; Stacks
`algebra-lemma-flat-local-given-residue-field`, tag 03C3, in the special form the
`[HG-B6]` bootstrap needs): every local ring `C` admits a **faithfully flat local**
`C`-algebra with **infinite residue field**, namely

`C[X]` localized at the prime `m·C[X]` (`m` the maximal ideal): its quotient is the domain
`(C/m)[X]` (`Ideal.polynomialQuotientEquivQuotientPolynomial`), flatness is
free-then-localization (`IsLocalization.flat` + `Module.Flat.trans`), the algebra map is
local because a constant polynomial lies in `m·C[X]` iff its coefficient lies in `m`
(`Polynomial.mem_map_C_iff`), faithful flatness follows
(`Module.FaithfullyFlat.of_flat_of_isLocalHom`), and the residue classes of the powers
`X^n` are pairwise distinct, so the residue field is infinite.

The 03BM proposition uses this at each localized invariant ring `C_𝔭`: base-changing the
translation groupoid along this extension preserves the co-invariants
(`Flat/Equalizer.lean`) and puts an infinite field under the semi-local basis-selection
lemma (`[HG-A4]`).
-/

open Polynomial IsLocalRing

universe u

namespace IsLocalRing

variable (C : Type u) [CommRing C] [IsLocalRing C]

/-- The extension `m·C[X]` of the maximal ideal to the polynomial ring — the prime at which
`C[X]` is localized to produce a flat local extension with infinite residue field. -/
noncomputable def polynomialMaximalIdeal : Ideal (Polynomial C) :=
  (maximalIdeal C).map (algebraMap C (Polynomial C))

/-- Membership in `m·C[X]` is coefficientwise membership in `m`. -/
theorem mem_polynomialMaximalIdeal {f : Polynomial C} :
    f ∈ polynomialMaximalIdeal C ↔ ∀ n, f.coeff n ∈ maximalIdeal C := by
  rw [polynomialMaximalIdeal, algebraMap_eq, Ideal.mem_map_C_iff]

/-- `m·C[X]` is prime: the quotient is the polynomial ring over the residue field. -/
instance polynomialMaximalIdeal_isPrime : (polynomialMaximalIdeal C).IsPrime := by
  rw [← Ideal.Quotient.isDomain_iff_prime]
  haveI : IsDomain (Polynomial (C ⧸ maximalIdeal C)) := inferInstance
  exact ((maximalIdeal C).polynomialQuotientEquivQuotientPolynomial).symm.isDomain

/-- The **flat local extension with infinite residue field** of a local ring `C`
(Stacks 03C3, concrete form): `C[X]` localized at `m·C[X]`. -/
noncomputable abbrev LocalPolynomialExtension : Type u :=
  Localization.AtPrime (polynomialMaximalIdeal C)

instance flat_localPolynomialExtension : Module.Flat C (LocalPolynomialExtension C) :=
  haveI : Module.Flat (Polynomial C) (LocalPolynomialExtension C) :=
    IsLocalization.flat _ (polynomialMaximalIdeal C).primeCompl
  Module.Flat.trans C (Polynomial C) (LocalPolynomialExtension C)

instance isLocalHom_localPolynomialExtension :
    IsLocalHom (algebraMap C (LocalPolynomialExtension C)) := by
  refine ⟨fun c hc => ?_⟩
  by_contra hcm
  have hCc : (Polynomial.C c : Polynomial C) ∈ polynomialMaximalIdeal C := by
    rw [mem_polynomialMaximalIdeal]
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simpa using (mem_maximalIdeal c).mpr hcm
    · simp [Polynomial.coeff_C, hn]
  have : IsUnit (algebraMap (Polynomial C) (LocalPolynomialExtension C) (Polynomial.C c)) := by
    rwa [show algebraMap (Polynomial C) (LocalPolynomialExtension C) (Polynomial.C c)
        = algebraMap C (LocalPolynomialExtension C) c from rfl]
  rw [IsLocalization.AtPrime.isUnit_to_map_iff (LocalPolynomialExtension C)
    (polynomialMaximalIdeal C)] at this
  exact this hCc

instance faithfullyFlat_localPolynomialExtension :
    Module.FaithfullyFlat C (LocalPolynomialExtension C) :=
  Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- The residue field of the local polynomial extension is infinite: the residue classes of
the powers `X^n` are pairwise distinct, because `X^n − X^m` has a coefficient equal to `1`,
which is not in the maximal ideal. -/
instance infinite_residueField_localPolynomialExtension :
    Infinite (ResidueField (LocalPolynomialExtension C)) := by
  refine Infinite.of_injective
    (fun n : ℕ => residue (LocalPolynomialExtension C)
      (algebraMap (Polynomial C) (LocalPolynomialExtension C) (X ^ n)))
    (fun n m hnm => ?_)
  by_contra hne
  have hmem : algebraMap (Polynomial C) (LocalPolynomialExtension C) (X ^ n - X ^ m)
      ∈ maximalIdeal (LocalPolynomialExtension C) := by
    rw [map_sub]
    exact Ideal.Quotient.eq.mp hnm
  rw [IsLocalization.AtPrime.to_map_mem_maximal_iff (LocalPolynomialExtension C)
    (polynomialMaximalIdeal C), mem_polynomialMaximalIdeal] at hmem
  have h1 : (X ^ n - X ^ m : Polynomial C).coeff n = 1 := by
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_X_pow,
      if_pos rfl, if_neg hne, sub_zero]
  exact (maximalIdeal.isMaximal C).ne_top
    ((Ideal.eq_top_iff_one _).mpr (h1 ▸ hmem n))

end IsLocalRing
