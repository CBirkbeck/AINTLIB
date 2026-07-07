/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.

# Grade / depth `≥ k` of an ideal, and its openness (Stacks 00LE/00LF/00LW) — [T-GRADE]

No packaged `grade`/`depth` invariant exists in mathlib (`RingTheory/Regular` has only
`IsRegular`/`IsWeaklyRegular`; `RingTheory/Regular/Depth.lean` is a deprecated stub).  This file
packages "`I` contains an `S`-regular sequence of length `k`" and proves the two facts the
Buchsbaum–Eisenbud openness argument (Stacks 00RB) needs: persistence under localisation, and
openness of the grade locus.

## Two handles for the openness (`isOpen_gradeGE_locus`)

* Native to Stacks 00RB — regular-sequence persistence under localisation / flat base change:
  `RingTheory.Sequence.IsWeaklyRegular.of_flat_of_isBaseChange` (= Stacks 10.129.2).
* Strategic alternative — `grade(I,S) ≥ k ⟺ Extⁱ_S(S/I,S) = 0 ∀ i < k` (Stacks 00LW/0AUJ), making
  `{𝔮 : grade_𝔮 ≥ k}` OPEN via `Module.support_eq_zeroLocus` (each `Extⁱ` is a finite module with
  CLOSED support).  Either route closes `isOpen_gradeGE_locus`.

See `projects/ModularCurves/.mathlib-quality/decomposition-buchsbaum-eisenbud.md` [T-GRADE].
-/
import Mathlib

noncomputable section

/-- grade of `I` in `S` is `≥ k`: `I` contains an `S`-regular sequence of length `k` (Stacks
00LE/00LF). -/
def Ideal.gradeGE {S : Type*} [CommRing S] (I : Ideal S) (k : ℕ) : Prop :=
  ∃ rs : List S, rs.length = k ∧ RingTheory.Sequence.IsRegular S rs ∧ (∀ x ∈ rs, x ∈ I)

/-- [T-GRADE.loc] grade survives localisation (fed into 00RB's spreading; the mathlib engine is
`IsWeaklyRegular.of_flat_of_isBaseChange` / `.of_isLocalization`). -/
theorem Ideal.gradeGE_localize {S : Type*} [CommRing S] [IsNoetherianRing S]
    (I : Ideal S) (T : Submonoid S) (k : ℕ) (h : I.gradeGE k) :
    (I.map (algebraMap S (Localization T))).gradeGE k := by
  sorry

/-- [T-GRADE.open] Openness of the grade locus: `{𝔮 : grade(I_𝔮) ≥ k}` is OPEN.  Via Ext this is the
complement of `⋃_{i<k} Supp Extⁱ_S(S/I,S)` (each closed by `Module.support_eq_zeroLocus`); it is the
replacement for Stacks 10.129.2 inside the fibre-exact openness argument (00RB). -/
theorem isOpen_gradeGE_locus {S : Type*} [CommRing S] [IsNoetherianRing S] (I : Ideal S) (k : ℕ) :
    IsOpen {q : PrimeSpectrum S |
      (I.map (algebraMap S (Localization q.asIdeal.primeCompl))).gradeGE k} := by
  sorry

end
