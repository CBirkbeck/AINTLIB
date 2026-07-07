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

## IMPORTANT — the unit-ideal disjunct (why both conclusions carry `∨ … = ⊤`)

With mathlib's `RingTheory.Sequence.IsRegular` a regular sequence `rs` on the ring `S` must satisfy
`top_ne_smul`, i.e. `S/(rs) ≠ 0`, equivalently `Ideal.ofList rs ≠ ⊤`.  Hence `Ideal.gradeGE`
measures grade with the mathlib convention `grade(⊤) = depth(S)` (NOT the Stacks convention
`grade(I, M) = ∞` when `IM = M`).  The two conventions disagree *exactly* on the unit ideal, and
this makes the naïve "grade survives localisation" / "grade locus is open" statements **false**:

* Counterexample (both naïve forms).  `S = k[x]` (Noetherian), `I = (x)`, `k = 1`.  Then
  `I.gradeGE 1` holds (`rs = [x]`).  Localising at `T = S \ {0}` gives the field `k(x)`, where
  `I.map = ⊤` (as `x` is a unit) and `(⊤ : Ideal k(x)).gradeGE 1` is **false** (a field has no
  length-`1` regular sequence).  So `I.gradeGE k ⟹ (I.map …).gradeGE k` fails.  For openness the
  same `I`, `k` give locus `= Spec S \ {(0)}` (grade drops only at the generic point, where the
  ideal becomes `⊤` over the fraction field), which is **not open** (`{(0)}` is not closed).

The mathematically correct — and Stacks-faithful — statements carry the unit-ideal escape
`∨ (I.map …) = ⊤`; this is exactly the disjunction "`(I_i)_𝔮 = S_𝔮` **or** `(I_i)_𝔮` contains a
regular sequence of length `i`" that Stacks 10.129.2 / 00RB use, and precisely the shape already
consumed by `buchsbaumEisenbud_acyclic` in `ForMathlib.BuchsbaumEisenbud` (line ~138,
`… .gradeGE i ∨ … = ⊤`).  Under the Stacks `∞`-convention the disjunction *is* `grade ≥ k`; with
the mathlib `IsRegular` def it must be spelled out.  Both theorems below are proved in this
corrected form.  (Neither theorem was referenced anywhere outside this file, so the statements are
adjusted here rather than in a consumer.)

## Two handles for the openness (`isOpen_gradeGE_locus`)

* Native to Stacks 00RB — regular-sequence persistence under localisation / flat base change:
  `RingTheory.Sequence.IsWeaklyRegular.of_flat_of_isBaseChange` (= Stacks 10.129.2).
* Strategic alternative — `grade(I,S) ≥ k ⟺ Extⁱ_S(S/I,S) = 0 ∀ i < k` (Stacks 00LW/0AUJ), making
  `{𝔮 : grade_𝔮 ≥ k}` OPEN via `Module.support_eq_zeroLocus` (each `Extⁱ` is a finite module with
  CLOSED support).  We use the Ext-support route: the whole grade-or-unit locus is the complement
  of the finitely many closed supports `Supp Extⁱ_S(S/I, S)` (`i < k`), hence open.  The single
  large sub-development left as `sorry` is the Rees/00LW bridge that identifies that locus with the
  Ext-support complement (`gradeGE_or_top_locus_eq_iInter_compl_zeroLocus`); the openness scaffolding
  around it is proved.

See `projects/ModularCurves/.mathlib-quality/decomposition-buchsbaum-eisenbud.md` [T-GRADE].
-/
import Mathlib

noncomputable section

open RingTheory.Sequence PrimeSpectrum

/-- grade of `I` in `S` is `≥ k`: `I` contains an `S`-regular sequence of length `k` (Stacks
00LE/00LF). -/
def Ideal.gradeGE {S : Type*} [CommRing S] (I : Ideal S) (k : ℕ) : Prop :=
  ∃ rs : List S, rs.length = k ∧ RingTheory.Sequence.IsRegular S rs ∧ (∀ x ∈ rs, x ∈ I)

/-- [T-GRADE.loc] grade survives localisation, up to the unit-ideal escape.

If `I` contains an `S`-regular sequence of length `k`, then in `Localization T` either the extended
ideal `I.map (algebraMap …)` still contains a regular sequence of length `k` (its grade stays
`≥ k`) **or** it is the whole ring.  The mapped sequence is automatically *weakly* regular
(localisation is flat, `IsWeaklyRegular.of_isLocalization`); it stays *regular* unless it degenerates
to the unit ideal, in which case `I.map … = ⊤`.  The unit-ideal disjunct is unavoidable — see the
file header counterexample (`S = k[x]`, `I = (x)`, `T = S \ {0}`, giving the field `k(x)`). -/
theorem Ideal.gradeGE_localize {S : Type*} [CommRing S] [IsNoetherianRing S]
    (I : Ideal S) (T : Submonoid S) (k : ℕ) (h : I.gradeGE k) :
    (I.map (algebraMap S (Localization T))).gradeGE k ∨
      I.map (algebraMap S (Localization T)) = ⊤ := by
  classical
  obtain ⟨rs, hlen, hreg, hmem⟩ := h
  set L := Localization T with hL
  set φ : S →+* L := algebraMap S L with hφ
  -- The mapped list and the basic facts about it.
  have hmem' : ∀ x ∈ rs.map φ, x ∈ I.map φ := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact Ideal.mem_map_of_mem φ (hmem y hy)
  -- `ofList rs ≤ I`, hence `ofList (rs.map φ) = (ofList rs).map φ ≤ I.map φ`.
  have hsub : Ideal.ofList rs ≤ I := Ideal.span_le.mpr (fun r hr => hmem r hr)
  have hmaple : Ideal.ofList (rs.map φ) ≤ I.map φ := by
    rw [← Ideal.map_ofList]; exact Ideal.map_mono hsub
  -- Weak regularity survives localisation (flat base change).
  have hweak : IsWeaklyRegular L (rs.map φ) :=
    IsWeaklyRegular.of_isLocalization L T hreg.toIsWeaklyRegular
  by_cases hbot : Ideal.ofList (rs.map φ) = ⊤
  · -- The mapped sequence generates the unit ideal ⟹ `I.map φ = ⊤`.
    right
    exact top_le_iff.mp (hbot ▸ hmaple)
  · -- The mapped sequence stays regular ⟹ grade `≥ k`.
    left
    refine ⟨rs.map φ, by simpa using hlen, ?_, hmem'⟩
    -- Upgrade weak regularity to regularity using `ofList (rs.map φ) ≠ ⊤`.
    refine (isRegular_iff L (rs.map φ)).mpr ⟨hweak, ?_⟩
    have key : Ideal.ofList (rs.map φ) • (⊤ : Submodule L L) = Ideal.ofList (rs.map φ) := by
      rw [Ideal.smul_eq_mul, Ideal.mul_top]
    rw [key]
    exact (Ne.symm hbot)

/-- ISOLATED SUB-DEVELOPMENT (Rees / Stacks 00LW ideal form + Ext–localisation compatibility).

The grade-`≥ k`-or-unit locus of `I` is the complement of a finite union of Zariski-closed sets.
Morally the closed sets are the supports `Supp Extⁱ_S(S/I, S)` (`i < k`): by the ideal form of the
Rees/00LW characterisation `grade(I_𝔮, S_𝔮) ≥ k ⟺ Extⁱ_{S_𝔮}(S_𝔮/I_𝔮, S_𝔮) = 0 ∀ i < k`,
together with the localisation compatibility of `Ext` for finite modules over a Noetherian ring
(`Ext^i(S/I, S)_𝔮 ≅ Ext^i_{S_𝔮}(S_𝔮/I_𝔮, S_𝔮)`), and the fact that when `I ⊄ 𝔮` (i.e.
`I·S_𝔮 = S_𝔮`) the module `S/I` localises to `0` so all `Extⁱ` vanish — which is precisely the
unit-ideal disjunct.  Each `Extⁱ_S(S/I, S)` is a finite `S`-module (`S` Noetherian, `S/I` finite),
so its support `= zeroLocus (annihilator)` is closed (`Module.support_eq_zeroLocus`); we phrase the
family directly as the annihilator ideals `J i`.

This is the sole `sorry` in the file.  The openness of the complement (below) is proved from it. -/
theorem gradeGE_or_top_locus_eq_iInter_compl_zeroLocus {S : Type*} [CommRing S]
    [IsNoetherianRing S] (I : Ideal S) (k : ℕ) :
    ∃ J : Fin k → Ideal S,
      {q : PrimeSpectrum S |
          (I.map (algebraMap S (Localization q.asIdeal.primeCompl))).gradeGE k ∨
            I.map (algebraMap S (Localization q.asIdeal.primeCompl)) = ⊤}
        = ⋂ i, (zeroLocus (J i : Set S))ᶜ := by
  sorry

/-- [T-GRADE.open] Openness of the grade locus: `{𝔮 : grade(I_𝔮) ≥ k or I_𝔮 = ⊤}` is OPEN.  Via Ext
this is the complement of `⋃_{i<k} Supp Extⁱ_S(S/I,S)` (each closed by `Module.support_eq_zeroLocus`,
here as `zeroLocus` of the annihilator); it is the replacement for Stacks 10.129.2 inside the
fibre-exact openness argument (00RB).  The unit-ideal disjunct `∨ … = ⊤` is required (see the file
header counterexample: the pure grade-`≥ k` locus need not be open). -/
theorem isOpen_gradeGE_locus {S : Type*} [CommRing S] [IsNoetherianRing S] (I : Ideal S) (k : ℕ) :
    IsOpen {q : PrimeSpectrum S |
      (I.map (algebraMap S (Localization q.asIdeal.primeCompl))).gradeGE k ∨
        I.map (algebraMap S (Localization q.asIdeal.primeCompl)) = ⊤} := by
  obtain ⟨J, hJ⟩ := gradeGE_or_top_locus_eq_iInter_compl_zeroLocus I k
  rw [hJ]
  exact isOpen_iInter_of_finite fun i => (isClosed_zeroLocus _).isOpen_compl

end
