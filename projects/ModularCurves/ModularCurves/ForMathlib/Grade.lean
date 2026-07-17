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
  of the finitely many closed supports `Supp Extⁱ_S(S/I, S)` (`i < k`), hence open.  The annihilator
  packaging (`gradeGE_or_top_locus_eq_iInter_compl_zeroLocus`, taking `J i := Ann_S Extⁱ_S(S/I, S)`
  and reducing via `Module.support_eq_zeroLocus` / `Module.notMem_support_iff`), the openness
  scaffolding (`isOpen_gradeGE_locus`), and the pointwise characterisation
  `gradeGE_or_top_iff_forall_subsingleton_localizedExt` are all proved in full.  That pointwise
  characterisation is assembled from two classical facts:
  * the **Rees / Stacks 00LW ideal-grade theorem** over the local ring `S_𝔮`
    (`gradeGE_or_top_iff_forall_subsingleton_ext_local`) — **proved here in full** by the classical
    Rees induction (`Ext⁰ ≅ Hom` boundary + the covariant long exact `Ext`-sequence dimension
    shift),
    and
  * the **`Ext`-localisation compatibility** `(Extⁱ_S(S/I,S))_𝔮 ≅ Extⁱ_{S_𝔮}(S_𝔮/I_𝔮, S_𝔮)`
    (`localizedModule_ext_subsingleton_iff`, in `ForMathlib.BaseChangeExt`, imported) — **proved in
    full**.  It is assembled from the localisation functor's `S`-linearity, the two object
    isomorphisms `(S)_𝔮 ≅ S_𝔮` and `(S/I)_𝔮 ≅ S_𝔮/I_𝔮`, transport of `Ext` along isomorphisms, and
    the *flat base change for `Ext`* core `isLocalizedModule_mapExt`
    (`(Extⁱ_S(X,Y))_𝔮 ≅ Extⁱ_{S_𝔮}(X_𝔮,Y_𝔮)` for finite `X` over Noetherian `S`) — proved by
    induction on `i`: the degree-`0` Hom base change
    (`Module.FinitePresentation.isLocalizedModule_mapExtendScalars`) and the derived-functor step
    via
    the five lemma on the localised contravariant `Ext` long exact sequence of a finite projective
    presentation (mirroring `Functor.mapExt_bijective_of_preservesProjectiveObjects`, with the exact
    projective-preserving `localizedModuleFunctor` and `IsLocalizedModule` in place of
    full-faithfulness).

Consequently the **entire grade/openness chain is fully proved and axiom-clean** (no `sorryAx`):
`#print axioms isOpen_gradeGE_locus` → `[propext, Classical.choice, Quot.sound]`.

See `projects/ModularCurves/.mathlib-quality/decomposition-buchsbaum-eisenbud.md` [T-GRADE].
-/
import Mathlib.RingTheory.Regular.ProjectiveDimension
import Mathlib.RingTheory.Depth.Rees
import Mathlib.RingTheory.Regular.Flat
import ModularCurves.ForMathlib.BaseChangeExt

noncomputable section

open RingTheory.Sequence PrimeSpectrum CategoryTheory Abelian

/-- grade of `I` in `S` is `≥ k`: `I` contains an `S`-regular sequence of length `k` (Stacks
00LE/00LF). -/
def Ideal.gradeGE {S : Type*} [CommRing S] (I : Ideal S) (k : ℕ) : Prop :=
  ∃ rs : List S, rs.length = k ∧ RingTheory.Sequence.IsRegular S rs ∧ (∀ x ∈ rs, x ∈ I)

/-- Grade-or-unit introduction rule for `Ideal.gradeGE`.  A **weakly** regular sequence `xs` all of
whose entries lie in `J` witnesses `J.gradeGE xs.length` — **unless** it degenerates to the unit
ideal, in which case `J = ⊤`.  (mathlib's `IsRegular` demands `L ⧸ (xs) ≠ 0`, i.e.
`Ideal.ofList xs ≠ ⊤`; that properness is exactly what upgrades weak regularity to regularity, and
its failure is the unit-ideal disjunct.)  This is the localisation-free core of the disjunction in
`Ideal.gradeGE_localize`. -/
lemma Ideal.gradeGE_length_or_eq_top_of_isWeaklyRegular {L : Type*} [CommRing L] {J : Ideal L}
    {xs : List L} (hw : IsWeaklyRegular L xs) (hmem : ∀ x ∈ xs, x ∈ J) :
    J.gradeGE xs.length ∨ J = ⊤ := by
  by_cases hbot : Ideal.ofList xs = ⊤
  · -- The sequence generates the unit ideal, so `J = ⊤` (it contains `ofList xs = ⊤`).
    exact Or.inr (top_le_iff.mp (hbot ▸ Ideal.span_le.mpr fun x hx => hmem x hx))
  · -- Properness upgrades weak regularity to regularity, giving a length-`xs.length` witness.
    refine Or.inl ⟨xs, rfl, (isRegular_iff L xs).mpr ⟨hw, ?_⟩, hmem⟩
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact Ne.symm hbot

/-- [T-GRADE.loc] grade survives localisation, up to the unit-ideal escape.

If `I` contains an `S`-regular sequence of length `k`, then in `Localization T` either the extended
ideal `I.map (algebraMap …)` still contains a regular sequence of length `k` (its grade stays
`≥ k`) **or** it is the whole ring.  The mapped sequence is automatically *weakly* regular
(localisation is flat, `IsWeaklyRegular.of_isLocalization`); it stays *regular* unless it
degenerates
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
  -- The mapped list lands in `I.map φ`.
  have hmem' : ∀ x ∈ rs.map φ, x ∈ I.map φ := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact Ideal.mem_map_of_mem φ (hmem y hy)
  -- Weak regularity survives localisation (flat base change).
  have hweak : IsWeaklyRegular L (rs.map φ) :=
    IsWeaklyRegular.of_isLocalization L T hreg.toIsWeaklyRegular
  -- Grade-or-unit is now exactly the localisation-free introduction rule.
  have hgrade := Ideal.gradeGE_length_or_eq_top_of_isWeaklyRegular hweak hmem'
  have hk : (rs.map φ).length = k := by simpa using hlen
  rwa [hk] at hgrade

/-!
## The Rees theorem over a local ring — the `∨ = ⊤` grade/Ext characterisation, proved in full

The pointwise residual splits into two classical facts (see the module header and the docstring of
`gradeGE_or_top_iff_forall_subsingleton_localizedExt`):

* **(B) Rees / Stacks 00LW (ideal-grade form)** over a LOCAL Noetherian ring — proved below in full
  as `gradeGE_or_top_iff_forall_subsingleton_ext_local`.  The proof is the classical Rees induction:
  the boundary `grade ≥ 1 ⟺ Hom(R/I, M) = 0` is `IsSMulRegular.subsingleton_linearMap_iff`
  (`Ext⁰ ≅ Hom`), and the dimension shift uses the covariant long exact `Ext`-sequence of the
  regular
  short exact sequence `0 → M →ˣ M → M/xM → 0` (`ModuleCat.smulShortComplex`,
  `Ext.covariant_sequence_exact₁/₂/₃`) together with the fact that `x ∈ ann(R/I)` acts as `0` on
  `Ext(R/I, M)`.
* **(A) `Ext`-localisation compatibility** — the single genuinely mathlib-absent classical fact,
  ISOLATED below as `localizedModule_ext_subsingleton_iff`.
-/

section ReesLocal

open scoped Pointwise

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

omit [IsNoetherianRing R] in
/-- If `x ∈ I` then multiplication by `x` on `R ⧸ I` is the zero endomorphism, hence `x` acts as `0`
on every `Ext`-group `Ext (R ⧸ I) M n`: postcomposing an `Ext`-class with `mk₀ (x • 𝟙 M)` — which is
the scalar action of `x` — gives `0`.  This is the key vanishing that collapses the Rees long exact
sequence into short exact pieces. -/
private lemma comp_mk₀_smul_id_eq_zero {I : Ideal R} {x : R} (hx : x ∈ I)
    (M : ModuleCat R) {n : ℕ} (α : Ext (ModuleCat.of R (R ⧸ I)) M n) :
    α.comp (Ext.mk₀ (x • 𝟙 M)) (add_zero n) = 0 := by
  have hxN : (x • 𝟙 (ModuleCat.of R (R ⧸ I))) = 0 := by
    have hxann : x ∈ Module.annihilator R (R ⧸ I) := by
      rw [Ideal.annihilator_quotient]; exact hx
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun y => ?_
    simpa using Module.mem_annihilator.mp hxann y
  rw [← Ext.smul_eq_comp_mk₀]
  have step : x • α
      = (Ext.mk₀ (x • 𝟙 (ModuleCat.of R (R ⧸ I)))).comp α (zero_add n) := by
    rw [Ext.mk₀_smul, Ext.smul_comp, Ext.mk₀_id_comp]
  rw [step, hxN, Ext.mk₀_zero, Ext.zero_comp]

omit [IsNoetherianRing R] in
/-- `Ext X M n` is subsingleton when `X` is a zero object (used for the unit-ideal disjunct, where
`R ⧸ ⊤` is the zero module). -/
private lemma subsingleton_ext_of_isZero_left (X M : ModuleCat R) (hX : Limits.IsZero X) (n : ℕ) :
    Subsingleton (Ext X M n) := by
  refine subsingleton_of_forall_eq 0 (fun α => ?_)
  have hid : 𝟙 X = 0 := hX.eq_zero_of_tgt _
  calc α = (Ext.mk₀ (𝟙 X)).comp α (zero_add n) := (Ext.mk₀_id_comp α).symm
    _ = (Ext.mk₀ (0 : X ⟶ X)).comp α (zero_add n) := by rw [hid]
    _ = 0 := by rw [Ext.mk₀_zero, Ext.zero_comp]

/-- The grade-`≥ 1` boundary of the Rees theorem: `I` contains an `M`-regular element iff
`Hom(R/I, M) = Ext⁰(R/I, M) = 0`.  This is `IsSMulRegular.subsingleton_linearMap_iff`
(`Hom(N, M) = 0 ⟺ ∃ M-regular in ann N`) with `ann (R/I) = I` and `Ext⁰ ≅ Hom`. -/
private lemma exists_isSMulRegular_iff_subsingleton_ext_zero {I : Ideal R}
    (M : ModuleCat R) [Module.Finite R M] :
    (∃ x ∈ I, IsSMulRegular M x) ↔ Subsingleton (Ext (ModuleCat.of R (R ⧸ I)) M 0) := by
  rw [Ext.homEquiv₀.subsingleton_congr, ModuleCat.homEquiv.subsingleton_congr,
    IsSMulRegular.subsingleton_linearMap_iff]
  simp only [ModuleCat.coe_of, Ideal.annihilator_quotient]

omit [IsNoetherianRing R] in
/-- The dimension shift of the Rees induction.  For an `M`-regular element `x ∈ I`, the covariant
long exact `Ext`-sequence of `0 → M →ˣ M → M/xM → 0` collapses (because `x` kills `Ext(R/I, M)`)
into short exact sequences `0 → Ext ⁿ(R/I, M) → Extⁿ(R/I, M/xM) → Extⁿ⁺¹(R/I, M) → 0`, whence the
middle term vanishes iff both ends do. -/
private lemma subsingleton_ext_quotSMulTop_iff {I : Ideal R} {x : R} (hx : x ∈ I)
    (M : ModuleCat R) (reg : IsSMulRegular M x) (n : ℕ) :
    Subsingleton (Ext (ModuleCat.of R (R ⧸ I)) (ModuleCat.of R (QuotSMulTop x M)) n) ↔
      Subsingleton (Ext (ModuleCat.of R (R ⧸ I)) M n) ∧
        Subsingleton (Ext (ModuleCat.of R (R ⧸ I)) M (n + 1)) := by
  set N := ModuleCat.of R (R ⧸ I) with hN
  have hSE : (M.smulShortComplex x).ShortExact := reg.smulShortComplex_shortExact
  constructor
  · intro hQ
    haveI hQ' : Subsingleton (Ext N (M.smulShortComplex x).X₃ n) := hQ
    refine ⟨subsingleton_of_forall_eq 0 (fun β => ?_), subsingleton_of_forall_eq 0 (fun γ => ?_)⟩
    · -- `g* : Ext N M n → Ext N (M/xM) n` is injective since `f* = 0`.
      have hg : β.comp (Ext.mk₀ (M.smulShortComplex x).g) (add_zero n) = 0 := Subsingleton.elim _ _
      obtain ⟨α, hα⟩ := Ext.covariant_sequence_exact₂ (X := N) (hS := hSE) (x₂ := β) (hx₂ := hg)
      rw [← hα]; exact comp_mk₀_smul_id_eq_zero hx M α
    · -- `δ : Ext N (M/xM) n → Ext N M (n+1)` is surjective since `f* = 0`.
      obtain ⟨δ, hδ⟩ := Ext.covariant_sequence_exact₁ (X := N) (hS := hSE) (x₁ := γ)
        (hx₁ := comp_mk₀_smul_id_eq_zero hx M γ) (hn₀ := rfl)
      rw [← hδ, Subsingleton.elim δ 0]
      exact Ext.zero_comp N n hSE.extClass (n + 1) rfl
  · rintro ⟨hMn, hMn1⟩
    haveI : Subsingleton (Ext N (M.smulShortComplex x).X₂ n) := hMn
    haveI : Subsingleton (Ext N (M.smulShortComplex x).X₁ (n + 1)) := hMn1
    refine subsingleton_of_forall_eq 0 (fun α => ?_)
    -- `ker δ = im g*`; `δ α = 0` (target subsingleton), so `α ∈ im g*` with preimage in `0`.
    have hδα : α.comp hSE.extClass (rfl : n + 1 = n + 1) = 0 := Subsingleton.elim _ _
    obtain ⟨β, hβ⟩ := Ext.covariant_sequence_exact₃ (X := N) (hS := hSE) (x₃ := α)
      (hn₁ := rfl) (hx₃ := hδα)
    rw [← hβ, Subsingleton.elim β 0]
    exact Ext.zero_comp N n (Ext.mk₀ (M.smulShortComplex x).g) n (add_zero n)

/-- **The Rees induction (core).** Over a Noetherian local ring `R` with `I ≤ 𝔪`, for every finite
nontrivial module `M`, `I` contains an `M`-regular sequence of length `k` iff `Extⁱ(R/I, M) = 0` for
all `i < k`.  Classical Rees (Stacks 0AUJ; Bruns–Herzog 1.2.10; Matsumura 16.7): induction on `k`,
the base is nontriviality, the boundary `k = 1` is `exists_isSMulRegular_iff_subsingleton_ext_zero`,
and the step is the dimension shift `subsingleton_ext_quotSMulTop_iff`. -/
lemma rees_core [IsLocalRing R] {I : Ideal R} (hI : I ≤ IsLocalRing.maximalIdeal R) :
    ∀ (k : ℕ) (M : ModuleCat R), Module.Finite R M → Nontrivial M →
      ((∃ rs : List R, rs.length = k ∧ IsRegular M rs ∧ ∀ x ∈ rs, x ∈ I) ↔
        ∀ i : Fin k, Subsingleton (Ext (ModuleCat.of R (R ⧸ I)) M i)) := by
  intro k
  induction k with
  | zero =>
    intro M _ hMnt
    refine ⟨fun _ i => i.elim0, fun _ => ⟨[], rfl, ⟨by simp, ?_⟩, by simp⟩⟩
    rw [Ideal.ofList_nil, Submodule.bot_smul]
    exact bot_lt_top.ne'
  | succ k ih =>
    intro M hMfin hMnt
    haveI := hMfin
    haveI := hMnt
    set N := ModuleCat.of R (R ⧸ I) with hN
    constructor
    · rintro ⟨rs, hlen, hreg, hmem⟩
      cases rs with
      | nil => simp at hlen
      | cons x rs' =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
        rw [isRegular_cons_iff] at hreg
        obtain ⟨hxreg, hrs'reg⟩ := hreg
        have hxI : x ∈ I := hmem x List.mem_cons_self
        have hmem' : ∀ y ∈ rs', y ∈ I := fun y hy => hmem y (List.mem_cons_of_mem x hy)
        have hExt0 : Subsingleton (Ext N M 0) :=
          (exists_isSMulRegular_iff_subsingleton_ext_zero M).mp ⟨x, hxI, hxreg⟩
        haveI hQnt : Nontrivial (QuotSMulTop x M) :=
          nontrivial_quotSMulTop_of_mem_maximalIdeal M (hI hxI)
        have hQvanish : ∀ i : Fin k,
            Subsingleton (Ext N (ModuleCat.of R (QuotSMulTop x M)) i) :=
          (ih (ModuleCat.of R (QuotSMulTop x M)) inferInstance hQnt).mp ⟨rs', hlen, hrs'reg, hmem'⟩
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using hExt0
        · have := (subsingleton_ext_quotSMulTop_iff hxI M hxreg (j : ℕ)).mp (hQvanish j)
          simpa [Fin.val_succ] using this.2
    · intro hvanish
      have hExt0 : Subsingleton (Ext N M 0) := by simpa using hvanish 0
      obtain ⟨x, hxI, hxreg⟩ :=
        (exists_isSMulRegular_iff_subsingleton_ext_zero M).mpr hExt0
      haveI hQnt : Nontrivial (QuotSMulTop x M) :=
        nontrivial_quotSMulTop_of_mem_maximalIdeal M (hI hxI)
      have hQvanish : ∀ j : Fin k,
          Subsingleton (Ext N (ModuleCat.of R (QuotSMulTop x M)) j) := fun j =>
        (subsingleton_ext_quotSMulTop_iff hxI M hxreg (j : ℕ)).mpr
          ⟨hvanish ⟨j, by omega⟩, by simpa [Fin.val_succ] using hvanish ⟨j + 1, by omega⟩⟩
      obtain ⟨rs', hlen', hrs'reg, hmem'⟩ :=
        (ih (ModuleCat.of R (QuotSMulTop x M)) inferInstance hQnt).mpr hQvanish
      refine ⟨x :: rs', by simp [hlen'], ?_, ?_⟩
      · rw [isRegular_cons_iff]; exact ⟨hxreg, hrs'reg⟩
      · intro y hy
        rw [List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact hxI
        · exact hmem' y hy

/-- **(B) The Rees theorem over a local ring**, in the `∨ = ⊤` unit-ideal form used by the openness
argument: over a Noetherian local ring `L`, the ideal `J` has grade `≥ k` OR is the unit ideal iff
every `Extⁱ(L/J, L)` (`i < k`) vanishes.  Assembled from `rees_core` (proper case, applied to the
ring `L` as a module over itself) and `subsingleton_ext_of_isZero_left` (the `J = ⊤` disjunct, where
`L/J` is the zero module). -/
private lemma gradeGE_or_top_iff_forall_subsingleton_ext_local
    {L : Type*} [CommRing L] [IsNoetherianRing L] [IsLocalRing L] (J : Ideal L) (k : ℕ) :
    (J.gradeGE k ∨ J = ⊤) ↔
      ∀ i : Fin k, Subsingleton (Ext (ModuleCat.of L (L ⧸ J)) (ModuleCat.of L L) i) := by
  by_cases hJ : J = ⊤
  · subst hJ
    refine ⟨fun _ i => subsingleton_ext_of_isZero_left _ _ ?_ _, fun _ => Or.inr rfl⟩
    exact ModuleCat.isZero_of_subsingleton _
  · have hJle : J ≤ IsLocalRing.maximalIdeal L := IsLocalRing.le_maximalIdeal hJ
    rw [or_iff_left hJ]
    exact rees_core hJle k (ModuleCat.of L L) inferInstance inferInstance

end ReesLocal

/- **(A) `Ext`-localisation compatibility** is proved *in full* in `ForMathlib.BaseChangeExt`
(imported above) as the theorem `localizedModule_ext_subsingleton_iff`: localising `Extⁱ_S(S/I, S)`
at a prime `𝔮` gives `Extⁱ_{S_𝔮}(S_𝔮/I_𝔮, S_𝔮)`, so the former is subsingleton (i.e. `= 0` after
localisation) iff the latter vanishes.  It is assembled from the localisation functor's
`S`-linearity,
the two object isomorphisms `(S)_𝔮 ≅ S_𝔮` and `(S/I)_𝔮 ≅ S_𝔮/I_𝔮`, transport of `Ext` along
isomorphisms, and the **flat base change for `Ext`** core `isLocalizedModule_mapExt`
(`Extⁱ_S(X, Y)_𝔮 ≅ Extⁱ_{S_𝔮}(X_𝔮, Y_𝔮)` for finite `X` over Noetherian `S`) — itself proved by
induction on `i` from the degree-`0` Hom base change
(`Module.FinitePresentation.isLocalizedModule_mapExtendScalars`) and the five-lemma dévissage on the
localised contravariant `Ext` long exact sequence of a finite projective presentation.  This closes
the last classical gap; the whole development is `sorry`-free and axiom-clean.  See
`BaseChangeExt.lean`
for the full development (References: Stacks 00DL / 0AUJ; Bruns–Herzog 1.2.9; Matsumura, p. 140). -/

/-- For a prime `𝔮`, the extended ideal `I·S_𝔮` has grade `≥ k` **or** is the unit ideal *iff* every
`Ext`-module `Extⁱ_S(S/I, S)` (`i < k`) vanishes after localising at `𝔮`.  This is the pointwise
form of the identity "grade-or-unit locus `=` complement of the Ext-supports"; the openness argument
(`isOpen_gradeGE_locus`) needs exactly this, and the topological/annihilator packaging around it
(`gradeGE_or_top_locus_eq_iInter_compl_zeroLocus`, below) is proved in full from it.

The proof composes the Rees theorem over the local ring `S_𝔮`
(`gradeGE_or_top_iff_forall_subsingleton_ext_local`, proved in full) with the `Ext`-localisation
compatibility `localizedModule_ext_subsingleton_iff` (from `ForMathlib.BaseChangeExt`, also proved
in
full — flat base change for `Ext`).  Both halves are complete, so this theorem is axiom-clean. -/
private theorem gradeGE_or_top_iff_forall_subsingleton_localizedExt {S : Type*} [CommRing S]
    [IsNoetherianRing S] (I : Ideal S) (k : ℕ) (q : PrimeSpectrum S) :
    ((I.map (algebraMap S (Localization q.asIdeal.primeCompl))).gradeGE k ∨
        I.map (algebraMap S (Localization q.asIdeal.primeCompl)) = ⊤)
      ↔ ∀ i : Fin k, Subsingleton (LocalizedModule q.asIdeal.primeCompl
          (Ext (ModuleCat.of S (S ⧸ I)) (ModuleCat.of S S) i)) := by
  rw [gradeGE_or_top_iff_forall_subsingleton_ext_local]
  refine forall_congr' fun i => ?_
  rw [localizedModule_ext_subsingleton_iff I q i]

/-- The grade-`≥ k`-or-unit locus of `I` is the complement of the finite family of Zariski-closed
supports `Supp Extⁱ_S(S/I, S)` (`i < k`), phrased directly through the annihilator ideals
`J i := Ann_S Extⁱ_S(S/I, S)`.  Each `Extⁱ_S(S/I, S)` is a finite `S`-module (`S` Noetherian, `S/I`
finite, `ModuleCat.finite_ext`), so `Supp = zeroLocus (annihilator)` (`Module.support_eq_zeroLocus`)
and `𝔮 ∉ Supp ⟺ Extⁱ_𝔮 = 0` (`Module.notMem_support_iff`); the pointwise grade/unit ⟺ Ext-vanishing
equivalence is the isolated residual `gradeGE_or_top_iff_forall_subsingleton_localizedExt` above.
The openness of the complement (`isOpen_gradeGE_locus`, below) is proved from this identity. -/
theorem gradeGE_or_top_locus_eq_iInter_compl_zeroLocus {S : Type*} [CommRing S]
    [IsNoetherianRing S] (I : Ideal S) (k : ℕ) :
    ∃ J : Fin k → Ideal S,
      {q : PrimeSpectrum S |
          (I.map (algebraMap S (Localization q.asIdeal.primeCompl))).gradeGE k ∨
            I.map (algebraMap S (Localization q.asIdeal.primeCompl)) = ⊤}
        = ⋂ i, (zeroLocus (J i : Set S))ᶜ := by
  classical
  refine ⟨fun i => Module.annihilator S (Ext (ModuleCat.of S (S ⧸ I)) (ModuleCat.of S S) i), ?_⟩
  ext q
  simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_compl_iff]
  rw [gradeGE_or_top_iff_forall_subsingleton_localizedExt I k q]
  refine forall_congr' fun i => ?_
  rw [← Module.support_eq_zeroLocus, Module.notMem_support_iff]

/-- [T-GRADE.open] Openness of the grade locus: `{𝔮 : grade(I_𝔮) ≥ k or I_𝔮 = ⊤}` is OPEN.  Via Ext
this is the complement of `⋃_{i<k} Supp Extⁱ_S(S/I,S)` (each closed by
`Module.support_eq_zeroLocus`,
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
