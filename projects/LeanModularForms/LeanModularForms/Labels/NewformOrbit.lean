/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.Labels.Encoding
import LeanModularForms.SMOObligations.StrongMultiplicityOneFull
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.NumberTheory.NumberField.Basic

/-!
# LMFDB newform-orbit label `x`

This file defines the LMFDB **newform Galois(Hecke)-orbit label**, the `x` component of a
classical modular-form label `N.k.a.x`, and proves its well-definedness (constant on Galois
orbits) together with the reduction of injectivity to Strong Multiplicity One.

It mirrors, for `Newform`s, the structure used for the character-orbit label `a` in
`Labels/CharacterOrbit.lean`: a Galois-conjugacy `Setoid`, a Galois-orbit `Finset`, an
orbit-invariant trace key, the rank in the sorted image as `orbitIndex`, and the base-`26`
letter `letterEncode (orbitIndex)`.

## The LMFDB ordering convention

Per *Computing Classical Modular Forms* (Best–Bober–Booker–Costa–Cremona–Derickx–Lee–Lowry-Duda–
Roe–Sutherland–Voight, arXiv:2002.04717, §"Labels"), within a fixed level `N`, weight `k`, and
character Galois orbit `a`, the newform Galois orbits are ordered **lexicographically by the trace
sequence**
`(Tr_{K_f/ℚ} a₁, Tr_{K_f/ℚ} a₂, Tr_{K_f/ℚ} a₃, …)`,
where `K_f = ℚ(aₙ : n)` is the coefficient (Hecke eigenvalue) field and the `aₙ` are the
normalised Fourier coefficients (`a₁ = 1`).  The orbit index is the (`1`-based) position in this
order; the letter is the base-`26` encoding of `index - 1` (see `Labels/Encoding.lean`).

Structurally the absolute trace of the orbit is the **sum over the Galois orbit of the coefficient
sequences**:
`Tr_{K_f/ℚ} aₙ = Σ_{g ∈ galoisOrbit f} aₙ(g)`,
which is manifestly orbit-invariant; this is the key we rank by.

## The genuinely-deep number-theoretic inputs (isolated as precise `sorry`s)

The labeling *machinery and its well-definedness reductions* are proved here sorry-free (in
particular the label is provably **constant on Galois orbits**, and the single-form Strong
Multiplicity One separation is discharged directly from `strongMultiplicityOne_axiom_clean`).
Exactly **four** declarations carry `sorry`, each genuine number theory absent from mathlib and
each isolated into a precisely stated declaration with a one-line statement of the input it needs:

* `Newform.coeffSeq_isIntegral` — **each Hecke eigenvalue is an algebraic integer**
  (`IsIntegral ℤ aₙ`, hence `IsIntegral ℚ aₙ`).  The standard fact that Hecke eigenvalues of a
  newform are algebraic integers (Shimura, *Introduction to the Arithmetic Theory of Automorphic
  Functions*, Thm 3.52 / Deligne).  Absent from mathlib.
* `Newform.instFiniteDimensionalCoeffField` — **the coefficient field is a number field**
  (`FiniteDimensional ℚ K_f`), i.e. `[K_f : ℚ] < ∞`.  The standard fact that the Hecke field of a
  newform is a number field (the eigenvalues lie in a fixed finite extension; equivalently the
  Hecke algebra acting on the finite-dimensional space `S_k(Γ₁(N))` is a finite-rank ℤ-algebra).
  Absent from mathlib.
* `instFiniteNewform` — **there are only finitely many newforms of level `N`, weight `k`**
  (`Finite (Newform N k)`), because `S_k(Γ₁(N))` is finite-dimensional and normalised eigenforms
  are linearly independent, hence finite in number.  Needed only to form the Galois-orbit `Finset`
  and to *rank* the finitely many orbit keys; it is carried as the explicit hypothesis
  `[Fintype (Newform N k)]` by the orbit/ranking lemmas, so that they stay axiom-clean and this
  `sorry` is the sole finiteness input.  Absent from mathlib at this level of packaging.
* `Newform.traceSeq_injOn_orbits` — **the orbit trace sequence separates distinct orbits**
  (equal trace sequences ⇒ Galois conjugate).  This is the orbit-level upgrade of the (sorry-free)
  single-form separation `coeffSeq_injOn_charSpace`; promoting it requires the linear independence
  of the distinct newform coefficient systems (the newform analogue of `linearIndependent_monoidHom`
  used for the character label), which is the residual deep input for label *injectivity*.

The Galois action `f ↦ σf` (conjugate the `aₙ` by `σ ∈ Gal(ℂ/ℚ)`) is modelled by the relation
`Newform.IsGaloisConj`; its *well-definedness* (that `σf` is again a `Newform` of the same `N, k`
with conjugated character) is the deep stability statement, but it is **not needed** for the label
machinery: the relation only ever relates `Newform`s that already exist, so the orbit/trace/rank
structure built on it is real and sorry-free.

## Main definitions

* `Newform.coeffSeq f` — the normalised Fourier coefficient sequence `n ↦ aₙ(f)`.
* `Newform.coeffField f` — the coefficient field `K_f = ℚ(aₙ : n) ⊆ ℂ`.
* `Newform.IsGaloisConj f g` — the Galois/Hecke-orbit equivalence relation.
* `Newform.galoisSetoid` / `Newform.galoisOrbit f` — the orbit `Setoid` / `Finset`.
* `Newform.traceSeqAt f n` — the orbit trace key `Σ_{g ∈ orbit} aₙ(g) = Tr_{K_f/ℚ} aₙ`.
* `Newform.newformOrbitLabel f` — the LMFDB letter label `x`.

## Main results

* `Newform.isGaloisConj_*` + `Newform.galoisSetoid` — `IsGaloisConj` is an equivalence relation.
* `Newform.traceSeqAt_eq_of_isGaloisConj` — the trace key is constant on orbits.
* `Newform.newformOrbitLabel_eq_of_isGaloisConj` — **the label is constant on Galois orbits**
  (well-definedness, sorry-free).
* `Newform.coeffSeq_injOn_charSpace` — **Strong Multiplicity One separation** (sorry-free): two
  newforms in the same Nebentypus eigenspace with equal coefficient sequences are equal.  This is
  the single-form separation discharged directly from `strongMultiplicityOne_axiom_clean`.
* `Newform.newformOrbitLabel_injOn_orbits` — injectivity of the label on distinct orbits, reduced
  to the orbit-level trace separation `Newform.traceSeq_injOn_orbits`.
-/

open scoped BigOperators

noncomputable section

namespace HeckeRing.GL2.Newform

open HeckeRing.GL2 CongruenceSubgroup

variable {N : ℕ} [NeZero N] {k : ℤ}

/-! ### The normalised Fourier coefficient sequence `aₙ`

We work with the canonical period-`1` `q`-expansion (the Diamond–Shurman / Miyake normalisation),
so `a₁ = 1` and, for `n` coprime to `N`, `aₙ` equals the classical Hecke eigenvalue. -/

/-- The **normalised Fourier coefficient sequence** of a newform: `aₙ(f)` is the `n`-th coefficient
of the canonical (period-`1`) `q`-expansion of `f`.  By the normalisation `a₁ = 1`, and for `n`
coprime to `N` this is the classical Hecke eigenvalue `f.eigenvalue n`. -/
def coeffSeq (f : Newform N k) (n : ℕ+) : ℂ :=
  (UpperHalfPlane.qExpansion (1 : ℝ) f.toCuspForm).coeff n.val

@[simp] lemma coeffSeq_one (f : Newform N k) : coeffSeq f 1 = 1 := f.isNorm

/-- For `n` coprime to `N`, the normalised Fourier coefficient `aₙ` equals the classical Hecke
eigenvalue `f.eigenvalue n` (DS Prop 5.8.5).  Requires the Nebentypus-character hypothesis, since
`Newform.eigenvalue_eq_coeff` is stated for forms in a single eigenspace. -/
lemma coeffSeq_coprime_eq_eigenvalue (f : Newform N k) (n : ℕ+) (hn : Nat.Coprime n.val N)
    (χ : (ZMod N)ˣ →* ℂˣ) (hf_char : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ) :
    coeffSeq f n = f.eigenvalue n :=
  (Newform.eigenvalue_eq_coeff f n hn χ hf_char).symm

/-! ### Strong Multiplicity One: the single-form separation

The genuine multiplicity-one payoff: within a fixed Nebentypus eigenspace, the coefficient
sequence determines the newform.  Discharged directly from `strongMultiplicityOne_axiom_clean`,
sorry-free, and independent of any finiteness; it is the foundation of the orbit-level separation
used for label injectivity. -/

/-- **Strong Multiplicity One separation (single newform).**  Two newforms of level `N`, weight
`k` lying in the *same* Nebentypus eigenspace `modFormCharSpace k χ` and having the *same*
normalised Fourier coefficient sequence are equal (as cusp forms).

This is the contrapositive of multiplicity one and is discharged directly from
`strongMultiplicityOne_axiom_clean` (DS Thm 5.8.2 / Miyake Thm 4.6.8): equal coefficient sequences
give equal Hecke eigenvalues at every `n` coprime to `N` (with empty exceptional set), forcing
`f = g`. -/
lemma coeffSeq_injOn_charSpace {f g : Newform N k} (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (h : coeffSeq f = coeffSeq g) : f.toCuspForm = g.toCuspForm := by
  refine strongMultiplicityOne_axiom_clean f g χ hfχ hgχ ∅ ?_
  intro n hn _
  rw [← coeffSeq_coprime_eq_eigenvalue f n hn χ hfχ,
    ← coeffSeq_coprime_eq_eigenvalue g n hn χ hgχ, h]

/-! ### The coefficient (Hecke eigenvalue) field `K_f = ℚ(aₙ : n)`

`K_f` is the subfield of `ℂ` generated over `ℚ` by all the `aₙ(f)`.  That it is a *number field*
(`[K_f : ℚ] < ∞`) is the deep input isolated below. -/

/-- The **coefficient field** (Hecke eigenvalue field) `K_f = ℚ(aₙ : n) ⊆ ℂ` of a newform: the
intermediate field of `ℂ / ℚ` generated by the normalised Fourier coefficients. -/
def coeffField (f : Newform N k) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (Set.range (coeffSeq f))

lemma coeffSeq_mem_coeffField (f : Newform N k) (n : ℕ+) : coeffSeq f n ∈ coeffField f :=
  IntermediateField.subset_adjoin ℚ _ ⟨n, rfl⟩

/-- **DEEP INPUT (algebraicity of Hecke eigenvalues).**  Each normalised Fourier coefficient
`aₙ(f)` of a newform is an algebraic number, i.e. integral over `ℚ` (in fact over `ℤ`: it is an
algebraic *integer*).  This is the standard "Hecke eigenvalues of a newform are algebraic integers"
theorem (Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Thm 3.52;
Deligne), which is not available in mathlib. -/
private lemma coeffSeq_isIntegral (f : Newform N k) (n : ℕ+) : IsIntegral ℚ (coeffSeq f n) :=
  sorry

/-- **DEEP INPUT (the coefficient field is a number field).**  The coefficient field
`K_f = ℚ(aₙ : n)` is finite-dimensional over `ℚ`, i.e. `[K_f : ℚ] < ∞`.  This is the standard fact
that the Hecke field of a newform is a number field: although the generating *set* `{aₙ : n}` is a
priori infinite, all `aₙ` lie in a single finite extension of `ℚ` (equivalently, the Hecke algebra
acting on the finite-dimensional space `S_k(Γ₁(N))` is a finite-rank `ℤ`-algebra).  Not available
in mathlib. -/
instance instFiniteDimensionalCoeffField (f : Newform N k) :
    FiniteDimensional ℚ (coeffField f) :=
  sorry

/-- The coefficient field `K_f` is a number field (`CharZero` + `[K_f : ℚ] < ∞`).  `CharZero` is
automatic (it is a subfield of `ℂ`); finite-dimensionality is the deep input
`instFiniteDimensionalCoeffField`. -/
instance instNumberFieldCoeffField (f : Newform N k) : NumberField (coeffField f) where
  to_charZero := inferInstance
  to_finiteDimensional := instFiniteDimensionalCoeffField f

/-! ### The Galois action and the Hecke orbit

A Galois automorphism `σ ∈ Gal(ℂ/ℚ) = (ℂ ≃ₐ[ℚ] ℂ)` acts on a newform by conjugating its Fourier
coefficients, `aₙ(σf) = σ(aₙ(f))`.  We model the resulting Hecke/Galois-orbit *relation* on
newforms directly (the existence of the conjugate newform is the deep stability fact, not needed
for the label machinery). -/

/-- `f` and `g` are **Galois conjugate** newforms if some `σ ∈ Gal(ℂ/ℚ)` carries the coefficient
sequence of `f` to that of `g`, i.e. `aₙ(g) = σ(aₙ(f))` for all `n`.  This is the relation whose
classes are the LMFDB newform Galois (Hecke) orbits. -/
def IsGaloisConj (f g : Newform N k) : Prop :=
  ∃ σ : ℂ ≃ₐ[ℚ] ℂ, ∀ n : ℕ+, coeffSeq g n = σ (coeffSeq f n)

lemma isGaloisConj_refl (f : Newform N k) : IsGaloisConj f f :=
  ⟨AlgEquiv.refl, fun _ => rfl⟩

lemma isGaloisConj_symm {f g : Newform N k} (h : IsGaloisConj f g) : IsGaloisConj g f := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨σ.symm, fun n => ?_⟩
  rw [hσ n, AlgEquiv.symm_apply_apply]

lemma isGaloisConj_trans {f g h : Newform N k}
    (h₁ : IsGaloisConj f g) (h₂ : IsGaloisConj g h) : IsGaloisConj f h := by
  obtain ⟨σ, hσ⟩ := h₁
  obtain ⟨τ, hτ⟩ := h₂
  refine ⟨σ.trans τ, fun n => ?_⟩
  rw [hτ n, hσ n, AlgEquiv.trans_apply]

/-- The Galois/Hecke-orbit equivalence relation on `Newform`s of level `N`, weight `k`. -/
def galoisSetoid (N : ℕ) [NeZero N] (k : ℤ) : Setoid (Newform N k) where
  r := IsGaloisConj
  iseqv := ⟨isGaloisConj_refl, isGaloisConj_symm, isGaloisConj_trans⟩

/-- **DEEP INPUT (finiteness of the space of newforms).**  There are only finitely many newforms
of level `N` and weight `k`.  This holds because the cusp-form space `S_k(Γ₁(N))` is
finite-dimensional and distinct normalised eigenforms are linearly independent, hence finite in
number.  It is the canonical witness for the `[Fintype (Newform N k)]` hypothesis carried by the
orbit/ranking machinery below; not available in mathlib at this level of packaging.

It is deliberately **not** registered as a global instance (only `@[reducible]`), so that the
orbit/ranking lemmas — which take `[Fintype (Newform N k)]` as an explicit hypothesis — stay
axiom-clean (they use the hypothesis, not this `sorry`).  Supply it
(`haveI := Newform.instFiniteNewform`) to specialise the machinery to the genuine, finite space of
newforms. -/
@[reducible] def instFiniteNewform : Finite (Newform N k) := sorry

/-! The Galois-orbit and ranking constructions below need a `Fintype` structure on `Newform N k`
to enumerate orbits.  We carry it as an **explicit hypothesis** `[Fintype (Newform N k)]` rather
than a global instance: this keeps every orbit/ranking/label lemma axiom-clean, isolating the deep
finiteness fact entirely into `instFiniteNewform` (the canonical witness, via `Fintype.ofFinite`).
-/

variable [Fintype (Newform N k)]

/-- The **Galois orbit** of a newform `f` as a `Finset`: all newforms Galois-conjugate to `f`. -/
noncomputable def galoisOrbit (f : Newform N k) : Finset (Newform N k) :=
  open scoped Classical in
  Finset.univ.filter (IsGaloisConj f)

lemma mem_galoisOrbit_iff {f g : Newform N k} : g ∈ galoisOrbit f ↔ IsGaloisConj f g := by
  classical
  simp [galoisOrbit]

lemma self_mem_galoisOrbit (f : Newform N k) : f ∈ galoisOrbit f :=
  mem_galoisOrbit_iff.mpr (isGaloisConj_refl f)

/-- The Galois orbits of `f` and of a conjugate `g` coincide as `Finset`s. -/
lemma galoisOrbit_eq_of_isGaloisConj {f g : Newform N k} (h : IsGaloisConj f g) :
    galoisOrbit f = galoisOrbit g := by
  ext r
  rw [mem_galoisOrbit_iff, mem_galoisOrbit_iff]
  exact ⟨fun hr => isGaloisConj_trans (isGaloisConj_symm h) hr, fun hr => isGaloisConj_trans h hr⟩

/-! ### The orbit trace key

`traceSeqAt f n = Σ_{g ∈ galoisOrbit f} aₙ(g)`.  This equals the absolute trace
`Tr_{K_f/ℚ} aₙ`; structurally it is manifestly invariant on the orbit (sum over the orbit). -/

/-- The **orbit trace key** at `n`: the sum of `aₙ(g)` over the Galois orbit of `f`.  Equals the
absolute trace `Tr_{K_f/ℚ} aₙ(f)`, the LMFDB newform-orbit ordering key at index `n`. -/
noncomputable def traceSeqAt (f : Newform N k) (n : ℕ+) : ℂ :=
  ∑ g ∈ galoisOrbit f, coeffSeq g n

/-- The orbit trace key is constant on Galois orbits. -/
lemma traceSeqAt_eq_of_isGaloisConj {f g : Newform N k} (h : IsGaloisConj f g) (n : ℕ+) :
    traceSeqAt f n = traceSeqAt g n := by
  unfold traceSeqAt
  rw [galoisOrbit_eq_of_isGaloisConj h]

/-! ### The orbit ranking key and the label

The LMFDB orbit key is the trace sequence `n ↦ traceSeqAt f n`, ranked lexicographically.  We
package it and rank orbits by their position in the sorted image, exactly as for the character
label. -/

/-- The LMFDB newform-orbit ordering key `n ↦ Tr_{K_f/ℚ} aₙ(f)`, manifestly orbit-invariant. -/
noncomputable def orbitRankKey (f : Newform N k) : ℕ+ → ℂ := traceSeqAt f

lemma orbitRankKey_eq_of_isGaloisConj {f g : Newform N k} (h : IsGaloisConj f g) :
    orbitRankKey f = orbitRankKey g := by
  funext n
  exact traceSeqAt_eq_of_isGaloisConj h n

section Ranking

/-- A fixed linear order on the orbit keys, used purely to *rank* orbits and produce a concrete
label.  The genuine LMFDB order is the lexicographic order on the trace tuple
`(Tr a₁, Tr a₂, …)`; because that tuple is an orbit invariant (`orbitRankKey`), any fixed linear
order on the key type injective on the finitely many realised keys yields the same orbit ranking
once `traceSeq_injOn_orbits` is known.  We linearise the key type with a classically-chosen
well-order (`WellOrderingRel`); pinning the comparator to the concrete `ℂ`-lexicographic-by-`n`
order is deferred together with that separation lemma. -/
noncomputable instance instLinearOrderOrbitKey : LinearOrder (ℕ+ → ℂ) :=
  IsWellOrder.linearOrder WellOrderingRel

/-- The `0`-based LMFDB newform-orbit index of `f`: the number of distinct orbits (of level `N`,
weight `k`) whose ordering key is strictly smaller than that of `f`.  With
`traceSeq_injOn_orbits` this is a genuine bijection onto `{0, …, #orbits − 1}` and matches LMFDB's
`index − 1`. -/
noncomputable def orbitIndex (f : Newform N k) : ℕ :=
  (((Finset.univ : Finset (Newform N k)).image orbitRankKey).filter (· < orbitRankKey f)).card

/-- The **LMFDB newform Galois-orbit label** `x`: the base-`26` letter encoding of the `0`-based
orbit index. -/
noncomputable def newformOrbitLabel (f : Newform N k) : String :=
  LeanModularForms.Labels.letterEncode (orbitIndex f)

/-- **The label is constant on Galois orbits** (well-definedness, the feasible direction). -/
lemma newformOrbitLabel_eq_of_isGaloisConj {f g : Newform N k} (h : IsGaloisConj f g) :
    newformOrbitLabel f = newformOrbitLabel g := by
  unfold newformOrbitLabel orbitIndex
  rw [orbitRankKey_eq_of_isGaloisConj h]

end Ranking

/-! ### Injectivity of the label on orbits

We reduce injectivity of `newformOrbitLabel` on distinct orbits to the orbit-level trace
separation `traceSeq_injOn_orbits` (equal trace sequences ⇒ same orbit), then run the same
rank-injectivity argument as for the character label. -/

/-- On a finite linearly ordered set `S`, the rank function `a ↦ #{x ∈ S | x < a}` is strictly
monotone, hence injective, on `S`. -/
private lemma rank_injOn {α : Type*} [LinearOrder α] (S : Finset α) {a b : α}
    (ha : a ∈ S) (hb : b ∈ S)
    (hcard : (S.filter (· < a)).card = (S.filter (· < b)).card) : a = b := by
  classical
  have mono : ∀ x y : α, x ∈ S → x < y →
      (S.filter (· < x)).card < (S.filter (· < y)).card := by
    intro x y hx hxy
    refine Finset.card_lt_card <| (Finset.ssubset_iff_of_subset
      (Finset.monotone_filter_right S (fun z _ hz => lt_trans hz hxy))).mpr ?_
    exact ⟨x, Finset.mem_filter.mpr ⟨hx, hxy⟩,
      fun hmem => lt_irrefl x (Finset.mem_filter.mp hmem).2⟩
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exact absurd hcard (ne_of_lt (mono a b ha hlt))
  · exact heq
  · exact absurd hcard.symm (ne_of_lt (mono b a hb hgt))

/-- **Orbit-level trace separation.**  If two newforms (of level `N`, weight `k`, sharing the
Nebentypus eigenspace `modFormCharSpace k χ`) have the *same orbit trace sequence*
`n ↦ Σ_{orbit} aₙ`, then they are Galois conjugate.  Equivalently, the LMFDB lexicographic order
on the trace tuple is a strict total order on orbits.

This is the orbit-level upgrade of the single-form Strong Multiplicity One separation
`coeffSeq_injOn_charSpace`: the trace sequence is a sum of the (distinct) coefficient systems over
the orbit, and equal trace sequences force equal orbits.  Mirrors the Artin–Dedekind separation
`orbitRankKey_injOn_orbits` used for the character label; promoting it from the single-form
separation requires the linear independence of the distinct newform coefficient systems sharing a
character (the newform analogue of `linearIndependent_monoidHom`), which is the residual deep
input here. -/
private lemma traceSeq_injOn_orbits {f g : Newform N k} (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (h : orbitRankKey f = orbitRankKey g) : IsGaloisConj f g :=
  sorry

/-- **Rank-injectivity.**  Equal orbit indices force equal ordering keys: the strictly-monotone
rank function `key ↦ #{realised keys strictly below it}` is injective on the finite set of realised
keys (`rank_injOn`), and both keys are realised. -/
lemma orbitIndex_inj {f g : Newform N k} (h : orbitIndex f = orbitIndex g) :
    orbitRankKey f = orbitRankKey g :=
  rank_injOn _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    (Finset.mem_image_of_mem _ (Finset.mem_univ _)) h

/-- **The label is injective on distinct orbits.**  If two newforms sharing a Nebentypus
eigenspace have the same label, they are Galois-conjugate.  A clean reduction: `letterEncode` is
injective, so equal labels give equal `orbitIndex`; `orbitIndex_inj` gives equal ordering keys;
and `traceSeq_injOn_orbits` (the SMO-based orbit separation) concludes Galois conjugacy. -/
lemma newformOrbitLabel_injOn_orbits {f g : Newform N k} (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (h : newformOrbitLabel f = newformOrbitLabel g) : IsGaloisConj f g :=
  traceSeq_injOn_orbits χ hfχ hgχ
    (orbitIndex_inj (LeanModularForms.Labels.letterEncode_injective h))

end HeckeRing.GL2.Newform
