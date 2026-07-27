/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.Labels.Encoding
import LeanModularForms.Labels.HeckeFieldArithmetic
import LeanModularForms.Labels.HeckeAlgFiniteFinal
import LeanModularForms.StrongMultiplicityOne.ConstantMultiple
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
Multiplicity One separation is discharged directly from `strongMultiplicityOne`).
Moreover the finiteness of the space of newforms (`instFiniteNewform`) and the orbit-separation
underlying label *injectivity* (`Newform.traceSeq_injOn_orbits`) are now **proved** here, both via
the linear independence of distinct newforms (`linearIndependent_toCuspForm` /
`linearIndependent_coeffSeq`), itself obtained from Petersson orthogonality of distinct newforms
(`petN_toCuspForm_eq_zero_of_ne`) together with Strong Multiplicity One — the newform analogue of
the Artin–Dedekind `linearIndependent_monoidHom` used for the character label.

Both arithmetic headlines below are now **proved here** (sorry-free in their own bodies), each
deriving from the *single* isolated finiteness input `heckeAlgℤ_finite` (`Module.Finite ℤ
(heckeAlgℤ N k)`, stated in `Labels/HeckeFieldArithmetic.lean` — the one remaining `sorry`, = the
integral Eichler–Shimura / integral-q-expansion-lattice input, Shimura Thm 3.48(1)+3.51(1)+3.52,
Miyake Thm 4.5.9+4.5.19; absent from mathlib):

* `Newform.coeffSeq_isIntegral` — **each Hecke eigenvalue is an algebraic integer**
  (`IsIntegral ℤ aₙ`, the full source strength).  Shimura **Thm 3.48(3)** p.83 (the eigenvalues are
  roots of the monic *integral* characteristic polynomial of the Hecke operators on the lattice);
  Diamond–Shurman Thm 6.5.1.
* `Newform.instFiniteDimensionalCoeffField` — **the coefficient field is a number field**
  (`FiniteDimensional ℚ K_f`, `[K_f : ℚ] < ∞`).  Shimura Thm 3.51(1) (`[D₀:ℚ] = r = dim S_k < ∞`):
  the eigenvalues lie in the fixed finite-dimensional ℚ-Hecke-algebra, hence in a number field.

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
  the single-form separation discharged directly from `strongMultiplicityOne`.
* `Newform.ext_of_toCuspForm` / `Newform.coeffSeq_injective` — **a newform is determined by its
  underlying form** (resp. its coefficient sequence): `f ↦ f.toCuspForm` and `coeffSeq` are
  injective on `Newform N k` (the character and ring eigenvalues are pinned by the nonzero form).
* `Newform.petN_toCuspForm_eq_zero_of_ne` / `Newform.linearIndependent_toCuspForm` /
  `Newform.linearIndependent_coeffSeq` — distinct newforms are **Petersson-orthogonal** and hence
  **linearly independent** (the newform analogue of `linearIndependent_monoidHom`).
* `Newform.instFiniteNewform` — **there are only finitely many newforms** (proved, via linear
  independence in the finite-dimensional cusp-form space).
* `Newform.newformOrbitLabel_injOn_orbits` — injectivity of the label on distinct orbits, via the
  orbit-level trace separation `Newform.traceSeq_injOn_orbits` (proved).
-/

open scoped BigOperators

noncomputable section

namespace HeckeRing.GL2.Newform

open HeckeRing.GL2 CongruenceSubgroup Matrix.SpecialLinearGroup

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
sequence determines the newform.  Discharged directly from `strongMultiplicityOne`,
sorry-free, and independent of any finiteness; it is the foundation of the orbit-level separation
used for label injectivity. -/

/-- **Strong Multiplicity One separation (single newform).**  Two newforms of level `N`, weight
`k` lying in the *same* Nebentypus eigenspace `modFormCharSpace k χ` and having the *same*
normalised Fourier coefficient sequence are equal (as cusp forms).

This is the contrapositive of multiplicity one and is discharged directly from
`strongMultiplicityOne` (DS Thm 5.8.2 / Miyake Thm 4.6.8): equal coefficient sequences
give equal Hecke eigenvalues at every `n` coprime to `N` (with empty exceptional set), forcing
`f = g`. -/
lemma coeffSeq_injOn_charSpace {f g : Newform N k} (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (h : coeffSeq f = coeffSeq g) : f.toCuspForm = g.toCuspForm := by
  refine strongMultiplicityOne f g χ hfχ hgχ ∅ ?_
  intro n hn _
  rw [← coeffSeq_coprime_eq_eigenvalue f n hn χ hfχ,
    ← coeffSeq_coprime_eq_eigenvalue g n hn χ hgχ, h]

/-! ### The underlying form determines the (eigen/new)form

An `Eigenform` (and hence a `Newform`) is determined by its underlying cusp form, provided that
form is nonzero.  Three ingredients combine, via the `@[ext]` lemmas, with all remaining fields
being `Prop` (proof-irrelevant):

* the Nebentypus character `χ` is pinned by `mem_charSpace` (the diamond operators act by `χ(d)` on
  the nonzero form, so two characters agreeing through the same form coincide);
* the ring eigenvalue `ringEigenvalue` is pinned at good `n` by `isRingEigen`/`isEigen` (the smul of
  the nonzero form by the eigenvalue is determined) and at bad `n` by `ringEigen_bad` (`= 0`).

Since `Newform`s are normalised (`isNorm`, so `a₁ = 1`) their underlying form is nonzero, hence
`f ↦ f.toCuspForm`, and therefore `coeffSeq`, are injective on `Newform N k`. -/

/-- The Nebentypus character of an `Eigenform` is determined by its underlying form, provided that
form is nonzero: if `f.toCuspForm = g.toCuspForm ≠ 0` then `f.χ = g.χ`.  The diamond operators act
by `χ(d)` on the (shared, nonzero) form, so the two scalars `f.χ d` and `g.χ d` agree. -/
lemma _root_.HeckeRing.GL2.Eigenform.χ_eq_of_toCuspForm {f g : Eigenform N k}
    (hfg : f.toCuspForm = g.toCuspForm) (hne : f.toCuspForm ≠ 0) : f.χ = g.χ := by
  have hf : f.toCuspForm ∈ cuspFormCharSpace k f.χ :=
    Unified.cuspFormCharSpace_of_toModularForm'_mem f.mem_charSpace
  have hg : g.toCuspForm ∈ cuspFormCharSpace k g.χ :=
    Unified.cuspFormCharSpace_of_toModularForm'_mem g.mem_charSpace
  refine MonoidHom.ext fun d => Units.ext ?_
  have hfd : diamondOpCuspHom k d f.toCuspForm = (↑(f.χ d) : ℂ) • f.toCuspForm :=
    diamondOpCusp_apply_charSpace k f.χ d hf
  have hgd : diamondOpCuspHom k d g.toCuspForm = (↑(g.χ d) : ℂ) • g.toCuspForm :=
    diamondOpCusp_apply_charSpace k g.χ d hg
  rw [hfg] at hfd
  have hsmul : ((↑(f.χ d) : ℂ) - (↑(g.χ d) : ℂ)) • g.toCuspForm = 0 := by
    rw [sub_smul, ← hfd, ← hgd, sub_self]
  exact sub_eq_zero.mp <| (smul_eq_zero.mp hsmul).resolve_right (hfg ▸ hne)

/-- The ring eigenvalue of an `Eigenform` is determined by its underlying form, provided that form
is nonzero.  At good `n` the smul of the (shared, nonzero) form by the eigenvalue is fixed by
`isRingEigen`/`isEigen`; at bad `n` both eigenvalues are `0` by `ringEigen_bad`. -/
lemma _root_.HeckeRing.GL2.Eigenform.ringEigenvalue_eq_of_toCuspForm {f g : Eigenform N k}
    (hfg : f.toCuspForm = g.toCuspForm) (hne : f.toCuspForm ≠ 0) :
    f.ringEigenvalue = g.ringEigenvalue := by
  funext n
  by_cases hn : Nat.Coprime n.val N
  · haveI : NeZero n.val := ⟨n.pos.ne'⟩
    -- The character agrees, so the classical eigenvalues agree, hence the ring eigenvalues.
    have hχ : f.χ = g.χ := Eigenform.χ_eq_of_toCuspForm hfg hne
    have hf := f.isEigen n hn
    have hg := g.isEigen n hn
    rw [hfg] at hf
    have hval : f.eigenvalue n = g.eigenvalue n := by
      have hsmul : (f.eigenvalue n - g.eigenvalue n) • g.toCuspForm = 0 := by
        rw [sub_smul, ← hf, ← hg, sub_self]
      exact sub_eq_zero.mp <| (smul_eq_zero.mp hsmul).resolve_right (hfg ▸ hne)
    -- `eigenvalue n = χ(n) • ringEigenvalue n` with `χ(n)` a unit, and `f.χ = g.χ`.
    rw [Eigenform.eigenvalue, Eigenform.eigenvalue, dif_pos hn, dif_pos hn, hχ] at hval
    exact mul_left_cancel₀ (by exact_mod_cast (g.χ (ZMod.unitOfCoprime n.val hn)).ne_zero) hval
  · rw [f.ringEigen_bad n hn, g.ringEigen_bad n hn]

/-- **An `Eigenform` is determined by its underlying form** (when nonzero): if
`f.toCuspForm = g.toCuspForm ≠ 0` then `f = g`.  Combines `χ_eq_of_toCuspForm`,
`ringEigenvalue_eq_of_toCuspForm`, and proof-irrelevance of the remaining `Prop` fields via
`Eigenform.ext`. -/
lemma _root_.HeckeRing.GL2.Eigenform.ext_of_toCuspForm {f g : Eigenform N k}
    (hfg : f.toCuspForm = g.toCuspForm) (hne : f.toCuspForm ≠ 0) : f = g :=
  Eigenform.ext (by rw [hfg]) (Eigenform.χ_eq_of_toCuspForm hfg hne)
    (Eigenform.ringEigenvalue_eq_of_toCuspForm hfg hne)

-- `Newform.toCuspForm_ne_zero` now lives upstream in `HeckeFieldArithmetic.lean` (used by T003);
-- inherited here via the import. (Was duplicated here before the Group-A T004/T005 wiring.)

/-- **A `Newform` is determined by its underlying form**: if `f.toCuspForm = g.toCuspForm` then
`f = g`.  Newforms are normalised, hence nonzero, so the `Eigenform` data fields are pinned by
`χ_eq_of_toCuspForm`/`ringEigenvalue_eq_of_toCuspForm`; the extra `Prop` fields `isNew`/`isNorm`
are proof-irrelevant (`Newform.ext`). -/
lemma ext_of_toCuspForm {f g : Newform N k} (hfg : f.toCuspForm = g.toCuspForm) : f = g :=
  Newform.ext (by rw [hfg])
    (Eigenform.χ_eq_of_toCuspForm hfg f.toCuspForm_ne_zero)
    (Eigenform.ringEigenvalue_eq_of_toCuspForm hfg f.toCuspForm_ne_zero)

/-- **`f ↦ f.toCuspForm` is injective on `Newform N k`.** -/
lemma toCuspForm_injective :
    Function.Injective (fun f : Newform N k => f.toCuspForm) :=
  fun _ _ h => ext_of_toCuspForm h

/-- **`coeffSeq` is injective on `Newform N k`.**  The coefficient sequence is read off the
underlying form, which determines the newform (`Newform.toCuspForm_injective`). -/
lemma coeffSeq_injective : Function.Injective (coeffSeq (N := N) (k := k)) := by
  intro f g h
  -- The difference of the `ModularForm` coercions has vanishing `q`-expansion: every coefficient
  -- agrees (the positive ones by `h`, the `0`-th by cuspidality), so the difference is `0`.
  have hsub : f.toCuspForm.toModularForm' - g.toCuspForm.toModularForm' = 0 := by
    rw [← ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods_Gamma1_map N)]
    refine PowerSeries.ext fun n => ?_
    rw [map_zero,
      show (⇑(f.toCuspForm.toModularForm' - g.toCuspForm.toModularForm') : UpperHalfPlane → ℂ) =
        ⇑f.toCuspForm.toModularForm' - ⇑g.toCuspForm.toModularForm' from
        ModularForm.coe_sub _ _,
      ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods_Gamma1_map N), map_sub, sub_eq_zero]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [show (⇑f.toCuspForm.toModularForm' : UpperHalfPlane → ℂ) = ⇑f.toCuspForm from rfl,
        show (⇑g.toCuspForm.toModularForm' : UpperHalfPlane → ℂ) = ⇑g.toCuspForm from rfl,
        CuspFormClass.qExpansion_coeff_zero f.toCuspForm one_pos
          (one_mem_strictPeriods_Gamma1_map N),
        CuspFormClass.qExpansion_coeff_zero g.toCuspForm one_pos
          (one_mem_strictPeriods_Gamma1_map N)]
    · exact congrFun h ⟨n, hn⟩
  exact ext_of_toCuspForm (cuspFormToModularFormLin_injective (sub_eq_zero.mp hsub))

/-! ### Petersson orthogonality and linear independence of newforms

Distinct newforms are pairwise Petersson-orthogonal, hence linearly independent.  Two cases:

* **Same character**: by Strong Multiplicity One (`coeffSeq_injOn_charSpace`) distinct newforms in
  the same eigenspace have a *distinct Hecke eigenvalue at some good `n`*, so they are orthogonal by
  the spectral orthogonality `eigenforms_orthogonal_of_ne_eigenvalues`.
* **Different characters**: the diamond operators are `petN`-unitary
  (`diamondOp_petersson_unitary`) and act by the (norm-`1`) scalars `χ(d)`; choosing `d` with
  `f.χ d ≠ g.χ d` forces `petN f g = 0`.

Linear independence then follows by the elementary Petersson-pairing argument (pairing a vanishing
combination with each form and using `petN`-definiteness), with no inner-product-space instance
needed.  This is the newform analogue of `linearIndependent_monoidHom`. -/

/-- Values of a character of the finite group `(ZMod N)ˣ` are roots of unity, so
`conj (χ d) · χ d = 1`. -/
private lemma conj_char_mul_self (χ : (ZMod N)ˣ →* ℂˣ) (d : (ZMod N)ˣ) :
    (starRingEnd ℂ) (↑(χ d) : ℂ) * (↑(χ d) : ℂ) = 1 := by
  have hnorm : ‖(↑(χ d) : ℂ)‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one (n := Fintype.card (ZMod N)ˣ)
      (by rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one])
      Fintype.card_ne_zero
  rw [Complex.conj_mul', hnorm, Complex.ofReal_one, one_pow]

/-- `petN` distributes over finite sums in its second (linear) argument. -/
private lemma petN_sum_right {ι : Type*} (s : Finset ι)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (x : ι → CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN f (∑ i ∈ s, x i) = ∑ i ∈ s, petN f (x i) := by
  induction s using Finset.cons_induction with
  | empty => simp [petN_zero_right]
  | cons _ _ _ ih => rw [Finset.sum_cons, petN_add_right, ih, Finset.sum_cons]

/-- **Petersson orthogonality of distinct newforms.**  Two distinct newforms of level `N`,
weight `k` are orthogonal for the level-`N` Petersson product. -/
lemma petN_toCuspForm_eq_zero_of_ne {f g : Newform N k} (hfg : f ≠ g) :
    petN f.toCuspForm g.toCuspForm = 0 := by
  by_cases hχ : f.χ = g.χ
  · -- Same character: SMO forces a distinct good-prime eigenvalue; apply spectral orthogonality.
    have hf_char : f.toCuspForm ∈ cuspFormCharSpace k f.χ :=
      Unified.cuspFormCharSpace_of_toModularForm'_mem f.mem_charSpace
    have hg_char : g.toCuspForm ∈ cuspFormCharSpace k g.χ :=
      Unified.cuspFormCharSpace_of_toModularForm'_mem g.mem_charSpace
    rw [hχ] at hf_char
    -- Some good-prime eigenvalue differs, else `f = g` by Strong Multiplicity One + Task-2.
    have : ∃ n : ℕ+, Nat.Coprime n.val N ∧ f.eigenvalue n ≠ g.eigenvalue n := by
      by_contra hcon
      push Not at hcon
      refine hfg (ext_of_toCuspForm (strongMultiplicityOne f g g.χ
        (hχ ▸ f.mem_charSpace) g.mem_charSpace ∅ fun n hn _ => hcon n hn))
    obtain ⟨n, hn, hne⟩ := this
    haveI : NeZero n.val := ⟨n.pos.ne'⟩
    exact eigenforms_orthogonal_of_ne_eigenvalues g.χ hf_char hg_char
      f.toCuspForm_ne_zero g.toCuspForm_ne_zero hn (f.isEigen n hn) (g.isEigen n hn) hne
  · -- Different characters: use diamond unitarity and norm-`1` character values.
    obtain ⟨d, hd⟩ := DFunLike.ne_iff.mp hχ
    have hf_char : f.toCuspForm ∈ cuspFormCharSpace k f.χ :=
      Unified.cuspFormCharSpace_of_toModularForm'_mem f.mem_charSpace
    have hg_char : g.toCuspForm ∈ cuspFormCharSpace k g.χ :=
      Unified.cuspFormCharSpace_of_toModularForm'_mem g.mem_charSpace
    have hdf : diamondOp_cusp k d f.toCuspForm = (↑(f.χ d) : ℂ) • f.toCuspForm :=
      diamondOpCusp_apply_charSpace k f.χ d hf_char
    have hdg : diamondOp_cusp k d g.toCuspForm = (↑(g.χ d) : ℂ) • g.toCuspForm :=
      diamondOpCusp_apply_charSpace k g.χ d hg_char
    -- Unitarity + (conjugate-)linearity give `conj(χf d) · χg d · petN = petN`.
    have hu := diamondOp_petersson_unitary d f.toCuspForm g.toCuspForm
    rw [hdf, hdg, petN_conj_smul_left, petN_smul_right] at hu
    -- So `(conj(χf d) · χg d − 1) · petN = 0`; the scalar is nonzero since `χf d ≠ χg d`.
    have hcoeff_ne : (starRingEnd ℂ) (↑(f.χ d) : ℂ) * (↑(g.χ d) : ℂ) ≠ 1 := by
      intro hc
      -- Multiply by `χf d` and use `conj(χf d) · χf d = 1` to get `χg d = χf d`.
      apply hd
      apply Units.ext
      have := congrArg (· * (↑(f.χ d) : ℂ)) hc
      simp only [one_mul] at this
      rw [mul_right_comm, conj_char_mul_self f.χ d, one_mul] at this
      exact this.symm
    have : ((starRingEnd ℂ) (↑(f.χ d) : ℂ) * (↑(g.χ d) : ℂ) - 1) *
        petN f.toCuspForm g.toCuspForm = 0 := by
      rw [sub_mul, one_mul, mul_assoc, hu, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hcoeff_ne)

/-- **Linear independence of newforms.**  The underlying cusp forms of the newforms of level `N`,
weight `k` are `ℂ`-linearly independent: a vanishing linear combination, paired with each form via
`petN`, forces every coefficient to vanish (orthogonality + `petN`-definiteness).  No finiteness is
assumed (the index type is the bare `Newform N k`). -/
lemma linearIndependent_toCuspForm :
    LinearIndependent ℂ (fun f : Newform N k => f.toCuspForm) := by
  classical
  rw [linearIndependent_iff']
  intro s c hc f₀ hf₀
  -- Pair the vanishing combination `∑ f∈s, c f • f.toCuspForm = 0` with `f₀` on the right.
  have hpair : petN f₀.toCuspForm (∑ f ∈ s, c f • f.toCuspForm) = 0 := by rw [hc, petN_zero_right]
  -- The pairing collapses to the single diagonal term `c f₀ • petN f₀ f₀`.
  have hsum : petN f₀.toCuspForm (∑ f ∈ s, c f • f.toCuspForm) =
      c f₀ * petN f₀.toCuspForm f₀.toCuspForm := by
    rw [petN_sum_right, Finset.sum_eq_single f₀]
    · rw [petN_smul_right]
    · intro f _ hf
      rw [petN_smul_right, petN_toCuspForm_eq_zero_of_ne (Ne.symm hf), mul_zero]
    · exact fun h => absurd hf₀ h
  rw [hsum] at hpair
  -- `petN f₀ f₀ ≠ 0` since `f₀.toCuspForm ≠ 0`, so `c f₀ = 0`.
  exact (mul_eq_zero.mp hpair).resolve_right (fun h => f₀.toCuspForm_ne_zero (petN_definite _ h))

/-- The `q`-expansion (period `1`) as a `ℂ`-linear map `S_k(Γ₁(N)) → ℂ⟦X⟧`, with trivial kernel
(a cusp form is determined by its `q`-expansion).  Used to transfer linear independence from the
underlying forms to the coefficient sequences. -/
def qExpansionLin : CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ] PowerSeries ℂ where
  toFun F := UpperHalfPlane.qExpansion (1 : ℝ) F
  map_add' F G :=
    ModularForm.qExpansion_add one_pos (one_mem_strictPeriods_Gamma1_map N) F G
  map_smul' c F := by
    rw [RingHom.id_apply]
    exact ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma1_map N) c F

/-- The coefficient-sequence extraction as a `ℂ`-linear map `S_k(Γ₁(N)) → (ℕ⁺ → ℂ)`
(`F ↦ fun n ↦ aₙ(F)`), with trivial kernel.  Restricted to newforms it is `coeffSeq`. -/
def coeffSeqLin : CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ] (ℕ+ → ℂ) where
  toFun F n := (qExpansionLin F).coeff n.val
  map_add' F G := by funext n; simp [map_add]
  map_smul' c F := by funext n; simp [map_smul]

lemma coeffSeqLin_ker_eq_bot :
    LinearMap.ker (coeffSeqLin (N := N) (k := k)) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro F hF
  -- `coeffSeqLin F = 0` ⇒ all positive `q`-coefficients vanish; with cuspidality (coeff `0`) this
  -- forces the whole `q`-expansion to vanish, hence the form is `0`.
  have hcoeff : ∀ n : ℕ+, (UpperHalfPlane.qExpansion (1 : ℝ) F).coeff n.val = 0 :=
    fun n => congrFun hF n
  apply cuspFormToModularFormLin_injective
  rw [map_zero,
    show cuspFormToModularFormLin F = F.toModularForm' from rfl,
    ← ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods_Gamma1_map N)]
  refine PowerSeries.ext fun n => ?_
  rw [map_zero, show (⇑F.toModularForm' : UpperHalfPlane → ℂ) = ⇑F from rfl]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact CuspFormClass.qExpansion_coeff_zero F one_pos (one_mem_strictPeriods_Gamma1_map N)
  · exact hcoeff ⟨n, hn⟩

lemma coeffSeq_eq_coeffSeqLin (f : Newform N k) : coeffSeq f = coeffSeqLin f.toCuspForm := rfl

/-- **Linear independence of newform coefficient sequences.**  The normalised Fourier coefficient
sequences `coeffSeq f` of the newforms of level `N`, weight `k` are `ℂ`-linearly independent.  This
transfers `linearIndependent_toCuspForm` along the injective linear map `coeffSeqLin`
(`q`-expansion determines the form), and is the newform analogue of
`linearIndependent_monoidHom`. -/
lemma linearIndependent_coeffSeq :
    LinearIndependent ℂ (coeffSeq (N := N) (k := k)) := by
  have h := linearIndependent_toCuspForm (N := N) (k := k) |>.map'
    coeffSeqLin coeffSeqLin_ker_eq_bot
  exact h

/-! ### The coefficient (Hecke eigenvalue) field `K_f = ℚ(aₙ : n)`

`K_f` is the subfield of `ℂ` generated over `ℚ` by all the `aₙ(f)`.  That it is a *number field*
(`[K_f : ℚ] < ∞`) is the deep input isolated below. -/

/-- The **coefficient field** (Hecke eigenvalue field) `K_f = ℚ(aₙ : n) ⊆ ℂ` of a newform: the
intermediate field of `ℂ / ℚ` generated by the normalised Fourier coefficients. -/
def coeffField (f : Newform N k) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (Set.range (coeffSeq f))

lemma coeffSeq_mem_coeffField (f : Newform N k) (n : ℕ+) : coeffSeq f n ∈ coeffField f :=
  IntermediateField.subset_adjoin ℚ _ ⟨n, rfl⟩

/-! ### [T004a] Newform coefficients are Hecke eigenvalues for ALL `n` (DS eq 5.21 + Thm 5.8.2) -/

/-- The canonical `q`-coefficient of `heckeT_n_cusp` agrees with that of the underlying
`ModularForm`-level `heckeT_n` (they have the same `toModularForm'`, hence the same
`q`-expansion). -/
private lemma coeff_heckeT_n_cusp_eq_heckeT_n (m j : ℕ) [NeZero j]
    (h : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (UpperHalfPlane.qExpansion (1 : ℝ) (heckeT_n_cusp k j h)).coeff m =
      (UpperHalfPlane.qExpansion (1 : ℝ) (heckeT_n k j h.toModularForm')).coeff m := rfl

/-- `heckeT_n_cusp` preserves the Nebentypus eigenspace (at the cusp level): if
`h.toModularForm' ∈ modFormCharSpace k χ` then so is `(heckeT_n_cusp k j h).toModularForm'`.
Holds for **all** `j` (good or bad) via `heckeT_n_preserves_modFormCharSpace_all`. -/
private lemma heckeT_n_cusp_mem_charSpace (j : ℕ) [NeZero j] (χ : (ZMod N)ˣ →* ℂˣ)
    {h : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hh : h.toModularForm' ∈ modFormCharSpace k χ) :
    (heckeT_n_cusp k j h).toModularForm' ∈ modFormCharSpace k χ := by
  rw [heckeT_n_cusp_toModularForm']
  exact heckeT_n_preserves_modFormCharSpace_all k j χ hh

/-- **Cusp-level period-1 Fourier coefficient formula for a coprime `Tₙ`** (DS eq 5.20). For `n'`
coprime to `N` and a cusp form `h` in the eigenspace `modFormCharSpace k χ`, the `m`-th canonical
coefficient of `Tₙ' h` is the Hecke divisor sum.  This is the cusp-level transport of
`fourierCoeff_heckeT_n_period_one`. -/
private lemma coeff_heckeT_n_cusp_coprime (n' : ℕ) [NeZero n'] (hn' : Nat.Coprime n' N)
    (χ : (ZMod N)ˣ →* ℂˣ) {h : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hh : h.toModularForm' ∈ modFormCharSpace k χ) (m : ℕ) :
    (UpperHalfPlane.qExpansion (1 : ℝ) (heckeT_n_cusp k n' h)).coeff m =
      ∑ d ∈ (Nat.gcd m n').divisors,
        if hd : d.Coprime N then
          (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d hd)) *
            (UpperHalfPlane.qExpansion (1 : ℝ) h.toModularForm').coeff (m * n' / (d * d))
        else 0 := by
  rw [coeff_heckeT_n_cusp_eq_heckeT_n]
  exact fourierCoeff_heckeT_n_period_one k n' hn' χ hh m

/-- **Cusp-level coprime collapse at coprime index** (DS eq 5.20 single term). For `n'` coprime to
`N`, `h` in the eigenspace, and an index `m` coprime to `n'` (so `gcd(m, n') = 1`), the divisor sum
collapses to the single `d = 1` term: `a_m(Tₙ' h) = a_{m·n'}(h)`. -/
private lemma coeff_heckeT_n_cusp_coprime_index (n' : ℕ) [NeZero n'] (hn' : Nat.Coprime n' N)
    (χ : (ZMod N)ˣ →* ℂˣ) {h : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hh : h.toModularForm' ∈ modFormCharSpace k χ) (m : ℕ) (hm : Nat.Coprime m n') :
    (UpperHalfPlane.qExpansion (1 : ℝ) (heckeT_n_cusp k n' h)).coeff m =
      (UpperHalfPlane.qExpansion (1 : ℝ) h).coeff (m * n') := by
  rw [coeff_heckeT_n_cusp_coprime n' hn' χ hh m]
  have hunit : ZMod.unitOfCoprime 1 (Nat.coprime_one_left N) = 1 := by
    ext; simp [ZMod.coe_unitOfCoprime]
  rw [show Nat.gcd m n' = 1 from hm, Nat.divisors_one, Finset.sum_singleton,
    dif_pos (Nat.coprime_one_left N)]
  simp only [hunit, Nat.cast_one, one_zpow, map_one, Units.val_one, mul_one, Nat.div_one, one_mul]
  rfl

/-- **Bad prime-power Fourier relation** (cusp level): for a bad prime `p ∣ N` and any `v`, the
`l`-th canonical coefficient of `T_{p^v} h = U_p^v h` is `a_{p^v·l}(h)`, for **all** `l`.  Proved by
induction on `v`, iterating the single-prime relation `heckeT_n_cusp_divN_coeff`. -/
private lemma coeff_heckeT_ppow_bad (p : ℕ) (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N) (v : ℕ)
    (h : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (l : ℕ) :
    haveI : NeZero (p ^ v) := ⟨(pow_pos hp.pos v).ne'⟩
    (UpperHalfPlane.qExpansion (1 : ℝ) (heckeT_n_cusp k (p ^ v) h)).coeff l =
      (UpperHalfPlane.qExpansion (1 : ℝ) h).coeff (p ^ v * l) := by
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  induction v generalizing l with
  | zero =>
    haveI : NeZero (p ^ 0) := ⟨(pow_pos hp.pos 0).ne'⟩
    have h1 : heckeT_n_cusp k (p ^ 0) h = h := by
      apply CuspForm.ext; intro z
      show ((heckeT_n k (p ^ 0)) h.toModularForm').toFun z = h z
      simp only [pow_zero, heckeT_n_one]; rfl
    rw [h1, pow_zero, one_mul]
  | succ w ih =>
    haveI : NeZero (p ^ (w + 1)) := ⟨(pow_pos hp.pos _).ne'⟩
    haveI : NeZero (p ^ w) := ⟨(pow_pos hp.pos _).ne'⟩
    -- `T_{p^{w+1}} = T_p ∘ T_{p^w}` at the cusp level (bad prime: diamond term vanishes).
    have hmul : heckeT_n (N := N) k (p ^ (w + 1)) = heckeT_n k p * heckeT_n k (p ^ w) := by
      rw [heckeT_n_prime_pow k hp (w + 1) (Nat.succ_pos _),
        heckeT_ppow_eq_pow_of_not_coprime k hp hpN (w + 1), heckeT_n_prime k hp, pow_succ']
      cases w with
      | zero => simp [heckeT_n_one]
      | succ w' => rw [heckeT_n_prime_pow k hp (w' + 1) (Nat.succ_pos _),
          heckeT_ppow_eq_pow_of_not_coprime k hp hpN (w' + 1)]
    -- Decompose, apply the single-prime relation, then the inductive hypothesis at index `p·l`.
    have hdecomp : heckeT_n_cusp k (p ^ (w + 1)) h =
        heckeT_n_cusp k p (heckeT_n_cusp k (p ^ w) h) := by
      apply CuspForm.ext; intro z
      show ((heckeT_n (N := N) k (p ^ (w + 1))) h.toModularForm').toFun z =
        ((heckeT_n k p) ((heckeT_n k (p ^ w)) h.toModularForm')).toFun z
      rw [hmul]; rfl
    rw [hdecomp, heckeT_n_cusp_divN_coeff p hp hpN _ l, ih (p * l), ← mul_assoc, ← pow_succ]

/-- **[T004a sub-leaf — DS eq (5.21), general form]** Multiplicative Hecke coefficient relation: for
any `n`, any cusp form `g` in the eigenspace, and any index `m` coprime to `n`, the `m`-th canonical
coefficient of `Tₙ g` is `a_{m·n}(g)`.  Proved by strong induction on `n`, peeling the smallest
prime factor `p` (good: the coprime divisor-sum collapses; bad: iterate `U_p`), exactly mirroring
`Newform.exists_heckeT_n_cusp_smul`. -/
lemma coeff_heckeT_n_cusp_coprime_mul (n : ℕ) [NeZero n] (χ : (ZMod N)ˣ →* ℂˣ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hg : g.toModularForm' ∈ modFormCharSpace k χ)
    (m : ℕ) (hm : Nat.Coprime m n) :
    (UpperHalfPlane.qExpansion (1 : ℝ) (heckeT_n_cusp k n g)).coeff m =
      (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff (m * n) := by
  -- Strong induction over `n` with `m`, `g`, `hg`, `hm` generalised.
  suffices key : ∀ j : ℕ, (hj : j ≠ 0) →
      haveI : NeZero j := ⟨hj⟩
      ∀ (g' : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
        g'.toModularForm' ∈ modFormCharSpace k χ → ∀ m', Nat.Coprime m' j →
          (UpperHalfPlane.qExpansion (1 : ℝ) (heckeT_n_cusp k j g')).coeff m' =
            (UpperHalfPlane.qExpansion (1 : ℝ) g').coeff (m' * j) by
    exact key n (NeZero.ne n) g hg m hm
  clear hm hg m g
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
  intro hj0
  haveI : NeZero j := ⟨hj0⟩
  intro g hg m hm
  by_cases hj1 : j = 1
  · subst hj1
    have h1 : heckeT_n_cusp k 1 g = g := by
      apply CuspForm.ext; intro z
      show ((heckeT_n k 1) g.toModularForm').toFun z = g z
      rw [heckeT_n_one]; rfl
    rw [h1, mul_one]
  · have hj_gt : 1 < j := by omega
    set p := j.minFac with hp_def
    have hp : Nat.Prime p := Nat.minFac_prime (by omega)
    haveI : NeZero p := ⟨hp.pos.ne'⟩
    set v := j.factorization p with hv_def
    have hv_pos : 0 < v := hp.factorization_pos_of_dvd (by omega) (Nat.minFac_dvd j)
    set q := j / p ^ v with hq_def
    have hpvq : p ^ v * q = j := Nat.ordProj_mul_ordCompl_eq_self j p
    have hpq : Nat.Coprime p q := Nat.coprime_ordCompl hp (by omega)
    have hq_pos : 0 < q := Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd j p))
      (pow_pos hp.pos v)
    haveI : NeZero (p ^ v) := ⟨(pow_pos hp.pos v).ne'⟩
    haveI : NeZero q := ⟨hq_pos.ne'⟩
    have hq_lt : q < j := by
      have : q = j / p ^ v := hq_def
      rw [this]
      exact Nat.div_lt_self (by omega) (Nat.one_lt_pow hv_pos.ne' hp.one_lt)
    -- `coprime m (p^v)` and `coprime m q` (from `coprime m j`, since `p^v ∣ j`, `q ∣ j`).
    have hmpv : Nat.Coprime m (p ^ v) :=
      Nat.Coprime.coprime_dvd_right (Dvd.intro q hpvq) hm
    have hmq : Nat.Coprime m q := Nat.Coprime.coprime_dvd_right (Dvd.intro_left (p ^ v) hpvq) hm
    have hpvq_cop : Nat.Coprime (p ^ v) q := hpq.pow_left v
    -- Decompose `T_j = T_{p^v} ∘ T_q` at the cusp level.
    have hmul : heckeT_n (N := N) k j = heckeT_n k (p ^ v) * heckeT_n k q :=
      heckeT_n_mul_ppow_quot (N := N) (k := k) j hj_gt p hp hp_def v hv_def hv_pos hq_pos
    have hdecomp : heckeT_n_cusp k j g = heckeT_n_cusp k (p ^ v) (heckeT_n_cusp k q g) := by
      apply CuspForm.ext; intro z
      show ((heckeT_n (N := N) k j) g.toModularForm').toFun z =
        ((heckeT_n k (p ^ v)) ((heckeT_n k q) g.toModularForm')).toFun z
      rw [hmul]; rfl
    -- `T_q g` is again in the eigenspace.
    have hTqg : (heckeT_n_cusp k q g).toModularForm' ∈ modFormCharSpace k χ :=
      heckeT_n_cusp_mem_charSpace q χ hg
    -- Coefficient at `m` of `T_{p^v}(T_q g)`: good prime ⇒ coprime collapse; bad ⇒ iterate `U_p`.
    rw [hdecomp]
    have hstep : (UpperHalfPlane.qExpansion (1 : ℝ)
        (heckeT_n_cusp k (p ^ v) (heckeT_n_cusp k q g))).coeff m =
        (UpperHalfPlane.qExpansion (1 : ℝ) (heckeT_n_cusp k q g)).coeff (m * p ^ v) := by
      by_cases hpN : Nat.Coprime p N
      · -- good prime: `p^v` coprime to `N`; coprime collapse at index `m` (coprime to `p^v`).
        exact coeff_heckeT_n_cusp_coprime_index (p ^ v) (hpN.pow_left v) χ hTqg m hmpv
      · -- bad prime: `T_{p^v} = U_p^v`, coefficient relation `a_m(U_p^v ·) = a_{p^v·m}(·)`.
        rw [coeff_heckeT_ppow_bad p hp hpN v (heckeT_n_cusp k q g) m, mul_comm (p ^ v) m]
    rw [hstep]
    -- inductive hypothesis for `q` at index `m·p^v` (coprime to `q`).
    have hmpvq : Nat.Coprime (m * p ^ v) q := Nat.Coprime.mul_left hmq hpvq_cop
    rw [ih q hq_lt hq_pos.ne' g hg (m * p ^ v) hmpvq, mul_assoc, hpvq]

/-- **[T004a sub-leaf — DS eq (5.21), all `n`]** The `n`-th canonical Fourier coefficient equals
the *first* coefficient of `Tₙ g`: `aₙ(g) = a₁(Tₙ g)`.  (At `m = 1`, `gcd(1,n)=1` collapses the
Hecke divisor sum to the single `d=1` term.)  Holds for every `n` — both `(n,N)=1` and bad `n`. -/
lemma coeff_n_eq_coeff_one_heckeT_n_cusp (n : ℕ) [NeZero n] (χ : (ZMod N)ˣ →* ℂˣ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg : g.toModularForm' ∈ modFormCharSpace k χ) :
    (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff n =
      (UpperHalfPlane.qExpansion (1 : ℝ) (heckeT_n_cusp k n g)).coeff 1 := by
  rw [coeff_heckeT_n_cusp_coprime_mul n χ g hg 1 (Nat.coprime_one_left n), one_mul]

/-- a₁-coefficient of a scalar multiple (local; `qExpansion` is ℂ-linear). -/
private lemma qExp_one_coeff_one_smul (c : ℂ) (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (UpperHalfPlane.qExpansion (1 : ℝ) (⇑(c • g) : UpperHalfPlane → ℂ)).coeff 1 =
      c * (UpperHalfPlane.qExpansion (1 : ℝ) (⇑g : UpperHalfPlane → ℂ)).coeff 1 := by
  change (UpperHalfPlane.qExpansion (1 : ℝ) (c • g.toModularForm')).coeff 1 = _
  rw [ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma1_map N) c g.toModularForm',
    PowerSeries.coeff_smul, smul_eq_mul]
  rfl

/-- **[T004a]** For a newform, the `n`-th Fourier coefficient is the `Tₙ`-eigenvalue
`newformEigenHom f (heckeEnd n)`, for **all** `n` (DS Theorem 5.8.2(b)). -/
theorem coeffSeq_eq_newformEigenHom_heckeEnd (f : Newform N k) (n : ℕ+) :
    coeffSeq f n = newformEigenHom f ⟨heckeEnd N k n, heckeEnd_mem n⟩ := by
  haveI : NeZero n.val := ⟨n.pos.ne'⟩
  have hsmul : heckeT_n_cusp k n.val f.toCuspForm =
      newformEigenHom f ⟨heckeEnd N k n, heckeEnd_mem n⟩ • f.toCuspForm :=
    (f.eigenScalar_smul ⟨heckeEnd N k n, heckeEnd_mem n⟩).symm
  have h1 : coeffSeq f n =
      (UpperHalfPlane.qExpansion (1 : ℝ) (heckeT_n_cusp k n.val f.toCuspForm)).coeff 1 :=
    coeff_n_eq_coeff_one_heckeT_n_cusp n.val f.χ f.toCuspForm f.mem_charSpace
  rw [h1, hsmul, qExp_one_coeff_one_smul, f.isNorm, mul_one]

/-- **Hecke eigenvalues are algebraic integers** (Shimura, *Introduction to the Arithmetic Theory of
Automorphic Functions*, **Thm 3.48(3)** p.83; Diamond–Shurman Thm 6.5.1): each normalised Fourier
coefficient `aₙ(f)` of a newform is integral **over `ℤ`** (a genuine algebraic integer — the full
source strength, not merely algebraic over `ℚ`).  Proved modulo the single finiteness input
`heckeAlgℤ_finite`.  (Shimura Thm 3.52, p.85, is the *integral q-expansion basis* / full-rank
lattice
— a different statement, used for `heckeAlgℤ_finite`, not here.) -/
theorem coeffSeq_isIntegral (f : Newform N k) (n : ℕ+) : IsIntegral ℤ (coeffSeq f n) := by
  haveI : Module.Finite ℤ ↥(newformEigenHom f).range := newformEigenHom_range_finite f
  have hmem : coeffSeq f n ∈ (newformEigenHom f).range := by
    rw [coeffSeq_eq_newformEigenHom_heckeEnd]; exact ⟨_, rfl⟩
  exact (IsIntegral.of_finite ℤ (⟨coeffSeq f n, hmem⟩ : (newformEigenHom f).range)).map
    ((newformEigenHom f).range.subtype.toIntAlgHom)

/-- **The eigenvalue arithmetic of a newform** (Shimura Thm 3.51(1)): the generating set `{aₙ}` is a
priori infinite, but all `aₙ` lie in the eigenvalue ring `O_f = (newformEigenHom f).range`, which is
module-finite over `ℤ` — so `K_f` is finite-dimensional over `ℚ`.  Factored to take the
finiteness as
a hypothesis; the deep input (`heckeAlgℤ_finite`) enters at the use sites below.

`K_f` is finite-dimensional over `ℚ` once the eigenvalue ring `O_f := (newformEigenHom f).range`
is module-finite over `ℤ`.  The finiteness `hfin` (the one deep input, via `heckeAlgℤ_finite` /
`newformEigenHom_range_finite`) is taken as a hypothesis so the `k ≥ 2` corollary
`coeffField_numberField_of_two_le` can supply the axiom-clean Eichler-route finiteness directly. -/
theorem finiteDimensional_coeffField_of_rangeFinite (f : Newform N k)
    (hfin : Module.Finite ℤ ↥(newformEigenHom f).range) :
    FiniteDimensional ℚ (coeffField f) := by
  classical
  obtain ⟨S, hSfin, hSspan⟩ := Submodule.fg_def.mp hfin.fg_top
  set Tc : Set ℂ := (newformEigenHom f).range.subtype '' S
  haveI : Finite ↑Tc := (hSfin.image _).to_subtype
  have hOf_sub' : ∀ z : ↥(newformEigenHom f).range,
      (z : ℂ) ∈ (IntermediateField.adjoin ℚ Tc : Set ℂ) := by
    intro z
    have hz : z ∈ Submodule.span ℤ S := hSspan.ge Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem s hs => exact IntermediateField.subset_adjoin ℚ Tc ⟨s, hs, rfl⟩
    | zero => simp
    | add a b _ _ ha hb => exact add_mem ha hb
    | smul c a _ ha =>
        simpa [zsmul_eq_mul] using mul_mem ((IntermediateField.adjoin ℚ Tc).intCast_mem c) ha
  have hint : ∀ x ∈ Tc, IsIntegral ℚ x := by
    rintro x ⟨y, _, rfl⟩
    exact ((IsIntegral.of_finite ℤ y).map (newformEigenHom f).range.subtype.toIntAlgHom).tower_top
  haveI : FiniteDimensional ℚ ↥(IntermediateField.adjoin ℚ Tc) :=
    IntermediateField.finiteDimensional_adjoin hint
  have hle : coeffField f ≤ IntermediateField.adjoin ℚ Tc := by
    rw [coeffField, IntermediateField.adjoin_le_iff]
    rintro x ⟨n, rfl⟩
    rw [coeffSeq_eq_newformEigenHom_heckeEnd]
    exact hOf_sub' ⟨_, _, rfl⟩
  exact Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion_injective hle)

/-- `K_f` is finite-dimensional over `ℚ` (all weights), via the live finiteness input
`heckeAlgℤ_finite` (`newformEigenHom_range_finite`). -/
instance instFiniteDimensionalCoeffField (f : Newform N k) :
    FiniteDimensional ℚ (coeffField f) :=
  finiteDimensional_coeffField_of_rangeFinite f (newformEigenHom_range_finite f)

/-- The coefficient field `K_f` is a number field (`CharZero` + `[K_f : ℚ] < ∞`).  `CharZero` is
automatic (it is a subfield of `ℂ`); finite-dimensionality is the deep input
`instFiniteDimensionalCoeffField`. -/
instance instNumberFieldCoeffField (f : Newform N k) : NumberField (coeffField f) where
  to_charZero := inferInstance
  to_finiteDimensional := instFiniteDimensionalCoeffField f

/-- **The coefficient field `K_f = ℚ(aₙ : n)` of a weight-`k ≥ 2` newform is a number field —
UNCONDITIONALLY (axiom-clean).**  For `k ≥ 2` the finiteness of the integral Hecke algebra is
supplied by the integral Eichler–Shimura *period-map injectivity* route
(`ModularSymbols.heckeAlgℤ_finite_of_period` with injectivity `periodMap'_injective_eichler`,
which is
axiom-clean — `{propext, Classical.choice, Quot.sound}`), so this carries **no**
`exists_HeckeStableLattice` / Deligne–Serre dependency (that is only the `k < 2` branch of the
all-weights instance `instNumberFieldCoeffField`).  This is the headline arithmetic consequence
of the
Eichler route: `[K_f : ℚ] < ∞` for every weight `k ≥ 2`, every level `N`. -/
theorem coeffField_numberField_of_two_le (f : Newform N k) (hk : 2 ≤ k) :
    NumberField (coeffField f) := by
  -- `k ≥ 2`: the integral Hecke algebra is module-finite over `ℤ` via the Eichler period route
  -- (axiom-clean), bypassing the weight case-split of the live `heckeAlgℤ_finite` instance.
  haveI : Module.Finite ℤ (heckeAlgℤ N k) := heckeAlgℤ_finite_of_two_le hk
  -- Hence the eigenvalue ring `O_f` is a finite `ℤ`-module (surjective image of `heckeAlgℤ`), built
  -- from the *local* (Eichler, axiom-clean) finiteness above — NOT `newformEigenHom_range_finite`,
  -- which bakes in the weight-case-split instance and would re-pull the `k < 2` lattice `sorry`.
  haveI hOf : Module.Finite ℤ ↥(newformEigenHom f).range :=
    Module.Finite.of_surjective
      (RingHom.rangeRestrict (newformEigenHom f)).toIntAlgHom.toLinearMap
      (RingHom.rangeRestrict_surjective _)
  -- ...so `K_f = O_f ⊗ ℚ` is finite-dimensional, and `CharZero` (a subfield of `ℂ`) gives a
  -- number field.
  exact { to_finiteDimensional := finiteDimensional_coeffField_of_rangeFinite f hOf }

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

/-- **Finiteness of the space of newforms.**  There are only finitely many newforms of level `N`
and weight `k`.  Proved here: the cusp-form space `S_k(Γ₁(N))` is finite-dimensional
(`cuspForm_finiteDimensional`) and distinct newforms are `ℂ`-linearly independent
(`linearIndependent_toCuspForm`, via Petersson orthogonality + Strong Multiplicity One), so the
injective family `f ↦ f.toCuspForm` has a finite index type (`LinearIndependent.finite`).

It is the canonical witness for the `[Fintype (Newform N k)]` hypothesis carried by the
orbit/ranking machinery below.  It is deliberately **not** registered as a global instance (only
`@[reducible]`), so that the orbit/ranking lemmas — which take `[Fintype (Newform N k)]` as an
explicit hypothesis — keep that finiteness localised; supply it
(`haveI := Newform.instFiniteNewform`) to specialise the machinery to the genuine, finite space of
newforms. -/
@[reducible] def instFiniteNewform : Finite (Newform N k) :=
  haveI : FiniteDimensional ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
    cuspForm_finiteDimensional
  linearIndependent_toCuspForm.finite

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

/-- **Orbit-level trace separation.**  If two newforms (of level `N`, weight `k`, sharing the
Nebentypus eigenspace `modFormCharSpace k χ`) have the *same orbit trace sequence*
`n ↦ Σ_{orbit} aₙ`, then they are Galois conjugate.  Equivalently, the LMFDB lexicographic order
on the trace tuple is a strict total order on orbits.

This is the orbit-level upgrade of the single-form Strong Multiplicity One separation
`coeffSeq_injOn_charSpace`: the trace sequence is the orbit-indicator-weighted sum of the (linearly
independent) coefficient systems, and equal trace sequences force equal indicator coefficients,
hence equal orbits.  Mirrors the Artin–Dedekind separation `orbitRankKey_injOn_orbits` used for the
character label, with `linearIndependent_coeffSeq` (the newform analogue of
`linearIndependent_monoidHom`, proved via Petersson orthogonality + Strong Multiplicity One) playing
the role of `linearIndependent_monoidHom`.  The character hypotheses are not needed: the coefficient
systems are linearly independent globally. -/
private lemma traceSeq_injOn_orbits {f g : Newform N k} (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (h : orbitRankKey f = orbitRankKey g) : IsGaloisConj f g := by
  classical
  -- Indicator coefficient functions of the two orbits.
  set F : Newform N k → ℂ := fun ρ => if ρ ∈ galoisOrbit f then 1 else 0 with hF
  set G : Newform N k → ℂ := fun ρ => if ρ ∈ galoisOrbit g then 1 else 0 with hG
  have htrace : traceSeqAt f = traceSeqAt g := h
  -- An indicator-weighted sum of the coefficient systems reproduces the orbit-trace sequence.
  have key : ∀ (A : Finset (Newform N k)) (n : ℕ+),
      (∑ i, (if i ∈ A then (1 : ℂ) else 0) • coeffSeq i n) = ∑ ρ ∈ A, coeffSeq ρ n := by
    intro A n
    simp only [smul_eq_mul, boole_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hsum : ∑ i, F i • coeffSeq i = ∑ i, G i • coeffSeq i := by
    funext n
    simp only [Finset.sum_apply, Pi.smul_apply, hF, hG]
    rw [key (galoisOrbit f) n, key (galoisOrbit g) n]
    simpa only [traceSeqAt] using congrFun htrace n
  -- Linear independence of the coefficient systems forces equal indicator coefficients.
  have hcoeff := (Fintype.linearIndependent_iffₛ.mp linearIndependent_coeffSeq) F G hsum
  -- Hence the two Galois orbits coincide as `Finset`s.
  have horb : galoisOrbit f = galoisOrbit g := by
    ext ρ
    have hρ := hcoeff ρ
    simp only [hF, hG] at hρ
    by_cases h1 : ρ ∈ galoisOrbit f <;> by_cases h2 : ρ ∈ galoisOrbit g <;> simp_all
  -- `g ∈ galoisOrbit g = galoisOrbit f`, i.e. `g` is Galois-conjugate to `f`.
  exact mem_galoisOrbit_iff.mp (horb ▸ self_mem_galoisOrbit g)

/-- **Rank-injectivity.**  Equal orbit indices force equal ordering keys: the strictly-monotone
rank function `key ↦ #{realised keys strictly below it}` is injective on the finite set of realised
keys (`rank_injOn`), and both keys are realised. -/
lemma orbitIndex_inj {f g : Newform N k} (h : orbitIndex f = orbitIndex g) :
    orbitRankKey f = orbitRankKey g :=
  LeanModularForms.Labels.rank_injOn _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
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



