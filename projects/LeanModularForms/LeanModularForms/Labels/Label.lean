/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.Labels.CharacterOrbit
import LeanModularForms.Labels.NewformOrbit
import LeanModularForms.HeckeRIngs.GL2.Newforms.CoeffSeq

/-!
# The full LMFDB newform label `N.k.a.x`

This file assembles the complete LMFDB **classical-modular-form label**
`N.k.a.x` of a `Newform`, from the four components built in the preceding files:

* `N` — the level (a `ℕ`);
* `k` — the weight (an `ℤ`);
* `a` — the Dirichlet-character **Galois-orbit** label `DirichletCharacter.charOrbitLabel`
  of the form's Nebentypus character, from `Labels/CharacterOrbit.lean` (Phase 1);
* `x` — the newform **Galois(Hecke)-orbit** label `Newform.newformOrbitLabel`, from
  `Labels/NewformOrbit.lean` (Phase 2).

See *Computing Classical Modular Forms* (Best–Bober–Booker–Costa–Cremona–Derickx–Lee–
Lowry-Duda–Roe–Sutherland–Voight, arXiv:2002.04717, §"Labels") and the LMFDB knowl
`cmf.label`.

## The Nebentypus character of a newform

A `Newform N k` extends an `Eigenform N k`, which **carries** its Nebentypus character as the
field `Eigenform.χ : (ZMod N)ˣ →* ℂˣ`, together with the proof `mem_charSpace` that the form
lies in the single character eigenspace `modFormCharSpace k χ` (DS Def 5.5.4).  The `a`-component
is therefore read off the canonical Mathlib `DirichletCharacter ℂ N` lift of this character,
`Newform.dirichletLift f.χ = MulChar.ofUnitHom f.χ` (`Labels`'s `newformChar f`).

## Main definitions

* `HeckeRing.GL2.Newform.newformChar f` — the Nebentypus `DirichletCharacter ℂ N` of `f`.
* `HeckeRing.GL2.Newform.lmfdbLabel f` — the full LMFDB label `N.k.a.x` as a `String`.

## Main results

* `HeckeRing.GL2.Newform.lmfdbLabel_eq_of_isGaloisConj` — **the label is constant on the
  Galois orbit of `f`** (canonicity / well-definedness).  Galois conjugation sends the
  Nebentypus character `χ_f` to a Galois-conjugate character (hypothesis `hχ`, the deep
  character-stability input also left abstract in `Labels/NewformOrbit.lean`), so the
  `a`-component is invariant via Phase 1's `charOrbitLabel_eq_of_isGaloisConj`, and the
  `x`-component via Phase 2's `newformOrbitLabel_eq_of_isGaloisConj`; the two compose to give
  equality of the full label.  This is **sorry-free** and is the deliverable: a single
  well-defined LMFDB label map, proven Galois-invariant.
* `HeckeRing.GL2.Newform.lmfdbLabel_injOn_orbits` — **the label is injective on distinct
  orbits**: newforms (sharing the Nebentypus eigenspace `modFormCharSpace k χ`) with equal
  labels are Galois conjugate *and* have Galois-conjugate Nebentypus characters.  Proved by the
  dual composition: the dot-separated label string is parsed back into its `a`- and
  `x`-components (the letter labels are dot-free, `letterEncode_dot_not_mem`), and Phase 1's
  `charOrbitLabel_injOn_orbits` / Phase 2's `newformOrbitLabel_injOn_orbits` conclude the two
  conjugacies.  It carries the same hypotheses Phase 2's injectivity does.
-/

open scoped BigOperators

noncomputable section

namespace HeckeRing.GL2.Newform

open HeckeRing.GL2 CongruenceSubgroup LeanModularForms.Labels

variable {N : ℕ} [NeZero N] {k : ℤ}

/-! ### The Nebentypus character of a newform -/

/-- The **Nebentypus character** of a newform, as a Mathlib `DirichletCharacter ℂ N`.

A `Newform N k` carries its Nebentypus character `f.χ : (ZMod N)ˣ →* ℂˣ` (the `Eigenform`
field, with `f.toCuspForm.toModularForm' ∈ modFormCharSpace k f.χ`); this is its canonical
extension-by-zero to a `DirichletCharacter` via `Newform.dirichletLift = MulChar.ofUnitHom`. -/
noncomputable def newformChar (f : Newform N k) : DirichletCharacter ℂ N :=
  Newform.dirichletLift f.χ

@[simp] lemma newformChar_def (f : Newform N k) :
    newformChar f = Newform.dirichletLift f.χ := rfl

/-- The underlying form of a newform lies in the Nebentypus eigenspace of its character. -/
lemma toModularForm'_mem_modFormCharSpace (f : Newform N k) :
    f.toCuspForm.toModularForm' ∈ modFormCharSpace k f.χ :=
  f.mem_charSpace

/-! ### The full label `N.k.a.x` -/

variable [Fintype (Newform N k)]

/-- The full **LMFDB newform label** `N.k.a.x` of a newform `f`: the level `N`, the weight `k`,
the Dirichlet-character Galois-orbit label `a` of the Nebentypus character of `f`, and the
newform Galois(Hecke)-orbit label `x`, joined by `.`.

The character label `a` and form label `x` are read from `Labels/CharacterOrbit.lean` (Phase 1)
and `Labels/NewformOrbit.lean` (Phase 2) respectively; both are base-`26` letter strings. -/
noncomputable def lmfdbLabel (f : Newform N k) : String :=
  s!"{N}.{k}.{DirichletCharacter.charOrbitLabel (newformChar f)}.{newformOrbitLabel f}"

/-- The label expanded as an explicit `String` concatenation (the desugaring of the
interpolation `s!"{N}.{k}.{a}.{x}"`). -/
lemma lmfdbLabel_eq_append (f : Newform N k) :
    lmfdbLabel f = toString N ++ "." ++ toString k ++ "." ++
      DirichletCharacter.charOrbitLabel (newformChar f) ++ "." ++ newformOrbitLabel f := rfl

/-! ### Canonicity: the label is constant on the Galois orbit (the deliverable) -/

/-- **The full LMFDB label is constant on the Galois orbit of `f`** (canonicity /
well-definedness).

If `f` and `g` are Galois-conjugate newforms (`IsGaloisConj f g`) whose Nebentypus characters
are Galois-conjugate as Dirichlet characters (`hχ`), then they receive the *same* LMFDB label.

The proof composes the two component-level invariances:
* the `a`-component via Phase 1's `DirichletCharacter.charOrbitLabel_eq_of_isGaloisConj hχ`;
* the `x`-component via Phase 2's `Newform.newformOrbitLabel_eq_of_isGaloisConj h`.

The hypothesis `hχ` (that Galois conjugation carries `χ_f` to a Galois-conjugate character) is
the standard fact that `σf` is again a newform with Nebentypus `σ ∘ χ_f`; it is the same deep
character-stability input left abstract throughout `Labels/NewformOrbit.lean` (whose
`IsGaloisConj` only constrains the Fourier coefficients), and is supplied here as a hypothesis
rather than re-derived. -/
theorem lmfdbLabel_eq_of_isGaloisConj {f g : Newform N k}
    (hχ : DirichletCharacter.IsGaloisConj (newformChar f) (newformChar g))
    (h : IsGaloisConj f g) :
    lmfdbLabel f = lmfdbLabel g := by
  unfold lmfdbLabel
  rw [DirichletCharacter.charOrbitLabel_eq_of_isGaloisConj hχ,
    newformOrbitLabel_eq_of_isGaloisConj h]

/-! ### Injectivity on orbits

The label is also *injective on distinct orbits*: equal labels force both the Nebentypus
characters to be Galois-conjugate (Phase 1) and the newforms to be Galois-conjugate (Phase 2).
We recover the `a`- and `x`-components by parsing the dot-separated string, using that the
letter labels are dot-free.  This carries the same `χ`-eigenspace hypotheses as Phase 2's
injectivity `newformOrbitLabel_injOn_orbits`. -/

/-- The dot character `'.'` never occurs in an LMFDB letter label `letterEncode n` (whose
characters are exactly the lowercase letters `'a' = 97, …, 'z' = 122`). -/
lemma letterEncode_dot_not_mem (n : ℕ) : '.' ∉ (letterEncode n).toList := by
  intro hmem
  unfold letterEncode at hmem
  rw [String.toList_ofList, List.mem_map] at hmem
  obtain ⟨d, hd, heq⟩ := hmem
  have hd26 : d < 26 := Nat.toLetterDigits_lt_26 hd
  have hv : (97 + d).isValidChar := Or.inl (by omega)
  have hval : (digitToLetter d).toNat = 97 + d := by
    unfold digitToLetter; rw [Char.ofNat, dif_pos hv]; rfl
  rw [heq] at hval
  simp only [show ('.').toNat = 46 from rfl] at hval
  omega

/-- If two lists over `α` are split by a separator `c` that occurs in neither prefix, the
prefixes and suffixes agree.  (A list-level "split at the first separator" lemma.) -/
private theorem list_split_at_sep {α : Type*} (c : α) (a₁ a₂ x₁ x₂ : List α)
    (h₁ : c ∉ a₁) (h₂ : c ∉ a₂)
    (h : a₁ ++ c :: x₁ = a₂ ++ c :: x₂) : a₁ = a₂ ∧ x₁ = x₂ := by
  induction a₁ generalizing a₂ with
  | nil =>
    cases a₂ with
    | nil => simpa using h
    | cons b a₂' =>
      rw [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd h.1 (fun hb => h₂ (hb ▸ List.mem_cons_self))
  | cons b a₁' ih =>
    cases a₂ with
    | nil =>
      rw [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd h.1 (fun hb => h₁ (hb ▸ List.mem_cons_self))
    | cons d a₂' =>
      rw [List.cons_append, List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, hrest⟩ := h
      obtain ⟨he1, he2⟩ := ih a₂' (fun hm => h₁ (List.mem_cons_of_mem _ hm))
        (fun hm => h₂ (List.mem_cons_of_mem _ hm)) hrest
      exact ⟨by rw [he1], he2⟩

/-- String version of `list_split_at_sep` at the dot separator: if `a₁`, `a₂` are dot-free
strings and `a₁.x₁ = a₂.x₂`, then `a₁ = a₂` and `x₁ = x₂`. -/
private theorem string_split_at_dot (a₁ a₂ x₁ x₂ : String)
    (h₁ : '.' ∉ a₁.toList) (h₂ : '.' ∉ a₂.toList)
    (h : a₁ ++ "." ++ x₁ = a₂ ++ "." ++ x₂) : a₁ = a₂ ∧ x₁ = x₂ := by
  have hlist : a₁.toList ++ '.' :: x₁.toList = a₂.toList ++ '.' :: x₂.toList := by
    have := congrArg String.toList h
    simpa [String.toList_append] using this
  obtain ⟨he1, he2⟩ := list_split_at_sep '.' _ _ _ _ h₁ h₂ hlist
  exact ⟨String.toList_inj.mp he1, String.toList_inj.mp he2⟩

/-- **Splitting the full label.**  From equality of two full labels (with the *same* `N`, `k`)
recover equality of the `a`-components and of the `x`-components.

The common prefix `toString N ++ "." ++ toString k ++ "."` cancels by
`String.append_right_inj`, and the remaining `a.x = a'.x'` splits at the dot via
`string_split_at_dot` (the letter labels being dot-free, `letterEncode_dot_not_mem`). -/
lemma charLabel_eq_and_orbitLabel_eq_of_lmfdbLabel_eq {f g : Newform N k}
    (h : lmfdbLabel f = lmfdbLabel g) :
    DirichletCharacter.charOrbitLabel (newformChar f) =
        DirichletCharacter.charOrbitLabel (newformChar g) ∧
      newformOrbitLabel f = newformOrbitLabel g := by
  rw [lmfdbLabel_eq_append, lmfdbLabel_eq_append] at h
  -- regroup as `(common prefix) ++ (a ++ "." ++ x)`
  have hgroup : ∀ a x : String,
      toString N ++ "." ++ toString k ++ "." ++ a ++ "." ++ x =
        (toString N ++ "." ++ toString k ++ ".") ++ (a ++ "." ++ x) := by
    intro a x; simp only [String.append_assoc]
  rw [hgroup, hgroup] at h
  -- cancel the common `N.k.` prefix
  have h' := (String.append_right_inj _).mp h
  -- both `a`-components are letter labels, hence dot-free
  refine string_split_at_dot _ _ _ _ ?_ ?_ h'
  · rw [show DirichletCharacter.charOrbitLabel (newformChar f) =
      letterEncode (DirichletCharacter.orbitIndex (newformChar f)) from rfl]
    exact letterEncode_dot_not_mem _
  · rw [show DirichletCharacter.charOrbitLabel (newformChar g) =
      letterEncode (DirichletCharacter.orbitIndex (newformChar g)) from rfl]
    exact letterEncode_dot_not_mem _

/-- **The full LMFDB label is injective on distinct orbits.**  If two newforms sharing the
Nebentypus eigenspace `modFormCharSpace k χ` have the *same* LMFDB label, then their Nebentypus
characters are Galois-conjugate **and** the newforms themselves are Galois-conjugate.

This is the dual composition of the canonicity lemma: the label string is split back into its
`a`- and `x`-components (`charLabel_eq_and_orbitLabel_eq_of_lmfdbLabel_eq`), Phase 1's
`charOrbitLabel_injOn_orbits` concludes the character conjugacy, and Phase 2's
`newformOrbitLabel_injOn_orbits` concludes the newform conjugacy.  It carries the same
`χ`-eigenspace hypotheses (and the same residual separation input) as Phase 2's injectivity. -/
theorem lmfdbLabel_injOn_orbits {f g : Newform N k} (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (h : lmfdbLabel f = lmfdbLabel g) :
    DirichletCharacter.IsGaloisConj (newformChar f) (newformChar g) ∧ IsGaloisConj f g := by
  obtain ⟨ha, hx⟩ := charLabel_eq_and_orbitLabel_eq_of_lmfdbLabel_eq h
  exact ⟨DirichletCharacter.charOrbitLabel_injOn_orbits ha,
    newformOrbitLabel_injOn_orbits χ hfχ hgχ hx⟩

end HeckeRing.GL2.Newform
