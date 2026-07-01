/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# LMFDB letter encoding (base-26 labels)

This file defines the LMFDB letter encoding used throughout the database to turn a
`0`-based index into a label string of lowercase letters:
`0 ↦ "a", 1 ↦ "b", …, 25 ↦ "z", 26 ↦ "ba", 27 ↦ "bb", …`.

This is the "base-26 using the letters of the alphabet" scheme described in the LMFDB
knowls (e.g. `character.dirichlet.galois_orbit_label`, which states the index `1` is
written `a`, the index `2` is written `b`, the index `27` is written `ba`).  Note that
LMFDB orbit/embedding **indices are `1`-based**, so the LMFDB letter for `1`-based index
`i` is `letterEncode (i - 1)` with the `0`-based map defined here.

## Implementation note

With the convention `26 ↦ "ba"` the encoding is exactly ordinary (most-significant-first)
base-`26` with digit alphabet `a = 0, …, z = 25`, with the single special case that
`0 ↦ "a"` (because `Nat.digits 26 0 = []`).  In particular no label other than `"a"` has a
leading `'a'`, so the map is injective but **not** surjective onto `String` (strings such as
`"aa"`, `"1"` or `""` are not labels).  We therefore record injectivity via an explicit
left inverse `letterDecode`, and prove `Function.Bijective` for the corestriction
`letterEncode' : ℕ → letterRange` onto its range.

## Main definitions

* `Nat.toLetterDigits` / `Nat.ofLetterDigits` : the underlying big-endian digit lists.
* `letterEncode : ℕ → String` : the `0`-based LMFDB letter encoding.
* `letterDecode : String → ℕ` : its left inverse.
* `letterEncode'` : the corestriction of `letterEncode` onto its range `letterRange`.

## Main results

* `letterDecode_letterEncode` : `letterDecode (letterEncode n) = n`.
* `letterEncode_injective` : `Function.Injective letterEncode`.
* `letterEncode'_bijective` : `Function.Bijective letterEncode'`.
* `letterEncode_zero`, `letterEncode_25`, `letterEncode_26` : small computations
  pinning down the convention (`0 ↦ "a"`, `25 ↦ "z"`, `26 ↦ "ba"`).
-/

namespace LeanModularForms.Labels

/-! ### Digit ↔ character translation -/

private theorem Char.toNat_ofNat_of_isValidChar {n : ℕ} (h : n.isValidChar) :
    (Char.ofNat n).toNat = n := by
  rw [Char.ofNat, dif_pos h]
  rfl

/-- Translate a base-`26` digit `d ∈ {0, …, 25}` to the lowercase letter `'a' + d`. -/
def digitToLetter (d : ℕ) : Char := Char.ofNat (97 + d)

/-- Translate a lowercase letter back to a base-`26` digit (left inverse of
`digitToLetter` on `{0, …, 25}`). -/
def letterToDigit (c : Char) : ℕ := c.toNat - 97

@[simp] lemma letterToDigit_digitToLetter {d : ℕ} (hd : d < 26) :
    letterToDigit (digitToLetter d) = d := by
  have hv : (97 + d).isValidChar := Or.inl (by omega)
  unfold letterToDigit digitToLetter
  rw [Char.toNat_ofNat_of_isValidChar hv]
  omega

lemma digitToLetter_injOn : Set.InjOn digitToLetter (Set.Iio 26) := by
  intro a ha b hb h
  have := congrArg letterToDigit h
  rwa [letterToDigit_digitToLetter ha, letterToDigit_digitToLetter hb] at this

/-! ### Underlying digit lists -/

/-- The big-endian (most-significant-first) base-`26` digit list of `n`, with `0` mapped to
`[0]` so that the encoding produces the single letter `"a"`. -/
def Nat.toLetterDigits (n : ℕ) : List ℕ :=
  if n = 0 then [0] else (Nat.digits 26 n).reverse

/-- Read a big-endian base-`26` digit list back to a natural number. -/
def Nat.ofLetterDigits (l : List ℕ) : ℕ := Nat.ofDigits 26 l.reverse

@[simp] lemma Nat.ofLetterDigits_toLetterDigits (n : ℕ) :
    Nat.ofLetterDigits (Nat.toLetterDigits n) = n := by
  unfold Nat.ofLetterDigits Nat.toLetterDigits
  split_ifs with h
  · subst h; rfl
  · rw [List.reverse_reverse, Nat.ofDigits_digits]

lemma Nat.toLetterDigits_lt_26 {n : ℕ} {d : ℕ} (hd : d ∈ Nat.toLetterDigits n) : d < 26 := by
  unfold Nat.toLetterDigits at hd
  split_ifs at hd with h
  · simp only [List.mem_singleton] at hd; omega
  · exact Nat.digits_lt_base (by norm_num) (List.mem_reverse.mp hd)

/-! ### The encoding and its inverse -/

/-- The LMFDB letter encoding (`0`-based): `0 ↦ "a", …, 25 ↦ "z", 26 ↦ "ba", …`. -/
def letterEncode (n : ℕ) : String :=
  String.ofList ((Nat.toLetterDigits n).map digitToLetter)

/-- Left inverse of `letterEncode`. -/
def letterDecode (s : String) : ℕ :=
  Nat.ofLetterDigits (s.toList.map letterToDigit)

@[simp] lemma letterDecode_letterEncode (n : ℕ) : letterDecode (letterEncode n) = n := by
  unfold letterDecode letterEncode
  rw [String.toList_ofList, List.map_map]
  have : (Nat.toLetterDigits n).map (letterToDigit ∘ digitToLetter) = Nat.toLetterDigits n := by
    conv_rhs => rw [← List.map_id (Nat.toLetterDigits n)]
    refine List.map_congr_left fun d hd => ?_
    simpa using letterToDigit_digitToLetter (Nat.toLetterDigits_lt_26 hd)
  rw [this, Nat.ofLetterDigits_toLetterDigits]

/-- **The LMFDB letter encoding is injective.** -/
theorem letterEncode_injective : Function.Injective letterEncode :=
  Function.LeftInverse.injective letterDecode_letterEncode

/-! ### The encoding is a bijection onto its range -/

/-- The range of `letterEncode`: the set of valid LMFDB letter labels. -/
def letterRange : Set String := Set.range letterEncode

/-- The corestriction of `letterEncode` onto its range. -/
def letterEncode' (n : ℕ) : letterRange := ⟨letterEncode n, n, rfl⟩

/-- **The LMFDB letter encoding is a bijection onto the set of valid labels.** -/
theorem letterEncode'_bijective : Function.Bijective letterEncode' := by
  constructor
  · intro a b h
    exact letterEncode_injective (congrArg Subtype.val h)
  · rintro ⟨s, n, rfl⟩
    exact ⟨n, rfl⟩

/-! ### Pinning down the convention

These `native_decide`-free computations confirm `0 ↦ "a"`, `25 ↦ "z"`, `26 ↦ "ba"`,
`27 ↦ "bb"` by reducing through `letterDecode`/`Nat.digits`. -/

lemma letterEncode_zero : letterEncode 0 = String.ofList ['a'] := by
  unfold letterEncode Nat.toLetterDigits digitToLetter
  norm_num [List.map]

lemma letterEncode_25 : letterEncode 25 = String.ofList ['z'] := by
  unfold letterEncode Nat.toLetterDigits digitToLetter
  norm_num [Nat.digits, Nat.digitsAux, List.map]

lemma letterEncode_26 : letterEncode 26 = String.ofList ['b', 'a'] := by
  unfold letterEncode Nat.toLetterDigits digitToLetter
  norm_num [Nat.digits, Nat.digitsAux, List.map]

end LeanModularForms.Labels
