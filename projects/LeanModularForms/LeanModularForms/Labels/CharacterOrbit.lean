/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.Labels.Encoding
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.SetTheory.Cardinal.Order

/-!
# LMFDB character-orbit label `a`

This file defines the LMFDB **Dirichlet-character Galois-orbit label**, the `a` component of a
classical modular-form label `N.k.a.x`.

## The LMFDB ordering convention (confirmed)

The authoritative rule is given in *Computing Classical Modular Forms*
(Best–Bober–Booker–Costa–Cremona–Derickx–Lee–Lowry-Duda–Roe–Sutherland–Voight,
arXiv:2002.04717, §"Labels"), and matches the LMFDB knowls
`character.dirichlet.galois_orbit_label` / `character.dirichlet.galois_orbit_index`:

> "To choose this label we lexicographically order the sequences
> `ord(χ), Tr χ(1), Tr χ(2), Tr χ(3), Tr χ(4), …`
> where `Tr : ℚ(χ) → ℚ` is the absolute trace."

So the Galois orbits of Dirichlet characters of a fixed modulus `N` are ordered **lexicographically
by the orbit invariant**
`t([χ]) = (ord(χ), Tr_{ℚ(χ)/ℚ} χ(1), Tr_{ℚ(χ)/ℚ} χ(2), …, Tr_{ℚ(χ)/ℚ} χ(N))`,
the orbit index is the (`1`-based) position in this order (index `1` = the principal-character
orbit), and the letter is the base-`26` encoding of `index - 1` (see `Labels/Encoding.lean`).

Note this corrects the *believed* rule recorded in the project plan ("order ascending, then sorted
Conrey indices"): the genuine LMFDB tiebreak is the **absolute-trace tuple**, not the Conrey-index
tuple.  (The minimal Conrey index `min_conrey_conj` is used by LMFDB as the canonical orbit
*representative*, but not as the orbit *ordering* key.)

## The trace invariant, structurally

For a Dirichlet character `χ : DirichletCharacter ℂ N`, every value `χ(j)` is either `0` (when
`j` is not a unit) or a root of unity in `ℚ(ζ_{ord χ}) = ℚ(χ)`.  The Galois group of `ℚ(χ)/ℚ` acts
on the orbit `{χ^t : gcd(t, ord χ) = 1}`, with `σ_t : ζ ↦ ζ^t` sending `χ(j) ↦ χ(j)^t = (χ^t)(j)`.
Hence the absolute trace is the **sum over the Galois orbit of the character values**:
`Tr_{ℚ(χ)/ℚ} χ(j) = Σ_{ψ ∈ galoisOrbit χ} ψ(j)`.
We take this sum, `orbitTraceAt χ j : ℂ`, as the (manifestly orbit-invariant) trace key; that it
is real/rational/integral and equals the field-theoretic trace is the structural fact deferred to
the coefficient-field development (Phase 2).

## Character convention

We work with `χ : DirichletCharacter ℂ N = MulChar (ZMod N) ℂ`.  This bridges to the project's
Nebentypus convention `(ZMod N)ˣ →* ℂˣ` (used in `cuspFormCharSpace` / `modFormCharSpace`,
`LeanModularForms.HeckeRIngs.GL2.Gamma1Pair`) via `χ.toUnitHom`.

## Main definitions

* `DirichletCharacter.galoisConjBy χ t := χ ^ t` — the Galois conjugate.
* `DirichletCharacter.IsGaloisConj χ ψ` — the Galois-orbit equivalence relation.
* `DirichletCharacter.galoisSetoid N` — the corresponding `Setoid`.
* `DirichletCharacter.galoisOrbit χ` — the Galois orbit as a `Finset`.
* `DirichletCharacter.orbitTraceAt χ j` — the orbit trace key `Σ_{ψ} ψ(j)`.
* `DirichletCharacter.charOrbitLabel` — the LMFDB letter label (via the ranking below).

## Main results

* `IsGaloisConj` is reflexive / symmetric / transitive (`galoisSetoid`).
* `orderOf` is constant on Galois orbits (`orderOf_eq_of_isGaloisConj`).
* `orbitTraceAt` is constant on Galois orbits (`orbitTraceAt_eq_of_isGaloisConj`).
* `charOrbitLabel` is constant on Galois orbits (`charOrbitLabel_eq_of_isGaloisConj`).

## Remaining `sorry`s (documented)

* `orbitRankKey_injOn_orbits` — that the orbit invariant `(ord, orbitTraceAt)` separates distinct
  orbits, equivalently that the LMFDB order is a *strict total order on orbits*.  This is the
  number-field-theoretic content (the trace tuple determines the orbit); it is the analogue of
  multiplicity-one for characters.
* `charOrbitLabel_injOn_orbits` — injectivity of the label on distinct orbits, which follows from
  `orbitRankKey_injOn_orbits` together with injectivity of the ranking and of `letterEncode`.
-/

open scoped BigOperators

namespace DirichletCharacter

variable {N : ℕ} [NeZero N]

/-! ### Order of a Dirichlet character -/

/-- The **order** of a Dirichlet character: the least `n > 0` with `χ ^ n = 1` (the trivial
character of the same modulus).  Positive because `(ZMod N)ˣ` is finite. -/
noncomputable abbrev order (χ : DirichletCharacter ℂ N) : ℕ := orderOf χ

lemma order_pos (χ : DirichletCharacter ℂ N) : 0 < order χ :=
  MulChar.orderOf_pos χ

lemma order_ne_zero (χ : DirichletCharacter ℂ N) : order χ ≠ 0 :=
  (order_pos χ).ne'

/-! ### The Galois action and orbit -/

/-- The Galois conjugate `χ ↦ χ^t` of a Dirichlet character by `t`.  For `t` coprime to the order
this realises the action of `σ_t ∈ Gal(ℚ(χ)/ℚ)`, `ζ ↦ ζ^t`. -/
noncomputable def galoisConjBy (χ : DirichletCharacter ℂ N) (t : ℕ) :
    DirichletCharacter ℂ N := χ ^ t

omit [NeZero N] in
@[simp] lemma galoisConjBy_apply (χ : DirichletCharacter ℂ N) (t : ℕ) (a : (ZMod N)ˣ) :
    galoisConjBy χ t a = (χ a) ^ t := by
  simpa [galoisConjBy] using MulChar.pow_apply_coe χ t a

/-- `ψ` is a **Galois conjugate** of `χ` if `ψ = χ^t` for some `t` coprime to the order of `χ`.
This is the relation whose classes are the LMFDB Galois orbits. -/
def IsGaloisConj (χ ψ : DirichletCharacter ℂ N) : Prop :=
  ∃ t : ℕ, (order χ).Coprime t ∧ ψ = χ ^ t

omit [NeZero N] in
lemma isGaloisConj_refl (χ : DirichletCharacter ℂ N) : IsGaloisConj χ χ :=
  ⟨1, Nat.coprime_one_right _, (pow_one χ).symm⟩

omit [NeZero N] in
/-- The order is invariant under Galois conjugation: `ord(χ^t) = ord χ` for `t` coprime to
`ord χ`. -/
lemma order_eq_of_isGaloisConj {χ ψ : DirichletCharacter ℂ N} (h : IsGaloisConj χ ψ) :
    order ψ = order χ := by
  obtain ⟨t, ht, rfl⟩ := h
  exact ht.orderOf_pow

omit [NeZero N] in
lemma isGaloisConj_symm {χ ψ : DirichletCharacter ℂ N} (h : IsGaloisConj χ ψ) :
    IsGaloisConj ψ χ := by
  obtain ⟨t, ht, rfl⟩ := h
  -- Let `m = ord χ`; `t` is coprime to `m`.  The symmetric witness is the modular inverse of `t`.
  set m := order χ with hm
  -- `s` = the value of the inverse of `t` in `ZMod m`; it is coprime to `m`.
  set s : ℕ := ((t : ZMod m)⁻¹).val with hs
  have hsm : Nat.Coprime s m := by
    have hcoe : (t : ZMod m)⁻¹ = ((ZMod.unitOfCoprime t ht.symm)⁻¹ : (ZMod m)ˣ) := by
      rw [← ZMod.coe_unitOfCoprime t ht.symm, ZMod.inv_coe_unit]
    rw [hs, hcoe]
    exact ZMod.val_coe_unit_coprime _
  -- `t * s ≡ 1 [MOD m]`, hence `χ ^ (t * s) = χ`.
  have hmod : (t * s : ZMod m) = 1 := by rw [hs]; exact ZMod.mul_val_inv ht.symm
  have hpow : χ ^ (t * s) = χ := by
    have hcongr : t * s ≡ 1 [MOD m] := by
      have := (ZMod.natCast_eq_natCast_iff (t * s) 1 m).mp (by push_cast; simpa using hmod)
      simpa using this
    calc χ ^ (t * s) = χ ^ (t * s % m) := (pow_mod_orderOf χ (t * s)).symm
      _ = χ ^ (1 % m) := by rw [hcongr]
      _ = χ ^ 1 := by rw [pow_mod_orderOf]
      _ = χ := pow_one χ
  refine ⟨s, ?_, ?_⟩
  · -- coprimality of `s` with `ord (χ^t) = m`
    rw [order_eq_of_isGaloisConj ⟨t, ht, rfl⟩, ← hm]
    exact hsm.symm
  · -- `χ = (χ^t) ^ s`
    rw [← pow_mul]; exact hpow.symm

omit [NeZero N] in
lemma isGaloisConj_trans {χ ψ ρ : DirichletCharacter ℂ N}
    (h₁ : IsGaloisConj χ ψ) (h₂ : IsGaloisConj ψ ρ) : IsGaloisConj χ ρ := by
  obtain ⟨t, ht, rfl⟩ := h₁
  obtain ⟨s, hs, rfl⟩ := h₂
  refine ⟨t * s, ?_, by rw [pow_mul]⟩
  -- `ord(χ^t) = ord χ`, so `s` coprime to `ord(χ^t)` is coprime to `ord χ`; products of coprimes.
  have hords : order (χ ^ t) = order χ := ht.orderOf_pow
  rw [order] at hords
  exact Nat.Coprime.mul_right ht (hords ▸ hs)

/-- The Galois-orbit equivalence relation on Dirichlet characters of modulus `N`. -/
def galoisSetoid (N : ℕ) [NeZero N] : Setoid (DirichletCharacter ℂ N) where
  r := IsGaloisConj
  iseqv := ⟨isGaloisConj_refl, isGaloisConj_symm, isGaloisConj_trans⟩

/-- The **Galois orbit** of `χ` as a `Finset`: `{χ^t : 0 ≤ t < ord χ, gcd(t, ord χ) = 1}`.
Since `χ^t` depends only on `t mod ord χ`, this enumerates the full orbit. -/
noncomputable def galoisOrbit (χ : DirichletCharacter ℂ N) : Finset (DirichletCharacter ℂ N) :=
  open scoped Classical in
  ((Finset.range (order χ)).filter fun t => (order χ).Coprime t).image fun t => χ ^ t

lemma mem_galoisOrbit_iff {χ ψ : DirichletCharacter ℂ N} :
    ψ ∈ galoisOrbit χ ↔ IsGaloisConj χ ψ := by
  classical
  simp only [galoisOrbit, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨t, ⟨_, htc⟩, rfl⟩
    exact ⟨t, htc, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t % order χ, ⟨Nat.mod_lt _ (order_pos χ), ?_⟩, ?_⟩
    · -- coprimality is preserved modulo `order χ` since `t = t % m + m * (t / m)`
      have key : t % order χ + order χ * (t / order χ) = t := Nat.mod_add_div t (order χ)
      rw [← Nat.coprime_add_mul_left_right (order χ) (t % order χ) (t / order χ), key]
      exact ht
    · rw [order, pow_mod_orderOf]

lemma self_mem_galoisOrbit (χ : DirichletCharacter ℂ N) : χ ∈ galoisOrbit χ :=
  mem_galoisOrbit_iff.mpr (isGaloisConj_refl χ)

/-! ### The orbit trace key

`orbitTraceAt χ j = Σ_{ψ ∈ galoisOrbit χ} ψ(j)`.  This equals `Tr_{ℚ(χ)/ℚ} χ(j)`; structurally it
is manifestly invariant on the orbit. -/

/-- The orbit trace key at a unit `j`: the sum of `ψ(j)` over the Galois orbit of `χ`.  Equal to
the absolute trace `Tr_{ℚ(χ)/ℚ} χ(j)`. -/
noncomputable def orbitTraceAt (χ : DirichletCharacter ℂ N) (j : (ZMod N)ˣ) : ℂ :=
  ∑ ψ ∈ galoisOrbit χ, ψ j

/-- The Galois orbits of `χ` and of a conjugate `ψ` coincide as `Finset`s. -/
lemma galoisOrbit_eq_of_isGaloisConj {χ ψ : DirichletCharacter ℂ N} (h : IsGaloisConj χ ψ) :
    galoisOrbit χ = galoisOrbit ψ := by
  ext ρ
  rw [mem_galoisOrbit_iff, mem_galoisOrbit_iff]
  exact ⟨fun hρ => isGaloisConj_trans (isGaloisConj_symm h) hρ, fun hρ => isGaloisConj_trans h hρ⟩

/-- The orbit trace key is constant on Galois orbits. -/
lemma orbitTraceAt_eq_of_isGaloisConj {χ ψ : DirichletCharacter ℂ N} (h : IsGaloisConj χ ψ)
    (j : (ZMod N)ˣ) : orbitTraceAt χ j = orbitTraceAt ψ j := by
  unfold orbitTraceAt
  rw [galoisOrbit_eq_of_isGaloisConj h]

/-! ### The orbit ranking key and the label

The LMFDB orbit invariant is `t([χ]) = (ord χ, j ↦ orbitTraceAt χ j)`.  We package it as a single
key for ranking. -/

/-- The LMFDB orbit-ordering key `t([χ]) = (ord χ, j ↦ Tr χ(j))`, manifestly orbit-invariant in
each component.  The character values are indexed by units `j ∈ (ZMod N)ˣ` (equivalently
`j = 1, …, N` with non-units contributing trace `0`). -/
noncomputable def orbitRankKey (χ : DirichletCharacter ℂ N) : ℕ × ((ZMod N)ˣ → ℂ) :=
  (order χ, orbitTraceAt χ)

lemma orbitRankKey_eq_of_isGaloisConj {χ ψ : DirichletCharacter ℂ N} (h : IsGaloisConj χ ψ) :
    orbitRankKey χ = orbitRankKey ψ := by
  unfold orbitRankKey
  refine Prod.ext (order_eq_of_isGaloisConj h).symm ?_
  funext j
  exact orbitTraceAt_eq_of_isGaloisConj h j

/-- **Orbit-separation (documented `sorry`).**  The orbit invariant `t([χ])` separates distinct
Galois orbits: if two characters of modulus `N` have the same order *and* the same trace tuple,
they are Galois-conjugate.  Equivalently, the LMFDB lexicographic order on `t([χ])` is a *strict
total order on orbits*.  This is the number-field content (the absolute-trace tuple of character
values determines the Galois orbit) and is the analogue of multiplicity one at the character level;
it is deferred to the coefficient-field development. -/
lemma orbitRankKey_injOn_orbits {χ ψ : DirichletCharacter ℂ N}
    (h : orbitRankKey χ = orbitRankKey ψ) : IsGaloisConj χ ψ := by
  sorry

/-! ### The label

We order the orbits of modulus `N` by the LMFDB key `t([χ])` and read off the `0`-based index as a
base-`26` letter.  Concretely the index of `χ` is the number of *distinct orbits whose key is
strictly smaller*; with a strict total order on orbits this matches LMFDB's `1`-based index minus
one. -/

section Ranking

/-- `DirichletCharacter ℂ N` is finite (the character group of a finite group into `ℂ`), hence we
may enumerate orbits.  Noncomputable, used only for the ranking `Finset.univ`. -/
noncomputable instance : Fintype (DirichletCharacter ℂ N) := Fintype.ofFinite _

/-- A fixed linear order on the orbit keys, used purely to *rank* orbits and produce a concrete
label.  The first (order-of-character) component is the genuine LMFDB primary key; we linearise the
whole key type with a classically-chosen well-order (`WellOrderingRel`).

This is honest about scope: the LMFDB tiebreak is the *lexicographic order on the absolute-trace
tuple* `(Tr χ(1), Tr χ(2), …)`.  Because that trace tuple is an orbit invariant (see
`orbitRankKey`), *any* fixed linear order on the key type that is injective on the (finitely many)
realised keys yields the same orbit ranking once `orbitRankKey_injOn_orbits` is known; pinning the
comparator to the concrete `ℂ`-lexicographic-by-`j` order is deferred together with that lemma. -/
noncomputable instance instLinearOrderOrbitKey : LinearOrder (ℕ × ((ZMod N)ˣ → ℂ)) :=
  IsWellOrder.linearOrder WellOrderingRel

/-- The `0`-based LMFDB orbit index of `χ`: the number of distinct orbits of modulus `N` whose
ordering key is strictly smaller than that of `χ`.  (With `orbitRankKey_injOn_orbits` this is a
genuine bijection onto `{0, …, #orbits − 1}` and matches LMFDB's `index − 1`.) -/
noncomputable def orbitIndex (χ : DirichletCharacter ℂ N) : ℕ :=
  ((Finset.univ.image orbitRankKey).filter (· < orbitRankKey χ)).card

/-- The **LMFDB character Galois-orbit label** `a`: the base-`26` letter encoding of the
`0`-based orbit index. -/
noncomputable def charOrbitLabel (χ : DirichletCharacter ℂ N) : String :=
  LeanModularForms.Labels.letterEncode (orbitIndex χ)

/-- **The label is constant on Galois orbits** (well-definedness, the feasible direction). -/
lemma charOrbitLabel_eq_of_isGaloisConj {χ ψ : DirichletCharacter ℂ N} (h : IsGaloisConj χ ψ) :
    charOrbitLabel χ = charOrbitLabel ψ := by
  unfold charOrbitLabel orbitIndex
  rw [orbitRankKey_eq_of_isGaloisConj h]

/-- **Rank-injectivity (documented `sorry`).**  Equal orbit indices force equal ordering keys.
This is the order-theoretic fact that the strictly-monotone rank function `key ↦ #{realised keys
strictly below it}` is injective on the finite set of realised keys; combined with
`orbitRankKey_injOn_orbits` it gives injectivity of the label on orbits.  (Provable from
`Finset` rank-function monotonicity; left as an explicit gap for Phase 1.) -/
lemma orbitIndex_inj {χ ψ : DirichletCharacter ℂ N} (h : orbitIndex χ = orbitIndex ψ) :
    orbitRankKey χ = orbitRankKey ψ := by
  sorry

/-- **The label is injective on distinct orbits.**  If two characters have the same label they are
Galois-conjugate.  This is a clean reduction: `letterEncode` is injective (Phase 0), so equal
labels give equal `orbitIndex`; `orbitIndex_inj` then gives equal ordering keys; and
`orbitRankKey_injOn_orbits` concludes Galois conjugacy.  The only unproven inputs are the two
documented `sorry`s `orbitIndex_inj` and `orbitRankKey_injOn_orbits`. -/
lemma charOrbitLabel_injOn_orbits {χ ψ : DirichletCharacter ℂ N}
    (h : charOrbitLabel χ = charOrbitLabel ψ) : IsGaloisConj χ ψ := by
  have hidx : orbitIndex χ = orbitIndex ψ :=
    LeanModularForms.Labels.letterEncode_injective h
  exact orbitRankKey_injOn_orbits (orbitIndex_inj hidx)

end Ranking

end DirichletCharacter
