# Mathlibable assessment: `EllSequence.map_compl'`

**Verdict: YES-but-generalise-first**

**Qualified name:** `EllSequence.map_compl'`
(Source: `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1140`. Declared as
`lemma EllSequence.map_compl'` inside `section Map` — the enclosing `namespace EllSequence`
closed at L1112 — so the fully-qualified name is exactly `EllSequence.map_compl'`.)

---

## 1. Exact statement (from source, L1140–1150)

```lean
lemma EllSequence.map_compl' (W₁ compl₂ : ℤ → R) (m : ℤ) (n : ℕ) :
    f (compl' W₁ compl₂ m n) = compl' (f ∘ W₁) (f ∘ compl₂) m n := by
  refine n.strong_induction_on fun n ih ↦ ?_
  obtain _|_|n := n
  iterate 2 simp [compl']
  rw [compl']; conv_rhs => rw [compl']
  split_ifs with hn
  · rw [map_mul, ih _ (by omega)]; rfl
  simp_rw [map_sub, map_mul, map_pow]
  rw [ih _ (by omega), ih]; · rfl
  · have := (Nat.not_even_iff_odd.mp hn).pos; omega
```

Here `f : F` with `[FunLike F R S] [RingHomClass F R S]` (a ring hom `R → S`), and
`EllSequence.compl' W₁ compl₂ m : ℕ → R` (L1085) is a **division-free, strong-recursive**
construction of the sequence representing `W(n·m)/W(m)`, built from **two arbitrary input
sequences** `W₁ compl₂ : ℤ → R` (intended: `W₁ = W(·)/W(1)` and `compl₂ = W(2·)/W(·)`).

This is a pure `map_*` functoriality lemma: pushing a ring hom through the recursion. The
proof is mechanical (strong induction + `map_mul`/`map_sub`/`map_pow`/`apply_ite`/`rfl`).
No `sorry`; depends only on mathlib (`RingHomClass`, `Nat.strong_induction_on`,
`Nat.not_even_iff_odd`) and the project's own `compl'`.

---

## 2. Mathlib search (five methods)

This file is a **fork of `Mathlib.NumberTheory.EllipticDivisibilitySequence`** — identical
copyright header ("Authors: David Kurniadi Angdinata"), identical `IsEllSequence` /
`preNormEDS` / `normEDS` / `complEDS₂` API. The relevant mathlib file is
`.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`.

**Mathlib already contains the specialized analogue.** L388–400 define
`complEDS' b c d k : ℕ → R` — "the complement sequence `Wᶜ` for a normalised EDS `W` that
witnesses `W(k) ∣ W(n*k)`" — by the **same recursion**, but with the two input sequences
**hardcoded** to `normEDS b c d` and `complEDS₂ b c d`. And L533–535 give the matching
functoriality lemma:

```lean
@[simp] lemma map_complEDS' (k : ℤ) (n : ℕ) :
    f (complEDS' b c d k n) = complEDS' (f b) (f c) (f d) k n
```

plus `map_complEDS`, `map_complEDS₂`, `map_normEDS`, `map_preNormEDS'`, `map_preNormEDS`
(L510–545). All `@[simp]`.

- **exact?/loogle/leansearch shape:** the *concept* `map_complEDS'` is present; a
  parametrized `EllSequence.compl'` / `map_compl'` (abstracting over the two input
  sequences) is **not** in mathlib. `grep` for `compl'`, `namespace EllSequence`,
  `(W₁`, `f ∘ W` in mathlib's EDS file returns nothing.
- **Relationship:** the fork **generalizes** `complEDS'` → `EllSequence.compl'` by abstracting
  the two hardcoded sequences into parameters `W₁ compl₂`, then recovers the concrete one as
  `EllSequence.complEDS b c d m := compl (normEDS b c d) (compl₂EDS b c d) m` (L1110).
  Thus mathlib's `complEDS' b c d k = compl' (normEDS b c d) (complEDS₂ b c d) k`, and
  mathlib's `map_complEDS'` is the **specialization** of `EllSequence.map_compl'`.

Conclusion: **`map_compl'` is strictly more general than mathlib's existing `map_complEDS'`**,
obtained by parametrizing the recursion's two input sequences.

## 3. Literature / generality analysis

WebSearch (EDS complement sequences, division polynomials, ring homomorphisms) and the
mathlib docs confirm the EDS complement is treated **concretely** in the literature — via
division polynomials / the normalised EDS `normEDS` (Wikipedia; Silverman/Stange-style
treatments; mathlib docs). The "abstract recursion over two arbitrary input sequences
`W₁`, `compl₂`" is a **Lean-engineering abstraction** (factor the recursion so it can later be
applied through `aeval` to the universal `MvPolynomial Param ℤ` EDS — see `universalNormEDS`,
`complEDS_eq_aeval` at L1186–1199), **not** a named mathematical object. So there is no
"more standard / maximally general literature form" beyond simply parametrizing the inputs,
which the fork already does. The generalization is sound and is the right level.

## 4. Composition check (≤3 mathlib calls?)

No. `compl'` is a custom binary-pattern strong recursion that is **not** definitionally any
single mathlib term, so `map_compl'` cannot be discharged by composing a constant number of
existing mathlib lemmas — it needs its own induction over that recursion (exactly the proof
given). It is, however, *mechanically* the same proof as mathlib's `map_complEDS'`; only the
two input sequences differ. So it is not "composable from mathlib primitives", but it is also
not novel mathematics — it is the generalized restatement of a lemma mathlib already proves.

## 5. Verdict rationale → YES-but-generalise-first

- **Not NO-mathlib-has-it:** mathlib's `map_complEDS'` is the *specialized* version (inputs
  fixed to `normEDS`/`complEDS₂`); `map_compl'` covers strictly more (arbitrary `W₁`,
  `compl₂`), e.g. unnormalised or universal-polynomial sequences.
- **Not NO-composable:** it requires its own induction, not a ≤3-lemma composition.
- **Not YES-add-as-is:** adding it under a fresh `EllSequence.compl'` namespace would
  **duplicate** mathlib's existing `complEDS'`/`map_complEDS'` concept. The correct move is to
  **generalize mathlib's own `complEDS'` (and the whole `map_complEDS'`/`map_complEDS` family)
  to take the two parameter sequences**, then re-derive `complEDS'` as the special case — which
  is precisely the abstraction this fork performs across the file (`compl'` → `complEDS`,
  `map_compl'` → `map_complEDS`). `map_compl'` should land as part of that generalization of
  the existing API, not as a parallel duplicate. It would carry `@[simp]` like its mathlib
  siblings.
- **Not BORDERLINE:** the right action is unambiguous (generalize the existing mathlib def +
  lemma); only a routine naming/namespace decision (likely keep mathlib's `complEDS'` spelling
  with sequence args, rather than a new `EllSequence.compl'`) needs a maintainer's nod.

**Recommendation:** upstream as the generalization of `Mathlib.NumberTheory.\
EllipticDivisibilitySequence.complEDS'` / `map_complEDS'` — abstract the two input sequences
into explicit parameters, prove `map_compl'` over the general recursion (this proof), and
recover the current concrete `complEDS'`/`map_complEDS'` as the `normEDS`/`complEDS₂`
specialization (a one-line corollary).
