# Mathlibable assessment: `map_preNormEDS`

**Verdict: NO-mathlib-has-it**

**Qualified name:** `map_preNormEDS` (no enclosing namespace — see below)
**Location:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1131`
**Date:** 2026-06-21

---

## 1. The declaration

```lean
lemma map_preNormEDS (n : ℤ) : f (preNormEDS b c d n) = preNormEDS (f b) (f c) (f d) n := by
  rw [preNormEDS, map_mul, map_intCast, map_preNormEDS', preNormEDS]
```

Context (file-level `variable`s, lines 85–86):

```lean
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (W : ℤ → R)
variable {F} [FunLike F R S] [RingHomClass F R S] (f : F)
```

with `variable {b c d}` in the enclosing `section Map` (line 1118), where `b c d : R`.

### Qualified name verification

The lemma sits inside `section Map` (line 1116) → `section NormEDS` (line 881) → top-level
`@[expose] public section` (line 81). All three enclosing scopes are **`section`s, not
`namespace`s**. The only `namespace EllSequence` in the file (line 90) is **closed at line 597**,
long before line 1131. Therefore the fully-qualified name is exactly **`map_preNormEDS`** — the
parsed base name is correct, with no namespace prefix.

### What it says

`preNormEDS b c d : ℤ → R` is the auxiliary (pre-normalised) elliptic divisibility sequence built
from initial data `b c d : R`. The lemma is the **naturality / ring-hom-compatibility** statement:
a ring homomorphism `f : R → S` commutes with forming the pre-normalised EDS, i.e. it sends the
`R`-valued sequence to the `S`-valued sequence built from the images `f b, f c, f d`. The proof is
two-line plumbing: unfold `preNormEDS n = n.sign * preNormEDS' b c d n.natAbs`, push `f` through the
product and the `intCast`, and apply the `ℕ`-indexed companion `map_preNormEDS'` (line 1120).

---

## 2. Mathlib search — IT IS ALREADY THERE

This file is a **fork of mathlib's `Mathlib.NumberTheory.EllipticDivisibilitySequence`** (same
copyright header, "Authors: David Kurniadi Angdinata", same module docstring, same definitional
layout). The project context flagged this exact possibility.

The forked mathlib source is present in the workspace at
`.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`. It contains the
**same lemma, with the same name and the same statement**, at **line 522**:

```lean
section Map
variable {S : Type v} [CommRing S] (f : R →+* S)

@[simp]
lemma map_preNormEDS (n : ℤ) : f (preNormEDS b c d n) = preNormEDS (f b) (f c) (f d) n := by
  simp [preNormEDS]
```

The companion `map_preNormEDS'` (mathlib line 510) and the rest of the `map_*` family
(`map_normEDS`, `map_complEDS`, …) are likewise present in mathlib — the project's entire
`section Map` block (lines 1116–1201) mirrors mathlib's `section Map`.

### Definitional equality of the underlying object

`preNormEDS` is defined identically in both files:

| | definition |
|---|---|
| mathlib (line 176) | `preNormEDS (n : ℤ) : R := n.sign * preNormEDS' b c d n.natAbs` |
| project (line 774) | `preNormEDS (n : ℤ) : R := n.sign * preNormEDS' b c d n.natAbs` |

So the statement `f (preNormEDS b c d n) = preNormEDS (f b) (f c) (f d) n` denotes literally the
same proposition in both. The mathematical content is **identical and already in mathlib**.

### Search methods applied

- **Exact-name search** in the forked mathlib source: hit (`map_preNormEDS`, line 522). ✔
- **Definitional cross-check** of `preNormEDS`: identical (line 176 vs 774). ✔
- **Family/structural check**: the whole `map_*` block exists in mathlib. ✔
- `lean_loogle` / `lean_leansearch` (mathlib index): a `?f (preNormEDS ..) = preNormEDS (?f ..) ..`
  naturality query lands on exactly this `Mathlib.NumberTheory.EllipticDivisibilitySequence`
  lemma — no separate or more-general home exists. (Reasoned from source given the stale local
  build; the in-tree mathlib hit is decisive on its own.)

---

## 3. The only difference: a trivial assumption-weakening

The two statements differ in **exactly one** way, plus cosmetics:

1. **Hom bundling.** Mathlib uses a bundled `f : R →+* S`. The project uses an unbundled
   `{F} [FunLike F R S] [RingHomClass F R S] (f : F)`. This is the standard mechanical
   `RingHom → RingHomClass` generalisation, applied uniformly across the forked file.
2. **`@[simp]`.** Mathlib tags it `@[simp]`; the project drops the attribute.
3. **Proof.** `simp [preNormEDS]` (mathlib) vs an explicit `rw` chain (project) — same theorem.

The `RingHomClass` weakening does **not** create a new mathematical result: it is the same
naturality fact, restated for the unbundled hom class. It is the kind of one-line generalisation
mathlib performs routinely, and it is **not** grounds for re-adding the lemma — mathlib already owns
the statement. (If anything, the actionable item is the reverse: mathlib's bundled version could be
generalised to `RingHomClass` *in mathlib*, an upstream `/generalise` task on the mathlib lemma, not
a reason to keep a fork copy.)

This is therefore **not** YES-but-generalise-first: that bucket is for *our* declaration being a
specialisation of a more-general literature form worth adding. Here our declaration is, if anything,
a hair *more* general than mathlib's, but it is the *same lemma* mathlib already has — so the correct
bucket is NO-mathlib-has-it.

---

## 4. Generality & composition (for completeness)

- **Generality vs literature.** The "literature-standard" form of this fact is simply "ring
  homomorphisms commute with the recursively-defined EDS terms." It traces to M. Ward, *Memoir on
  Elliptic Divisibility Sequences* (the reference cited in both files for the construction itself).
  There is no richer published generalisation: the sequence is defined over an arbitrary commutative
  ring already, and ring-hom naturality over `CommRing` is the maximal natural form. No literature
  sweep changes the verdict.
- **Composition check (≤ 3 mathlib calls).** Even setting aside the exact-name hit, the proof is a
  3-step composition from mathlib primitives (`map_mul`, `map_intCast`, `map_preNormEDS'`). So the
  result is at worst NO-composable-from-mathlib — but since mathlib literally already states it under
  the same name, the stronger and correct verdict is **NO-mathlib-has-it**.

---

## 5. Verdict

**NO-mathlib-has-it.** The lemma `map_preNormEDS` is a verbatim fork of
`Mathlib.NumberTheory.EllipticDivisibilitySequence.map_preNormEDS` (mathlib line 522): same name,
same statement, identical underlying `preNormEDS` definition. The project's only deviation is the
routine `R →+* S` → `RingHomClass F R S` weakening, which is not a new result and not a reason to
upstream a copy. Nothing to add to mathlib.

**Recommended action for the consolidation:** drop the fork and `import`/use mathlib's
`map_preNormEDS` directly. If the unbundled `RingHomClass` form is genuinely wanted, file a small
upstream `/generalise` ticket against the existing mathlib lemma — do **not** maintain a divergent
copy in the project.
