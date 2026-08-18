# Mathlibable assessment — `map_preNormEDS'`

**Verdict: `NO-mathlib-has-it`**

**Qualified name:** `map_preNormEDS'` (root namespace; inside `section Map`)
**Source:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1120`
**Date:** 2026-06-21
**Mathlib pin:** `09b373db6e24` (2026-06-21), toolchain v4.32.0-rc1

---

## 1. The declaration (verified from source)

```lean
-- projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1116–1129
section Map
variable {b c d}   -- b c d : R   [CommRing R]
-- ambient (lines 85–86):
--   variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
--   variable {F} [FunLike F R S] [RingHomClass F R S] (f : F)

lemma map_preNormEDS' (n : ℕ) :
    f (preNormEDS' b c d n) = preNormEDS' (f b) (f c) (f d) n := by
  induction n using normEDSRec' with
  | zero  => rw [preNormEDS'_zero,  map_zero, preNormEDS'_zero]
  | one   => rw [preNormEDS'_one,   map_one,  preNormEDS'_one]
  | two   => rw [preNormEDS'_two,   map_one,  preNormEDS'_two]
  | three => rw [preNormEDS'_three, preNormEDS'_three]
  | four  => rw [preNormEDS'_four,  preNormEDS'_four]
  | _ _ ih =>
    simp only [preNormEDS'_odd, preNormEDS'_even, map_one, map_sub,
      map_mul, map_pow, apply_ite f]
    repeat rw [ih _ <| by linarith only]
```

**Math content.** `preNormEDS' b c d n` is the ℕ-indexed auxiliary sequence for a normalised
elliptic divisibility sequence over a commutative ring `R`, defined by the EDS recursion from
seeds `(0,1,1,c,d)` with the extra parameter `b`. The lemma states the obvious functoriality:
a ring homomorphism `f : R → S` commutes with `preNormEDS'`, i.e.
`f (preNormEDS' b c d n) = preNormEDS' (f b) (f c) (f d) n`. The proof is a routine
`normEDSRec'` induction pushing `f` through the recursion (`map_zero/one/sub/mul/pow`,
`apply_ite`). Used downstream for `map_preNormEDS`, `map_normEDS`, `map_compl₂EDS`, and in
`DivisionPolynomial.lean` (`preΨ'`).

This is **not** a deep theorem; it is naturality / `map_*`-style boilerplate. Its mathlibability
hinges entirely on whether mathlib already has it.

## 2. Mathlib search — IT IS ALREADY THERE (verbatim)

This project file is an explicit **fork** of the mathlib file
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (same copyright header,
"Authors: David Kurniadi Angdinata", line 4; the prompt flags the fork and duplicated
General*/PID* tracks).

The pinned mathlib already contains the identical lemma:

```lean
-- .lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:505–519
section Map
variable {S : Type v} [CommRing S] (f : R →+* S)

@[simp]
lemma map_preNormEDS' (n : ℕ) :
    f (preNormEDS' b c d n) = preNormEDS' (f b) (f c) (f d) n := by
  induction n using normEDSRec' with
  | zero => simp
  | one => simp
  | two => simp
  | three => simp
  | four => simp
  | _ _ ih =>
    simp only [preNormEDS'_even, preNormEDS'_odd, apply_ite f, map_pow, map_mul, map_sub, map_one]
    repeat rw [ih _ <| by linarith only]
```

Search methods used:
1. **grep on the pinned mathlib source** — `map_preNormEDS'` found at line 510 of
   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`. Statement is **identical**
   (same name, same conclusion, same `preNormEDS'` over `[CommRing R]`, `b c d : R`).
2. **leansearch / loogle** — index is the same upstream mathlib; the lemma is the canonical
   `map_preNormEDS'`. The direct source hit makes the index lookup redundant.
3. **WebSearch** — mathlib4 docs page `Mathlib.NumberTheory.EllipticDivisibilitySequence`
   is the canonical home of `preNormEDS'` / `map_preNormEDS*`, joint work with
   D.K. Angdinata (the file's author). Confirms upstream ownership.
4. The whole project `section Map` (lines 1116–1170) mirrors mathlib's `section Map`
   (lines 505–547): `map_preNormEDS`, `map_normEDS`, `map_complEDS₂`/`map_compl₂EDS` all
   present upstream.
5. `DivisionPolynomial/Basic.lean` upstream already consumes `map_preNormEDS'` / `map_preNormEDS`
   (lines 439, 515), confirming these are load-bearing, established mathlib API.

## 3. Generality analysis (fork vs. upstream)

Only **cosmetic / packaging** differences exist — no new mathematical content:

| Aspect | Mathlib (upstream) | Project (fork) |
|---|---|---|
| Hom argument | `f : R →+* S` (bundled `RingHom`) | `(f : F)` with `[FunLike F R S] [RingHomClass F R S]` |
| Attribute | `@[simp]` | none |
| Proof | `simp`-heavy | slightly more explicit `rw` |
| Statement | identical | identical |

The project uses the **unbundled `RingHomClass` spread**, which is *marginally more general* in
the variable `f` (it accepts any `F` that is a `RingHomClass`, e.g. `AlgHom`, `RingEquiv`,
without `.toRingHom`). But:
- This is **not new mathematics** — `RingHomClass.toRingHom` makes the two interchangeable;
  the bundled form is recovered instantly, and any `RingHomClass` use-site can apply the
  bundled lemma to `(f : R →+* S)` via the coercion.
- Whether mathlib's `map_*` lemmas should be stated bundled (`→+*`) or via `RingHomClass` is a
  **library-wide stylistic policy choice**, not a reason to re-add this specific lemma. Mathlib's
  EDS API is deliberately stated with `R →+* S`. Converting that whole API to `RingHomClass`
  would be a generalisation PR *against mathlib*, not a contribution *of a missing result*.

So this does not even qualify as `YES-but-generalise-first`: the result (and its essentially-
equivalent generalisation) is already in mathlib.

## 4. Composition check

Not applicable in the usual sense (it is not a one-off corollary), but worth noting: even if it
were absent, it is ≤ 1 mathlib call — `exact map_preNormEDS' (f := (f : R →+* S)) ..` plus the
`RingHomClass` coercion — i.e. trivially recovered from the existing mathlib lemma. This further
confirms there is nothing to add.

## 5. Verdict

**`NO-mathlib-has-it`.** The lemma `map_preNormEDS'` is a verbatim fork of
`Mathlib.NumberTheory.EllipticDivisibilitySequence.map_preNormEDS'`
(`.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:510`), present in
the currently-pinned mathlib (`09b373db6e24`). Identical statement; the project differs only by a
cosmetic `RingHomClass` spread vs. bundled `R →+* S` and a missing `@[simp]`. No new mathematics,
nothing to upstream. This is exactly the duplicated-mathlib-track situation the project context
warned about; the project copy should eventually be deleted in favour of `import`ing mathlib.

**Sources:**
- [Mathlib.NumberTheory.EllipticDivisibilitySequence (mathlib4 docs)](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EllipticDivisibilitySequence.html)
- [Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic (mathlib4 docs)](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.html)
- Local pinned source: `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:505–519`
