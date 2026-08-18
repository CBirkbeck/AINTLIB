# Mathlibable assessment — `map_complEDS_root`

**Verdict: NO-mathlib-has-it**

## Declaration

- **Qualified name:** `map_complEDS_root` (no enclosing namespace — see naming note)
- **Source:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1668`, in
  `section Map` (opened line 1646, closed line 1672). All `namespace EllSequence` /
  `IsEllSequence` / `HaveSameParity₄` blocks close before line 1524, and `section` introduces no
  namespace, so the lemma lives in the root namespace.

```lean
section Map
variable {R : Type u} [CommRing R] (b c d : R) {S : Type v} [CommRing S] (f : R →+* S)

@[simp]
lemma map_complEDS_root (k n : ℤ) :
    f (complEDS b c d k n) = complEDS (f b) (f c) (f d) k n := by
  simp [complEDS]
```

Here `complEDS` is the ℤ-indexed complement sequence of a normalised EDS, defined (line 1568) as
`complEDS b c d k n = n.sign * complEDS' b c d k n.natAbs`. The lemma states that any ring
homomorphism `f : R →+* S` commutes with this sequence (a naturality / base-change statement).

### Naming note (the `_root` suffix)
The `_root` suffix is **disambiguation, not new mathematics**. This file defines `complEDS`
**twice**: once at line 1110 (`def complEDS := EllSequence.compl (normEDS b c d) …`, inside the
`@[expose] public` block) and once at line 1568 (the `n.sign * complEDS'` version, in
`section ComplEDS`). The line-1110 version already owns the name `map_complEDS` (line 1156), so the
line-1568 version's map lemma was named `map_complEDS_root` to avoid a clash. Both `complEDS`
definitions are the same mathematical object (the complement sequence); the file is mid-deduplication
between two formalisation tracks.

## 1. Literature search

The "complement sequence" `Wᶜ(k,n)` with `W(k)·Wᶜ(k,n) = W(nk)` is an internal construction used to
prove divisibility properties of elliptic divisibility sequences (Ward 1948; Shipsey 2000; Silverman,
*The Arithmetic of Elliptic Curves*). It is auxiliary scaffolding, not a named object in the
literature. "A ring map commutes with the complement sequence" is a base-change triviality, not a
citable theorem. No literature sweep is warranted (small, mechanical decl); the decisive evidence is
the mathlib search below.

## 2. Mathlib search (the decisive step)

**Mathlib already contains this exact lemma, statement-for-statement and proof-for-proof.**

`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:544` (mathlib pinned at rev `09b373db6e24`,
the require in this repo's `lakefile.toml`):

```lean
section Map
variable {S : Type v} [CommRing S] (f : R →+* S)

@[simp]
lemma map_complEDS (k n : ℤ) : f (complEDS b c d k n) = complEDS (f b) (f c) (f d) k n := by
  simp [complEDS]
```

Side-by-side:

| | mathlib `map_complEDS` | project `map_complEDS_root` |
|---|---|---|
| Statement | `f (complEDS b c d k n) = complEDS (f b) (f c) (f d) k n` | identical |
| Hypotheses | `[CommRing R] [CommRing S] (f : R →+* S)` | identical |
| Proof | `by simp [complEDS]` | `by simp [complEDS]` |
| Attribute | `@[simp]` | `@[simp]` |
| Underlying `complEDS` | `n.sign * complEDS' b c d k n.natAbs` (line 427) | `n.sign * complEDS' b c d k n.natAbs` (line 1568) |

This is not a coincidental match: the project's `section ComplEDS` + `section Map`
(lines 1524–1672) are a **verbatim fork** of mathlib's `section ComplEDS` + `section Map`
(lines 384–547). Every supporting declaration is duplicated identically — `complEDS₂`, `complEDS'`,
`complEDS`, `complEDS_ofNat`, `complEDS_neg`, `complEDS_even`, `complEDS_odd`, `complEDSRec'`,
`complEDSRec`, `map_complEDS₂`, `map_normEDS`, `map_complEDS'`.

Search methods applied:
1. **Exact-name grep** across all of mathlib: `def complEDS` / `map_complEDS` appears **only** in
   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` → that is the upstream of this fork.
2. **Statement read** of that file: lemma present at line 544 (above).
3. `lean_loogle` / `lean_leansearch` are consistent with this (mathlib's `map_complEDS` is the
   canonical hit for `f (complEDS …) = complEDS (f …) …`); the local grep already gives certainty.

## 3. Generality analysis

No generalisation gap. The mathlib lemma is at the natural level: arbitrary commutative rings `R`,
`S` and an arbitrary ring hom `f : R →+* S`. The statement *is* the maximal sensible form (`complEDS`
is only defined over a `CommRing`, and `→+*` is the right morphism class). The project lemma matches
it exactly. There is no "more general mathlib form to weaken to" beyond what mathlib already states.

## 4. Composition check

Even setting aside the verbatim duplicate, the lemma is a one-line consequence of mathlib primitives:
`simp [complEDS]` unfolds `complEDS = n.sign * complEDS' …` and closes via `map_mul`, `map_intCast`
(for `↑n.sign`), and the already-upstream `map_complEDS'`. So it is also trivially ≤3-mathlib-call
composable. But that is moot: the identical lemma is already an upstream `@[simp]` lemma.

## 5. Verdict

**NO-mathlib-has-it.**

`map_complEDS_root` is `Mathlib.NumberTheory.EllipticDivisibilitySequence`'s `map_complEDS`
(rev `09b373db6e24`, line 544) under a disambiguating rename. Same statement, same hypotheses, same
proof, same `@[simp]` attribute, same surrounding API. It is a duplicate carried by this project's
fork of the mathlib EDS file, not a new contribution.

**Action:** do not submit. During the planned NagellLutz↔mathlib deduplication, delete the forked
`section ComplEDS` + `section Map` (lines 1524–1672 of the project file) and `import
Mathlib.NumberTheory.EllipticDivisibilitySequence`, replacing call-sites of `map_complEDS_root`
with mathlib's `map_complEDS`. (The HasseWeil project carries a parallel copy of the same EDS API in
`projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean` — same dedup applies
there.)
