# Mathlibable assessment: `complEDS`

**Verdict: NO-mathlib-has-it**

**Qualified name:** `complEDS` (top-level / `_root_.complEDS`)

**Location in project:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1568`

**One-line rationale:** This declaration is character-for-character identical to upstream
mathlib's `complEDS` (same file, same author); the project file is a fork.

> NOTE: A previous version of this report (re)analysed `EllSequence.complEDS` at line **1110** (the
> abstract, namespaced variant). The `/overview` Step-9 target for this file is the **top-level**
> `complEDS` at line **1568**. This report assesses line 1568. Both land in NO-mathlib-has-it, but
> for different reasons — see §1's naming note.

---

## 1. The declaration under assessment

From `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean`, inside `section ComplEDS`
(lines 1524–1644) with **no enclosing namespace**, so the qualified name is the top-level
`complEDS`:

```lean
universe u
variable {R : Type u} [CommRing R] (b c d : R) (k : ℤ)

/-- The complement sequence `Wᶜ : ℤ × ℤ → R` for a normalised EDS `W : ℤ → R` that witnesses
`W(k) ∣ W(n * k)`. In other words, `W(k) * Wᶜ(k, n) = W(n * k)` for any `k, n ∈ ℤ`.

This extends `complEDS'` by defining its values at negative integers. -/
def complEDS (n : ℤ) : R :=
  n.sign * complEDS' b c d k n.natAbs
```

It is the ℤ-indexed extension of the ℕ-indexed `complEDS'` (line 1533), which is itself a
division-free recurrence built from `normEDS` and the 2-complement `complEDS₂`. Mathematically,
`complEDS b c d k n` is the **complement / quotient sequence** `W(n·k) / W(k)` for the normalised
EDS `W = normEDS b c d`, defined without ring division so that it makes sense over any commutative
ring `R`. The accompanying API in the project file (`complEDS_ofNat`, `complEDS_zero`,
`complEDS_one`, `complEDS_neg`, `complEDS_even`, `complEDS_odd`, recursors `complEDSRec'` /
`complEDSRec`, and `map_complEDS`) realises the witnessing identity `W(k) · complEDS(k,n) = W(n·k)`
and hence the divisibility `W(k) ∣ W(n·k)`.

### Naming note — there are TWO `complEDS` in this file

- **line 1110:** `def complEDS := compl (normEDS b c d) (compl₂EDS b c d) m` — this lives **inside
  `namespace EllSequence`** (lines 1079–1112), so it is `EllSequence.complEDS`. It is the *abstract*
  version, built from the generic `compl` combinator over arbitrary witness sequences.
- **line 1568 (this assessment):** the **top-level** `complEDS`, the *concrete* one defined directly
  by `n.sign * complEDS' …`.

The file comment at line 1522 — `end -- close @[expose] public section to avoid
EllSequence.complEDS ambiguity` — confirms the two were deliberately disambiguated. This is the
project's internal "abstract (`EllSequence.*`) vs. concrete (`_root_.*`)" duplication track. **The
concrete top-level `complEDS` is the one that matches upstream mathlib** (see §3); the abstract
`EllSequence.complEDS` is a project-only re-derivation of the same object via the generic `compl`.

---

## 2. Literature search

`complEDS` is a *definition*, so the literature question is whether the underlying mathematical
object — the division-free complement/quotient sequence `W(n·k)/W(k)` of a normalised EDS — is a
recognised standard construction.

- The notion of an **elliptic divisibility sequence** and its divisibility property
  `W(m) ∣ W(n)` whenever `m ∣ n` is classical, originating in **M. Ward, *Memoir on Elliptic
  Divisibility Sequences*, Amer. J. Math. 70 (1948)** — the reference cited in the upstream mathlib
  file itself ("## References — M Ward, *Memoir on Elliptic Divisibility Sequences*").
- The specific *division-free* witness `W(n·k)/W(k)` (and the 2-step special case `W(2k)/W(k)`) is
  the standard tool for proving that divisibility constructively over a general base ring; it is the
  formal analogue of the recurrences in Ward's memoir and in modern treatments
  (Wikipedia: [Elliptic divisibility sequence](https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence);
  Stange / Silverman, "Sequences associated to elliptic curves"). The construction is exactly what
  one needs to formalise that `normEDS` is an `IsEllDivSequence`.

So the object is mathematically standard. But the literature gate is moot here: the search below
shows the **exact Lean declaration already exists in mathlib**, which dominates any
add-as-is / generalise discussion.

Sources consulted:
- [Mathlib.NumberTheory.EllipticDivisibilitySequence — mathlib4 docs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EllipticDivisibilitySequence.html)
- [Elliptic divisibility sequence — Wikipedia](https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence)
- M. Ward, *Memoir on Elliptic Divisibility Sequences* (cited in the upstream mathlib file).

---

## 3. Mathlib search — IT IS ALREADY THERE (exact match)

The project's `EllipticDivisibilitySequence.lean` is a **fork of the upstream mathlib file**
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (identical copyright header: "Copyright (c)
2024 David Kurniadi Angdinata", identical module docstring including the same `## Main definitions`
bullet — `complEDS`: the complement sequence for a normalised EDS indexed by ℤ).

Upstream copy at the pinned mathlib revision
(`lakefile.toml` → mathlib `rev = "09b373db6e24"`, toolchain `v4.32.0-rc1`):
`.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`.

**Line 427 of the upstream file:**

```lean
section ComplEDS
variable (k : ℤ)

/-- The complement sequence `Wᶜ : ℤ × ℤ → R` for a normalised EDS `W : ℤ → R` that witnesses
`W(k) ∣ W(n * k)`. In other words, `W(k) * Wᶜ(k, n) = W(n * k)` for any `k, n ∈ ℤ`.

This extends `complEDS'` by defining its values at negative integers. -/
def complEDS (n : ℤ) : R :=
  n.sign * complEDS' b c d k n.natAbs
```

This is **byte-for-byte identical** to the project declaration at line 1568:
- identical docstring (the "complement sequence `Wᶜ : ℤ × ℤ → R` … extends `complEDS'`" text);
- identical signature `def complEDS (n : ℤ) : R`;
- identical body `n.sign * complEDS' b c d k n.natAbs`;
- identical variable context (`{R} [CommRing R] (b c d : R) (k : ℤ)`).

The entire surrounding API is also upstream and matches the fork:
- `complEDS'` (upstream line 392 ↔ project 1533),
- `complEDS₂` (upstream 246 ↔ project 844),
- `complEDS_ofNat`, `complEDS_zero`, `complEDS_one`, `complEDS_neg`, `complEDS_even`, `complEDS_odd`
  (upstream 430–473 ↔ project 1571–1616),
- `complEDSRec'` / `complEDSRec` (upstream 482 / 497 ↔ project 1624 / 1638),
- `map_complEDS` (upstream 544),
- and the divisibility scaffolding `normEDS_mul_complEDS₂`, `normEDS_dvd_normEDS_two_mul`
  (upstream 321, 326).

The mathlib4 docs page (above) confirms `complEDS` is a **public, released** declaration in
`Mathlib.NumberTheory.EllipticDivisibilitySequence`, not merely present in this local pin.

### Five-method search summary
1. **Exact-name / file search:** `complEDS` found at `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:427` — exact hit.
2. **Docs / web (leansearch-equivalent):** mathlib4 docs list `complEDS` as the ℤ-indexed complement sequence — confirmed.
3. **Definitional shape (loogle-equivalent):** signature `(b c d : R) (k n : ℤ) : R` with body `n.sign * complEDS' …` — matches upstream verbatim.
4. **Surrounding-API search:** every sibling lemma/recursor of the project's `complEDS` block also exists upstream — this is a whole-section fork.
5. **Provenance:** identical author + docstring + `Main definitions` entry ⇒ the project file *is* the mathlib file (a working fork), so `complEDS` is the upstreamed declaration, not a project original.

---

## 4. Generality analysis

Not applicable for an add/generalise decision (mathlib already has the declaration), but for the
record: the upstream and project forms are **identical in generality** — both over an arbitrary
`CommRing R`, both ℤ-indexed via `n.sign * … n.natAbs`. There is no weaker-hypothesis or
more-general variant to prefer; the upstream form is already the canonical one. The only nearby
"more abstract" object is the project's *own* `EllSequence.complEDS` (line 1110), built from the
generic `compl` combinator — but that is a different, project-internal abstraction track, not a
mathlib generalisation of this declaration.

---

## 5. Composition check

Moot — no need to compose primitives, because the *entire* declaration (and its API) is already a
single named definition in mathlib. Any downstream use should simply `import
Mathlib.NumberTheory.EllipticDivisibilitySequence` and refer to `complEDS` directly. (For
reference, `complEDS` is itself *defined by composition* upstream — `n.sign * complEDS' …` — but
that composition is already packaged under the mathlib name, so re-deriving it locally is pure
duplication.)

---

## 6. Verdict and recommended action

**NO-mathlib-has-it.** `complEDS` is already in mathlib at
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:427`, identical in statement, body,
docstring, and surrounding API. The project's `EllipticDivisibilitySequence.lean` is a fork of that
mathlib file.

Recommended cleanup action (for the owning project / consolidation):
- Do **not** submit this declaration to mathlib — it is already there.
- The project should ultimately **drop its forked copy** of the upstream
  `Mathlib.NumberTheory.EllipticDivisibilitySequence` content and `import` mathlib's version
  instead, keeping only the genuinely-new material (e.g. the `EllSequence.*` abstract track,
  `rel₄` / `net` / `invar*` / `redInvar*` machinery, and any results not yet upstream). The top-level
  `complEDS` here is part of the already-upstreamed core and is redundant with mathlib.
- This same conclusion applies to the parallel sibling declarations in this file's `ComplEDS`
  section (`complEDS'`, `complEDS_ofNat`, `complEDS_even`, `complEDS_odd`, `complEDSRec`, etc.),
  which are likewise verbatim-upstream.

---

### Evidence index
- Project decl: `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1568` (top-level `complEDS`).
- Sibling abstract decl (different name): `…/EllipticDivisibilitySequence.lean:1110` (`EllSequence.complEDS`).
- Disambiguation comment: `…/EllipticDivisibilitySequence.lean:1522`.
- Upstream mathlib decl: `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:427`.
- Mathlib pin: `lakefile.toml` → mathlib `rev = "09b373db6e24"`, toolchain `leanprover/lean4:v4.32.0-rc1`.
- Docs: https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EllipticDivisibilitySequence.html
