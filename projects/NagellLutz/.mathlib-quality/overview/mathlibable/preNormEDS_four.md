# /mathlibable report — `preNormEDS_four`

**Verdict: NO-mathlib-has-it** — the declaration is a byte-for-byte fork of an existing
mathlib lemma (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:202-204`).

> Companion note: this is the **integer-indexed** (`preNormEDS : ℤ → R`) seed lemma. Its
> natural-number sibling `preNormEDS'_four` (`preNormEDS' : ℕ → R`) was assessed separately in
> `preNormEDS'_four.md` and reached the same verdict. Do not conflate the two — the decl at line 800
> is the `ℤ` one (`preNormEDS b c d 4 = d`), proof `simp [preNormEDS, Int.sign_eq_one_of_pos]`.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task note; reasoning from source — the
                            decl is a forked copy of a green mathlib lemma, so elaboration is not in doubt)
- decl `preNormEDS_four`:   ✓ resolved at
                            `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:800`
- kind:                     lemma (`@[simp]`)
- has sorry:                no
- module docstring summary: The file is a near-verbatim FORK of
                            `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` — same copyright
                            header (© 2024 David Kurniadi Angdinata), same author, same
                            `section PreNormEDS`, same `def preNormEDS`. The project file does **not**
                            `import` the mathlib module; it re-declares the EDS machinery in order to
                            extend it (adding `EllSequence`, `complEDS₂`, the 2-complement / divisibility
                            development) for the Nagell–Lutz theorem.

**Qualified name.** The decl lives in `section PreNormEDS` (opens at line 704), which contains **no**
`namespace`. So the qualified name is the bare `preNormEDS_four` — there is no namespace prefix.
(`variable (b c d : R)` is a section variable, not a namespace.) Verified against the file's
`namespace`/`section`/`end` scan: the enclosing scopes between line 704 and line 879 are
`section PreNormEDS` only — no `namespace` is opened. **Parsed/declared qualified name confirmed:
`preNormEDS_four`.**

---

### Statement (Phase 1)

`preNormEDS_four` states that the integer-indexed auxiliary normalised-EDS sequence
`preNormEDS b c d : ℤ → R` takes the value `d` at index `4`:

```lean
@[simp]
lemma preNormEDS_four : preNormEDS b c d 4 = d := by
  simp [preNormEDS, Int.sign_eq_one_of_pos]
```

`preNormEDS` is the **integer extension** of the auxiliary sequence `preNormEDS'`, defined by
`preNormEDS b c d n = n.sign * preNormEDS' b c d n.natAbs` (line 774). It carries the same seed values
`W(0)=0, W(1)=1, W(2)=1, W(3)=c, W(4)=d` with parameter `b`, now over all of `ℤ`. This lemma is the
**seed-value read-off** for index `4`: at `n = 4 > 0` the sign is `1` and `n.natAbs = 4`, so
`preNormEDS b c d 4 = preNormEDS' b c d 4 = d`. The proof discharges this by `simp` with the
definition and `Int.sign_eq_one_of_pos` (and `preNormEDS_ofNat` / `preNormEDS'_four` fire as `@[simp]`
to land on `d`).

- Variables / typeclasses: `{R : Type*} [CommRing R]` (from the file's `variable` block);
  `(b c d : R)` section parameters.
- Hypotheses: none.
- Conclusion (math): the 4th term of the seed of the integer EDS `preNormEDS` equals `d`.
- Conclusion (Lean): `preNormEDS b c d 4 = d`.

This is one of a family of glue lemmas: `preNormEDS_zero/_one/_two/_three/_four` (+ `preNormEDS_ofNat`,
`preNormEDS_neg`), each reading off one value of the integer sequence — the `ℤ` mirror of the
`preNormEDS'_zero…_four` `ℕ` family.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a definitional read-off / glue lemma (`@[simp]`, one-line `simp`) for one seed value of a
sequence; not a structure, not a named theorem, not a main result.

### One-line check (Phase 2b)

Body line count: 1 substantive line (`simp [preNormEDS, Int.sign_eq_one_of_pos]`). Kind is `lemma`, so
the def-oriented one-liner exemption table is **n/a** — this section is informational only. It is the
archetypal glue lemma (a definitional read-off via the `sign · natAbs` formula), which under the
skill's verdict-inheritance rule is a strong "do not add separately" signal: its content is wholly
determined by `def preNormEDS` together with the already-established `preNormEDS'_four`.

---

### Literature search (Phase 3)

For a definitional seed read-off the "literature-standard form" is just *the definition of the
integer-extended sequence at index 4*. There is no independent mathematical content to locate in the
literature — `preNormEDS b c d 4 = d` is true purely because Angdinata's definition sets
`preNormEDS n = n.sign · preNormEDS' n.natAbs` and the 4th seed of `preNormEDS'` is `d`. The relevant
"source" is the definition itself, which already lives in mathlib. The channels below are recorded for
completeness.

| #  | Channel                           | Query                                                                 | Hit? | Standard form found                          | Notes |
|----|-----------------------------------|-----------------------------------------------------------------------|------|----------------------------------------------|-------|
|  1 | WebSearch (specific form)         | "preNormEDS mathlib elliptic divisibility sequence … Angdinata"       | yes  | `preNormEDS n = n.sign · preNormEDS' n.natAbs`, seed `W(0..4)=0,1,1,c,d`, param `b` | Maps to the mathlib docs page for `Mathlib.NumberTheory.EllipticDivisibilitySequence`; confirms the integer extension and its seed values |
|  2 | WebSearch (general form)          | (same query, generality angle on normalised EDS over a ring)          | yes  | `normEDS` defined via `preNormEDS (b^4) c d`  | The construction (Shipsey / Stange / Ward normalised EDS from seeds) — the *recursion + sign extension* is the math; an individual seed-readoff is not a literature result |
|  3 | WebSearch (named-after / aliases) | EDS auxiliary "pre-normalised" sequence; extension to negative index   | yes  | arXiv 2604.05280 "On Elliptic Sequences over Commutative Rings"; arXiv math/0402415 (Stange/Ward EDS) — EDS are odd: `W(-n) = -W(n)` | Background on EDS over rings; the odd-extension `W(-n)=-W(n)` is standard, matching `n.sign`; none state a standalone "4th seed = d" lemma — it is definitional |
|  4 | ChatGPT MCP                       | n/a — not consulted (MCP down per task note + adds nothing here)       | n/a  | —                                            | Deliberately skipped: the decl is a verbatim fork of a mathlib glue lemma; a second opinion on "is the 4th seed equal to `d`" is not informative and the mathlib-has-it evidence is already conclusive |
|  5 | Local references                  | grep `.mathlib-quality/references/`                                    | n/a  | (directory absent)                           | `projects/NagellLutz/.mathlib-quality/references/` does not exist — recorded n/a |
|  6 | nLab                              | "elliptic divisibility sequence"                                      | n/a  | —                                            | nLab has no EDS page; not a categorical concept — n/a |
|  7 | nCatLab                           | —                                                                     | n/a  | —                                            | Not a categorical concept — n/a |
|  8 | Stacks Project                    | —                                                                     | n/a  | —                                            | Not a scheme-theoretic concept (an arithmetic recurrence) — n/a |
|  9 | MathOverflow / Math.SE            | EDS auxiliary sequence seed values / odd extension                    | n/a  | —                                            | No standalone seed-readoff identity; definitional — n/a |
| 10 | recent arXiv (last 5 years)       | EDS over commutative rings                                            | yes  | arXiv 2604.05280                              | Confirms the area is active; no standalone "4th seed" lemma (definitional in any such paper) |

### Literature summary (Phase 3)

Concept identified as: the **integer-indexed auxiliary sequence `preNormEDS` for a normalised elliptic
divisibility sequence** (Angdinata's mathlib formalisation; rooted in Shipsey / Stange / Ward EDS
theory), extending the `ℕ`-indexed `preNormEDS'` to `ℤ` by the odd rule `W(-n) = -W(n)` (encoded as
`n.sign · preNormEDS' n.natAbs`).
Sources agree on the standard form: yes — seed `W(0..4) = 0,1,1,c,d`, parameter `b`, odd extension to
negative indices; exactly what the mathlib docs and EDS literature use.
Most general standard form: `preNormEDS b c d 4 = d` is not an independent theorem; it is the value of
the **definition** at index 4. There is no "more general" version to seek — the ring generality is
already maximal (`CommRing R`, see Phase 4).
Disagreement with the literature: none.

---

### Generality analysis (Phase 4)

### 4a. Generality status table

Literature-standard form: the seed value of the integer EDS `preNormEDS` at index 4, over a
commutative ring.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `{R : Type*} [CommRing R]` | commutative ring | commutative ring (EDS are defined over CommRing) | NO | `preNormEDS` is defined over `CommRing R`; the seed read-off holds at exactly that generality. Identical to mathlib's own `preNormEDS`. |
| 2 | `(b c d : R)` | ring elements | ring elements | NO | These ARE the defining seed parameters; nothing to weaken. |
| 3 | index `4 : ℤ` | literal seed position | literal seed position | NO | `4` names a specific recursion/seed arm; "generalising the index" is meaningless for a seed read-off. |

### 4b. Generality verdict

The current form is: **MAXIMALLY GENERAL** (identical to mathlib's own `preNormEDS_four`).
Number of weakening opportunities found: 0.
Proposed restatement: none.
Cost of restatement: n/a.

### 4c. Modern mathlib-idiom check

| # | Question | Applies? | Reason |
|---|----------|----------|--------|
| 1 | bundled hyps → typeclasses? | no | already a bare `CommRing` typeclass; no "let X be a foo" preamble |
| 2 | sequences/metric → filters/topology? | no | discrete arithmetic recurrence; no analytic notion to filter-ise |
| 3 | construction → universal-property class? | no | a seed read-off, not a construction |
| 4 | set+closure-pred → bundled substructure? | no | not a substructure |
| 5 | vector-space/field-specific → weaken typeclass? | no | already `CommRing`, the natural home for EDS |
| 6 | 1-categorical → higher-categorical? | no | not categorical |
| 7 | concrete index (ℕ/ℤ/ℝ) → general additive structure? | no | the index `4 : ℤ` is a literal seed position; generalising it names nothing |

Modern idiom available: **no**. The form is already the idiomatic mathlib one — because it **is** the
mathlib decl, verbatim.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (introduces no definitional equalities or typeclass-search paths).

---

### Mathlib search-status: `preNormEDS_four` (Phase 5)

[A] Lean-Finder       n/a (mathlib index unavailable for direct query this run; resolved by grep below)
[B] Loogle            type pattern `preNormEDS _ _ _ (4 : ℤ) = _`   resolved by direct source grep instead
[C] LeanSearch        "value of integer normalised EDS sequence at four"   resolved by direct source grep instead
[D] Grep mathlib src  `grep -n "preNormEDS_four" …/.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
                      → **HIT at line 202** (whole `preNormEDS_zero…_four` family at 186-204;
                      `def preNormEDS` at 176, `preNormEDS_ofNat` at 182)
[E] Name pattern      `preNormEDS_four`                             → exact name match in mathlib

Searched for both the project's current form and the (identical) literature-standard form.

**Concluded: found in mathlib as `preNormEDS_four`; IDENTICAL form** — byte-for-byte:

mathlib (`.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:202-204`):
```lean
@[simp]
lemma preNormEDS_four : preNormEDS b c d 4 = d := by
  simp [preNormEDS, Int.sign_eq_one_of_pos]
```
project (`EllipticDivisibilitySequence.lean:799-801`): the same three lines — same `@[simp]`, same
statement `preNormEDS b c d 4 = d`, same proof `simp [preNormEDS, Int.sign_eq_one_of_pos]`. Both in a
non-namespaced `section PreNormEDS`, both under `variable (b c d : R)` with `[CommRing R]`. The entire
surrounding block matches mathlib verbatim:
`def preNormEDS` (project 774 / mathlib 176), `preNormEDS_ofNat` (778/182), and
`preNormEDS_zero/_one/_two/_three/_four/_neg` (784-804 / 186-207) are line-for-line identical. The
project file shares mathlib's exact copyright header (© 2024 David Kurniadi Angdinata) and does not
import the mathlib module — it is a direct fork that re-declares the API to extend it.

---

### Composition check (Phase 6)

### 6.0. Call sites — `preNormEDS_four`

Internal use count (project, excluding the declaring file): **1** external file.
In-file callers: **1** (`EllipticDivisibilitySequence.lean:1077`, not counted in the external "1").

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:142` | `preNormEDS_four ..` |
| `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1077` | `rw [preNormEDS_one, preNormEDS_two, preNormEDS_four, if_neg (by decide)]` (same file) |

There is also a parallel cross-project fork in
`projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:623`
(`rw [preNormEDS_one, preNormEDS_two, preNormEDS_four, …]`) — a separate copy of the same forked API,
not a consumer of this decl. The call sites are exactly the ones mathlib's own `preNormEDS_four` would
serve — confirming the decl is redundant with mathlib, not a project-specific specialisation.

### 6a. Composition attempt

Can `preNormEDS_four` be derived from mathlib in ≤3 chained calls? It does not need composition —
mathlib has the **identical named lemma**. (For the record, the one-step derivation from primitives is
also already in mathlib: `simp [preNormEDS, Int.sign_eq_one_of_pos]`, i.e. unfold `preNormEDS`, use
`Int.sign_eq_one_of_pos` at `4 > 0`, then `preNormEDS_ofNat`/`preNormEDS'_four` land on `d` — ≤3
mathlib facts. So even the stronger NO-composable case would hold; but the precise verdict is the
sharper NO-mathlib-has-it.)

Conclusion: **the lemma already exists as a single named mathlib declaration** — the
NO-mathlib-has-it case applies (subsumes NO-composable).

---

## Verdict: `preNormEDS_four`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): the concept (the integer extension `preNormEDS` of the auxiliary
  normalised-EDS sequence) maps directly to mathlib; the "4th seed = d" statement is definitional, not
  an independent literature result.
- Generality analysis (Phase 4): MAXIMALLY GENERAL — identical to mathlib's form; no modern-idiom
  improvement (it *is* the idiom).
- Mathlib search (Phase 5): **found in mathlib as `preNormEDS_four`, byte-for-byte identical**
  (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:202`), `@[simp]`, proof
  `simp [preNormEDS, Int.sign_eq_one_of_pos]`.
- Composition check (Phase 6): not needed — mathlib has the exact named lemma (and the primitive
  one-liner is also already upstream).

**Rationale.**
The project's `EllipticDivisibilitySequence.lean` is a direct fork of mathlib's
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` — same © 2024 David Kurniadi Angdinata
header, same `section PreNormEDS`, same `def preNormEDS n = n.sign · preNormEDS' n.natAbs`. The lemma
`preNormEDS_four` is reproduced verbatim: identical statement (`preNormEDS b c d 4 = d`), identical
`@[simp]` attribute, identical proof, identical typeclass context (`CommRing R`). There is nothing to
upstream — mathlib already owns this exact declaration. The fork exists because the project forks the
EDS / division-polynomial machinery to extend it for the Nagell–Lutz development (it does not import
the mathlib module; it re-declares the seed lemmas and builds the `EllSequence` / `complEDS₂` /
divisibility layer on top).

**WHY not (refactor-actionable).**
Mathlib already has it, verbatim. The project does not need to re-declare it: every use site can call
the mathlib lemma directly. Because the whole `PreNormEDS` block is a fork, the right fix is not a
one-line swap of this single lemma but **deduplicating the forked block against upstream mathlib** —
i.e. delete the local `preNormEDS` definition + its seed lemmas (`preNormEDS_zero…_four`,
`preNormEDS_ofNat`, `preNormEDS_neg`, the `preNormEDS_even/_odd` recurrences, and the `preNormEDS'`
family) and `import Mathlib.NumberTheory.EllipticDivisibilitySequence` instead, keeping only the
genuinely-new material the fork adds on top (`EllSequence`, `complEDS₂`, the 2-complement /
divisibility development). This is exactly the cross-project dedup the AINTLIB cleanup lane owns.

Existing mathlib decl:        `preNormEDS_four`
Located at:                   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:202`
Our form follows in 0 lines (it is the same lemma):
```lean
-- after `import Mathlib.NumberTheory.EllipticDivisibilitySequence`, the name resolves directly:
example (R) [CommRing R] (b c d : R) : preNormEDS b c d 4 = d := preNormEDS_four
```
Call sites in this project (from Phase 6.0): 1 external (`DivisionPolynomial.lean:142`
`preNormEDS_four ..`) + 1 in-file (`EllipticDivisibilitySequence.lean:1077`); plus the cross-project
fork in `HasseWeil/.../EllipticDivisibilitySequence.lean:623`.

**Refactor plan:**
1. Prefer the mathlib `PreNormEDS` API over the local fork: replace the forked `def preNormEDS` (and
   its seed/recurrence lemmas, including `preNormEDS_four`) with
   `import Mathlib.NumberTheory.EllipticDivisibilitySequence` and drop the duplicates.
2. The call sites (`DivisionPolynomial.lean:142`, `EllipticDivisibilitySequence.lean:1077`) then
   resolve to the mathlib lemma unchanged — same name, same signature, same `@[simp]` behaviour, so no
   edit is needed at the call sites once the import is in place.
3. Coordinate with the `preNormEDS'_four` dedup (same block) and the HasseWeil-side fork
   (`HasseWeil/.../EllipticDivisibilitySequence.lean`, which carries its own copy of this lemma) so the
   whole forked `PreNormEDS` API collapses onto upstream mathlib in one cross-project cleanup.
   *Caveat:* the fork keeps a local `preNormEDS'` whose termination plumbing differs from mathlib's
   (explicit `have … omega` vs. `gcongr`); confirm nothing downstream depends on the local
   definitional plumbing before deleting (the lemma *statements* are defeq-identical, so consumers of
   the lemmas are safe).

**Next action:** treat as a cross-project **deduplication** cleanup ticket — delete the forked
`preNormEDS`/`preNormEDS'` seed lemmas (including `preNormEDS_four`) and import the mathlib module; do
NOT open a mathlib PR (mathlib already has the identical declaration).

---

## Next step

Delete `preNormEDS_four` (and the surrounding forked `PreNormEDS` seed-lemma block) from the project
and import `Mathlib.NumberTheory.EllipticDivisibilitySequence`; the 1 external + 1 in-file call sites
(plus the HasseWeil fork) resolve to the identical mathlib lemma unchanged. No mathlib PR — it is
already there.
