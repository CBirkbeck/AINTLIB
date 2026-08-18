# /mathlibable report — `map_complEDS₂`

**Project:** NagellLutz (Nagell–Lutz theorem; elliptic curves; division polynomials;
elliptic divisibility sequences)
**Date:** 2026-06-21 (supersedes the 2026-06-18 assessment, same verdict; this run
adds the full phase artifacts — literature protocol, call-sites table, generality
+ modern-idiom tables, refactor plan)
**Verdict:** `NO-mathlib-has-it`

**TL;DR.** The declaration is a *verbatim fork* of an existing mathlib lemma.
`map_complEDS₂` already lives in
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:526` at the mathlib commit
this workspace is pinned to (`09b373db`, 2026-06-21) with the **identical name,
identical statement, identical `@[simp]` attribute, identical top-level namespace,
and a strictly shorter proof**. The whole project file is a copy of that upstream
module (same 2024 copyright, David Kurniadi Angdinata) with extra
`complEDS`/`compl₂EDS`/`redInvar`/universal-EDS material bolted on.

---

### Baseline (Phase 0)
- lake build:               not re-run (local build is stale per task note; the decl
                            elaborates in the pinned mathlib and the project file is a
                            fork of it — statements compared directly from source).
- decl `map_complEDS₂`:      ✓ resolved at
  `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1652`
  (signature line; the `lemma` keyword is on 1651, body on 1654).
- kind:                      lemma (`@[simp]`)
- has sorry:                 no
- module docstring summary:  Normalised elliptic divisibility sequences — `preNormEDS`,
                            `normEDS`, the 2-complement `complEDS₂`, the complement
                            sequence `complEDS'`/`complEDS`, and ring-hom naturality lemmas.
                            A fork of `Mathlib.NumberTheory.EllipticDivisibilitySequence`.

---

### Statement (Phase 1)

`map_complEDS₂` is the **naturality** ("commutes with ring homomorphisms") lemma for
the 2-complement sequence `complEDS₂` of a normalised elliptic divisibility sequence.
For a ring hom `f : R →+* S`, structure constants `b c d : R`, and an index `n : ℤ`:

> `f (complEDS₂ b c d n) = complEDS₂ (f b) (f c) (f d) n`.

Here `complEDS₂ b c d k` is, by definition,
`(preNormEDS (b⁴) c d (k-1)² · preNormEDS (b⁴) c d (k+2) − preNormEDS (b⁴) c d (k-2) · preNormEDS (b⁴) c d (k+1)²) · (if Even k then 1 else b)`.
The lemma is the routine "transfer along a ring hom" fact: every ingredient (powers,
products, differences, the auxiliary `preNormEDS`, the `if Even` branch) is preserved
by `f`.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — source commutative ring.
- `{S : Type v} [CommRing S]` — target commutative ring.
- `(b c d : R)` — the three structure constants of the normalised EDS.
- `(f : R →+* S)` — a bundled ring homomorphism.
- `(n : ℤ)` — the index.

Hypotheses: none beyond the typeclasses.

Conclusion (math): the 2-complement EDS term is natural in the base ring.
Conclusion (Lean): `f (complEDS₂ b c d n) = complEDS₂ (f b) (f c) (f d) n`.

Project proof: `simp [complEDS₂, apply_ite f, map_preNormEDS, map_pow]`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-line `simp`-closed naturality (`map_*`) lemma about an auxiliary
sequence; not a named theorem, not a new structure, not a `## Main results` entry.
It feeds the larger `map_complEDS'`/`map_complEDS` naturality chain and the
Hasse–Weil division-polynomial bridge, but is itself a helper.

### One-line check (Phase 2b)

Kind is `lemma`, so the one-line-*definition* negative-signal check does not apply —
n/a. (A single-`simp`-call body is the expected, idiomatic shape for a `map_*`
naturality lemma; not itself a negative signal.)

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

The object here is an *infrastructure* lemma (functoriality of a Lean construction
along a ring hom). The literature question that matters — "what is `complEDS₂`, and
is the 2-complement a standard, paper-level object?" — is settled directly by the
mathlib source, which is the authoritative definition this project forks.

| #  | Channel                          | Query                                                                                   | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|-----------------------------------------------------------------------------------------|------|------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic divisibility sequence" division polynomial ring homomorphism naturality       | n/a  | —                                                    | `map_*` naturality is a Lean/mathlib idiom, not a paper result; nothing specific to surface. |
|  2 | WebSearch (general form)         | elliptic divisibility sequence base change / specialisation of structure constants      | weak | EDS attached to Weierstrass data; division polys specialise under ring maps | The *content* (division polynomials commute with base change, being universal ℤ-polynomials) is folklore — Silverman, *AEC* III §3 + exercises; no canonical `complEDS₂` name outside mathlib. |
|  3 | WebSearch (named-after / aliases)| Ward elliptic divisibility sequence; "2-complement" `Wᶜ₂`; `W(k) ∣ W(2k)`                | no   | —                                                    | The term "2-complement sequence" / notation `Wᶜ₂` is **mathlib's own coinage** (per the mathlib docstring); not a literature term. |
|  4 | ChatGPT MCP                      | standard form + generality + history of the 2-complement of a normalised EDS            | n/a  | —                                                    | MCP unavailable here (task note: ChatGPT MCP may be down). Compensated by reading the authoritative mathlib source directly — a strictly stronger signal than a chat answer. |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/`                                  | n/a  | —                                                    | No `references/` dir for this project (only `overview/`). Recorded n/a. |
|  6 | nLab                             | elliptic divisibility sequence                                                          | no   | —                                                    | No dedicated EDS / division-polynomial-naturality page. |
|  7 | nCatLab (categorical)            | —                                                                                       | n/a  | —                                                    | Not categorical beyond "construction is functorial in the base ring" — which is exactly what the lemma says. |
|  8 | Stacks Project (alg geom)        | division polynomial / elliptic divisibility sequence                                    | no   | —                                                    | Stacks does not develop division polynomials / EDS under this name. |
|  9 | MathOverflow / MSE               | elliptic divisibility sequence base change ring homomorphism                            | weak | —                                                    | General principle (division polys are universal, hence commute with any ring map) is well known; no canonical lemma statement to cite. |
| 10 | recent arXiv (≤5 yr)             | normalised elliptic divisibility sequence Lean formalisation                            | weak | —                                                    | The relevant "source" is the mathlib formalisation itself (Angdinata's EDS development) — precisely what was forked. |

**Decisive non-literature channel (mathlib source).** The authoritative definition
and naturality lemma exist verbatim in
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`. That file *is* the
reference for `complEDS₂`; the project file copies it (matching docstring: "The
2-complement sequence `Wᶜ₂ : ℤ → R` … that witnesses `W(k) ∣ W(2 * k)`").

### Literature summary (Phase 3)

Concept identified as: **naturality (ring-hom transfer) of the 2-complement sequence
`complEDS₂` of a normalised elliptic divisibility sequence.**
Sources agree on the standard form: yes — and the *source* is mathlib itself.
`complEDS₂` / `Wᶜ₂` is a mathlib coinage; the underlying fact (division-polynomial /
EDS data is preserved under base change because the terms are universal integer
polynomials in `b, c, d`) is folklore in the arithmetic of elliptic curves
(Silverman, *The Arithmetic of Elliptic Curves*, III §3 and the division-polynomial
exercises).
Most general standard form: `f (complEDS₂ b c d n) = complEDS₂ (f b) (f c) (f d) n`
for any ring hom `f : R →+* S` between commutative rings — exactly the declaration
under review and exactly the mathlib lemma.
Generality dimensions where the literature varies: none bearing on this lemma; the
construction is integer-polynomial, so `CommRing` + `RingHom` is the natural maximal
home.
Disagreement with the literature: none.

---

### Generality analysis — `map_complEDS₂` (Phase 4)

Literature/mathlib-standard form (from Phase 3): identical to the current form.

| # | Parameter / hypothesis | Current Lean form   | Mathlib-standard form        | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|---------------------|------------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]`         | commutative ring    | commutative ring             | NO                  | `complEDS₂` is built from `preNormEDS`, whose recursion multiplies and subtracts; `CommRing` is used throughout the EDS development. Matches mathlib exactly. |
| 2 | `[CommRing S]`         | commutative ring    | commutative ring             | NO                  | Same; the target carries the transferred sequence. |
| 3 | `(f : R →+* S)`        | bundled `RingHom`   | `RingHom` (mathlib identical) | borderline          | Could state over `[RingHomClass F R S]` for generic bundled `F` (the project's own `map_preNormEDS'` block does this upstream). But **mathlib's `map_complEDS₂` itself uses `R →+* S`** — matching mathlib (not over-generalising past it) is correct; not a reason to *add* anything. |
| 4 | `(n : ℤ)`              | integer index       | integer index                | NO                  | `complEDS₂` is defined on `ℤ` (extended from `ℕ` via sign); `ℤ` is the natural index. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL**, and — more to the point — *identical to
the mathlib lemma*.
Number of weakening opportunities that would justify a new contribution: 0.
The only axis with a variant (row 3: `RingHomClass F` vs `R →+* S`) is one where
mathlib has already made the choice (`R →+* S`); re-stating it more generally is a
`/generalise`-on-mathlib question, not a reason to add this fork.
Cost of restatement: n/a — no restatement warranted; the lemma already exists upstream.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Proposed reformulation | Mathlib downstream |
|----|--------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | "let X be a foo" preambles → typeclasses?                                 | no       | —                      | Already typeclass-driven (`CommRing`, `RingHom`). |
|  2 | sequences/metric → filters/topology?                                      | no       | —                      | Purely algebraic identity; no analysis. |
|  3 | construct object → universal-property class?                              | no       | —                      | This is a `map_*` equation, not a construction. |
|  4 | set+closure predicate → bundled substructure?                             | no       | —                      | No substructure here. |
|  5 | vector-space/field-specific → weaken typeclasses?                         | no       | —                      | Already at `CommRing`. |
|  6 | 1-categorical → higher-categorical?                                       | no       | —                      | n/a. |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group?                          | no       | —                      | Index is `ℤ` by the definition of `complEDS₂`; not generalisable. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no.** The lemma is already in idiomatic mathlib shape —
unsurprising, since it *is* the mathlib lemma. One-line reason: a byte-for-byte fork
of upstream; nothing to modernise.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (a proof, not a `def`/`class`/`instance`); it
introduces no definitional equalities or typeclass-search paths.

---

### Mathlib search-status: `map_complEDS₂` (Phase 5)

[A] Lean-Finder       "ring hom complEDS₂ naturality"                     hit — `map_complEDS₂` (EDS file)
[B] Loogle            `f (complEDS₂ _ _ _ _) = complEDS₂ (f _) ..`        hit — same lemma
[C] LeanSearch        "map of 2-complement of elliptic divisibility seq"  hit — same lemma
[D] Grep mathlib src  `grep -n "map_complEDS₂"` over `.lake/.../mathlib/` hit — **exact match, line 526**
[E] Name pattern      `map_complEDS₂`                                      hit — exact name, top-level namespace (both files have **zero** enclosing `namespace`)

**Direct source confirmation (method [D], decisive):**
`.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:526`

```lean
@[simp]
lemma map_complEDS₂ (n : ℤ) : f (complEDS₂ b c d n) = complEDS₂ (f b) (f c) (f d) n := by
  simp [complEDS₂, apply_ite f]
```

with section-level `variable (b c d : R)` (line 706) and
`variable {S : Type v} [CommRing S] (f : R →+* S)` (line 507) — i.e. the **same
signature, same name, same `@[simp]` attribute, same top-level namespace** as the
project declaration. The underlying `complEDS₂` definition is byte-for-byte identical
(project line 844 ≡ mathlib line 246). The mathlib proof is *shorter*: mathlib's
default `simp` set already supplies `map_preNormEDS`/`map_pow`, which the fork lists
redundantly.

Statement equivalence — IDENTICAL:

| | Project (NagellLutz) | Mathlib |
|---|---|---|
| Name | `map_complEDS₂` | `map_complEDS₂` |
| Attribute | `@[simp]` | `@[simp]` |
| Hypotheses | `{R} [CommRing R] (b c d : R) {S} [CommRing S] (f : R →+* S)`, `(n : ℤ)` | same |
| Conclusion | `f (complEDS₂ b c d n) = complEDS₂ (f b) (f c) (f d) n` | identical |
| Namespace | top-level (no `namespace`) | top-level (no `namespace`) |

Searched for both: the user's current form — found, exact; the more-general form —
the same lemma is already the most general form, so no separate hit needed.

**Concluded:** found in mathlib as `map_complEDS₂`
(`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:526`); **identical form**.
The project file is a fork of this exact mathlib module (matching 2024 copyright by
David Kurniadi Angdinata, matching docstrings, matching definitions of `complEDS₂`,
`map_preNormEDS`, `map_normEDS`, `map_complEDS'`, …).

---

### Call sites — `map_complEDS₂` (Phase 6.0)

Internal use count (NagellLutz, excluding the declaring file): **0**.
External-to-file callers (other AINTLIB projects in the same workspace): **2 files**.

| Caller file:line                                                              | Usage pattern (one-line excerpt)                                   |
|-------------------------------------------------------------------------------|--------------------------------------------------------------------|
| `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:199`          | `rw [ψc, map_complEDS₂, ← evalEval_ψ₂, ← evalEval_Ψ₃, ← evalEval_preΨ₄]` |
| `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:933`| `… ← map_complEDS₂, ← map_normEDS, ← map_complEDSAux₂]`             |
| (NagellLutz internal) `…/EllipticDivisibilitySequence.lean:1663`              | `simp only [… map_complEDS₂ …]` inside `map_complEDS'` (same file — not counted) |

Inline-derivation grep: consumers `rw`/`simp` with the lemma name directly; no inline
re-derivation. Note the HasseWeil callers most likely resolve against **mathlib's**
`map_complEDS₂` (or HasseWeil's own copy) rather than the NagellLutz fork; all copies
are byte-identical, so the call sites are agnostic to which one wins. This confirms
the lemma is genuinely used API — but API that **mathlib already provides**, so the
consumers can and should depend on the upstream lemma rather than a project fork.

### Composition check (Phase 6)

Can `map_complEDS₂` be derived from mathlib in ≤3 chained calls? **Trivially — it *is*
a mathlib lemma.** No composition needed; reference `map_complEDS₂` directly (it is
`@[simp]` in mathlib, so `simp` also discharges it).

Attempt: `exact map_complEDS₂ ..` / `simp`. Result: succeeds (identity reference).

Conclusion: **NOT-COMPOSABLE in the "build from primitives" sense — because it is not
built from primitives; it is the existing lemma verbatim.** This routes to
`NO-mathlib-has-it`, not `NO-composable-from-mathlib`.

---

## Verdict: `map_complEDS₂`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): `complEDS₂` ("2-complement", notation `Wᶜ₂`) is a
  mathlib coinage; the authoritative definition lives in mathlib and the project file
  is a verbatim fork of that module.
- Generality analysis (Phase 4): MAXIMALLY GENERAL and identical to the mathlib form;
  the modern-idiom check finds nothing to change (it already *is* the idiom).
- Mathlib search (Phase 5): found in mathlib as `map_complEDS₂` at
  `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:526` — identical name,
  signature, `@[simp]` attribute, and top-level namespace — with a strictly shorter
  proof.
- Composition check (Phase 6): trivially derivable — it is the same lemma.

**Rationale:**

This is not "mathlib has a more general version" nor "compose two primitives" — it is
an **exact duplicate**. The project file
`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` is a fork of
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (identical 2024 copyright by
David Kurniadi Angdinata, identical module-docstring bullet list, identical
definitions of `preNormEDS`, `normEDS`, `complEDS₂`, and identical `map_*` naturality
lemmas). At the mathlib commit this workspace is pinned to (`09b373db`, 2026-06-21),
`map_complEDS₂` is already present upstream with the same name, the same statement
`f (complEDS₂ b c d n) = complEDS₂ (f b) (f c) (f d) n`, the same `@[simp]` tag, and a
proof that is in fact *shorter* (mathlib: `simp [complEDS₂, apply_ite f]`; the fork
redundantly adds `map_preNormEDS, map_pow`, which mathlib's `simp` set already
supplies). There is nothing to contribute; the work has already landed in mathlib.

**WHY not (refactor-actionable):** Mathlib already has this lemma, character-for-
character. The project carries it only because the file was copied wholesale from the
upstream EDS module (the PROJECT CONTEXT flagged exactly this: the project "FORKS
parts of mathlib … `Mathlib.NumberTheory.EllipticDivisibilitySequence`"). The forked
`complEDS₂`/`normEDS`/`preNormEDS` block — including `map_complEDS₂` — is pure
duplication of upstream and should be deleted in favour of
`import Mathlib.NumberTheory.EllipticDivisibilitySequence`.

Existing mathlib decl:        `map_complEDS₂`
Located at:                   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:526`
Our form follows in ≤1 line (it is literally the same lemma):
```lean
example {R S : Type*} [CommRing R] [CommRing S] (b c d : R) (f : R →+* S) (n : ℤ) :
    f (complEDS₂ b c d n) = complEDS₂ (f b) (f c) (f d) n :=
  map_complEDS₂ ..   -- the mathlib lemma, after `import Mathlib.NumberTheory.EllipticDivisibilitySequence`
```

Call sites in this project (from Phase 6.0): 0 internal to NagellLutz; 2 in the
sibling HasseWeil project (which already reference the same name, agnostic to which
identical copy resolves).

**Refactor plan:**
1. Delete the forked `complEDS₂`/`map_complEDS₂` (and the whole duplicated
   `preNormEDS`/`normEDS`/`map_*` block) from
   `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean`, replacing it
   with `import Mathlib.NumberTheory.EllipticDivisibilitySequence` (or the project's
   `Common/` re-export). Keep only the genuinely-new additions the fork bolted on
   (`complEDS'`, `complEDS`, `compl₂EDS`, `redInvar*`, the universal-EDS machinery) —
   those are this project's actual contribution and warrant their own `/mathlibable`
   runs.
2. The downstream use of `map_complEDS₂` in the same file (inside `map_complEDS'`,
   line 1663) then resolves against the mathlib lemma unchanged — the call site is
   identical (`simp only [… map_complEDS₂ …]`).
3. The two HasseWeil call sites need no edit (same name, same statement).
4. This is **cleanup-on-`main` work** (dedup against mathlib), per AINTLIB's CLEANER
   rules — not new-math producer work. Since the surrounding fork still contains
   in-progress `complEDS`/`redInvar` material, scope the deletion to the
   mathlib-duplicated declarations only and confirm `lake build` stays green after
   re-pointing to the upstream import.

**Next action:** delete `map_complEDS₂` (and the rest of the mathlib-duplicated EDS
block) from the project; depend on `Mathlib.NumberTheory.EllipticDivisibilitySequence`
instead. No mathlib PR — the lemma is already there.

---

## Next step

Delete `map_complEDS₂` from the project and route its (zero internal + two
sibling-project) consumers to the existing mathlib lemma `map_complEDS₂`
(`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:526`) via
`import Mathlib.NumberTheory.EllipticDivisibilitySequence`. The forked EDS block is
pure duplication of upstream; only the project's genuinely-new
`complEDS`/`compl₂EDS`/`redInvar`/universal-EDS additions merit separate mathlibable
assessment.
