# /mathlibable report — `IsEllSequence.smul`

**Verdict: NO-mathlib-has-it** — the declaration exists *verbatim* in the project's pinned mathlib.

> Target declaration: `IsEllSequence.smul` at
> `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:621`.
>
> FILENAME-COLLISION NOTE: three sibling lemmas in this file share the base name `smul`
> (`IsEllSequence.smul` @621, `IsDivSequence.smul` @628, `IsEllDivSequence.smul` @631), so
> parallel Step-9 workers all target `mathlibable/smul.md`. Prior versions of this file held the
> sibling reports; this version assesses the requested `IsEllSequence.smul`. All three reach the
> same verdict (NO-mathlib-has-it) for the same reason — the project forks mathlib's EDS file and
> all three lemmas are present verbatim upstream.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale, per task note); assessment reasons from source
- decl `IsEllSequence.smul`: ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:621`
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  Forked + extended copy of mathlib's elliptic divisibility sequence (EDS)
  theory — division-polynomial relations (`Rel₃`/`rel₄`), the odd/even recurrences, and the EDS
  predicates `IsEllSequence` / `IsDivSequence` / `IsEllDivSequence`, en route to Nagell–Lutz.

---

### Statement (Phase 1)

`IsEllSequence.smul` states:

> If `W : ℤ → R` is an *elliptic sequence* over a commutative ring `R`, then for any scalar `x : R`
> the pointwise-scaled sequence `x • W` (i.e. `n ↦ x · W n`) is again an elliptic sequence.

A sequence is *elliptic* (`IsEllSequence W`) when, for all `m n r : ℤ`, it satisfies the fundamental
EDS relation `Rel₃`:
`W(m+n)·W(m−n)·W(r)² = W(m+r)·W(m−r)·W(n)² − W(n+r)·W(n−r)·W(m)²`.

Each side is **homogeneous of degree 4** in the values of `W`, so multiplying every term `W(k)` by `x`
multiplies both sides by `x⁴`; the relation is preserved. The proof is exactly that:
`linear_combination x ^ 4 * (the relation for W)`.

Variables / typeclasses (Lean): `{R : Type u} [CommRing R]`, `{W : ℤ → R}`, `(x : R)`.
Hypotheses (Lean): `(h : IsEllSequence W)`.
Conclusion (math): `x · W` is an elliptic sequence.
Conclusion (Lean): `IsEllSequence (x • W)`.

Source (project, line 621):
```lean
lemma IsEllSequence.smul (h : IsEllSequence W) (x : R) : IsEllSequence (x • W) :=
  fun m n r ↦ by
    have key := h m n r
    show Rel₃ (x • W) m n r
    simp only [Rel₃, Pi.smul_apply, smul_eq_mul] at key ⊢
    linear_combination (norm := ring) x ^ 4 * key
```

---

### Size classification (Phase 2a)

Verdict: **SMALL** — a one-step closure property (scalar multiple) of the `IsEllSequence` predicate;
a helper lemma, not a main result, not named after a person/place. (Lit width exhaustive regardless.)

### One-line check (Phase 2b)

n/a — kind is `lemma`, not a definition. The one-liner negative signal applies to defs only.

---

### Literature search table (Phase 3)

The declaration is **already a verbatim fork of a mathlib lemma** (Phase 5), which settles the
"standard form" question: mathlib — the contemporary literature-standard formalisation, built from
Ward's and Shipsey's EDS theory — already states it in exactly this form. Sweep recorded for completeness.

| #  | Channel                          | Query                                                                                 | Hit? | Standard form found                                              | Notes |
|----|----------------------------------|---------------------------------------------------------------------------------------|------|------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic divisibility sequence" scalar multiple / scaling closure                    | yes  | EDS / elliptic-net theory closed under scaling of terms          | Ward (1948) "Memoir on EDS"; Shipsey thesis; `c·W` stays elliptic |
|  2 | WebSearch (general form)         | "elliptic sequence" recurrence homogeneous degree scaling commutative ring            | yes  | relation is homogeneous of degree 4 ⇒ invariant under `W ↦ x·W`  | degree-4 homogeneity is the textbook reason |
|  3 | WebSearch (named-after/aliases)  | "elliptic net" / "Somos sequence" scaling closure                                     | yes  | same; elliptic nets (Stange) generalise; scaling-closed          | name varies (sequence / net); property standard |
|  4 | ChatGPT MCP                      | (MCP down per task note — fallback to WebSearch + mathlib source as the literature)    | n/a  | mathlib EDS file is the modern reference formulation             | MCP unavailable here; mathlib source consulted instead |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/` for "elliptic"/"smul"          | n/a  | (none decisive)                                                  | not the bottleneck — mathlib has the exact decl |
|  6 | nLab                             | "elliptic divisibility sequence"                                                       | no   | no dedicated EDS page                                            | n/a — not a category-theoretic concept |
|  7 | nCatLab                          | —                                                                                     | n/a  | —                                                                | n/a — not categorical |
|  8 | Stacks Project                   | "elliptic divisibility sequence"                                                       | no   | not in Stacks                                                    | n/a — arithmetic-of-EDS, not scheme theory |
|  9 | MathOverflow / MSE               | "elliptic divisibility sequence" scaling / multiply by constant                       | yes  | community confirms scaling preserves the EDS relation            | folklore; degree-4 homogeneity argument |
| 10 | recent arXiv (last 5 yrs)        | "elliptic divisibility sequence" / "elliptic net" structural closure                  | yes  | Stange et al. treat scaling/gauge equivalence of nets           | "gauge"/scaling freedom standard in elliptic-net papers |

### Literature summary (Phase 3)

Concept: **closure of elliptic (divisibility) sequences under term-wise scalar multiplication** — a
structural property of the EDS relation.
Sources agree on the standard form: **yes** — the relation is degree-4 homogeneous, so scaling all
terms by a constant preserves it (folklore in Ward/Shipsey/Stange EDS theory).
Most general standard form: over any commutative ring `R`, for `W : ℤ → R` and `x : R`, `x • W` is
elliptic whenever `W` is. **This is precisely the mathlib statement.**
Generality variation: essentially none for this micro-lemma; the natural home is "commutative ring of
coefficients", which both the literature argument and mathlib use.
Disagreement with the literature: none.

---

### Generality analysis (Phase 4)

Literature-standard form (Phase 3): over a commutative ring `R`, scaling an elliptic sequence by `x : R`
yields an elliptic sequence. (Matches mathlib's `[CommRing R]` form.)

| # | Parameter / hypothesis      | Current Lean form        | Literature-standard form         | Weaker form exists? | Reason |
|---|-----------------------------|--------------------------|----------------------------------|---------------------|--------|
| 1 | `[CommRing R]`              | commutative ring         | commutative ring                 | NO                  | the EDS relation uses `+ − ·` and commutativity (degree-4 product matched both sides); `CommRing` is exactly right and matches mathlib |
| 2 | `(x : R)`                   | ring element scalar      | ring element scalar              | NO                  | the scaling factor lives in the same ring; `x • W = (x · ·) ∘ W` via `Pi.smul`/`smul_eq_mul` |
| 3 | `(h : IsEllSequence W)`     | EDS hypothesis           | EDS hypothesis                   | NO                  | the defining hypothesis; cannot be weakened |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (and identical to mathlib's). Weakening opportunities: 0.
Proposed restatement: none — already at the natural generality (`CommRing`). Cost: n/a.

### Modern-idiom check (Phase 4c)

| # | Question                                                          | Applies? | Note |
|---|-------------------------------------------------------------------|----------|------|
| 1 | bundled hypotheses → typeclasses?                                 | no       | only hypothesis is the predicate `IsEllSequence W` |
| 2 | sequences/metric → filters/topology?                              | no       | purely algebraic identity; no topology |
| 3 | construction → universal property?                               | no       | no object constructed |
| 4 | set+closure-pred → bundled substructure?                         | no       | `IsEllSequence` is a `Prop`, appropriately |
| 5 | vector-space/field-specific → weaken typeclass?                  | no       | already `CommRing` (mathlib's choice) |
| 6 | 1-categorical → higher-categorical?                              | no       | n/a |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary group/monoid?                 | no       | EDS are definitionally ℤ-indexed (Ward); not a generalisation axis |

Modern idiom available: **no** — this is an algebraic closure lemma already stated in mathlib's own
(contemporary) EDS formulation at the right generality; mathlib *is* the modern idiom here, and it
agrees with the project's form line-for-line.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `IsEllSequence.smul` (Phase 5)

[A] Lean-Finder       "elliptic sequence scalar multiple"          → hit (EDS file)
[B] Loogle            `IsEllSequence (_ • _)`, `IsEllSequence _ → IsEllSequence (_ • _)` → hit
[C] LeanSearch        "scalar multiple of an elliptic sequence is elliptic" → hit
[D] Grep mathlib src  `IsEllSequence.smul` in `.lake/packages/mathlib/`     → **direct hit**
[E] Name pattern      `IsEllSequence.smul`                          → **direct hit**

**Direct source hit** in the project's *own pinned* mathlib,
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:106`:

```lean
lemma IsEllSequence.smul (h : IsEllSequence W) (x : R) : IsEllSequence (x • W) :=
  fun m n r => by
    linear_combination (norm := (simp_rw [Pi.smul_apply, smul_eq_mul]; ring1)) x ^ 4 * h m n r
```

This is **the same lemma** as project line 621:
- Same qualified name: `IsEllSequence.smul`.
- Same context: `variable {R : Type u} [CommRing R]`, `W : ℤ → R` in both (project line 85; mathlib
  lines 75/79).
- Same statement: `(h : IsEllSequence W) (x : R) : IsEllSequence (x • W)`.
- Same proof idea: `linear_combination x ^ 4 * (relation for W)` (degree-4 homogeneity). Only cosmetic
  difference — the project does `simp only [Rel₃, Pi.smul_apply, smul_eq_mul] at key ⊢` then
  `linear_combination (norm := ring) x ^ 4 * key`; mathlib inlines the `simp_rw` into the
  `linear_combination` `norm`. Mathematically identical.

The project file **redeclares** mathlib's EDS theory rather than importing it (it imports neither
`Mathlib.NumberTheory.EllipticDivisibilitySequence` nor the `DivisionPolynomial` track). A third copy
of the lemma lives at `EllipticDivisibilitySequenceOriginal.lean:596`. This is the documented "FORKS
parts of mathlib" pattern. Upstream original on disk:
`/Users/mcu22seu/Documents/GitHub/aintlib-main/.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:106`.

Concluded: **found in mathlib as `IsEllSequence.smul`; identical form.**

---

### Composition check (Phase 6)

#### Call sites — `IsEllSequence.smul`

Internal use count (this file, excluding the decl itself): **1**
- `EllipticDivisibilitySequence.lean:1271`: `@IsEllSequence.ext _ _ _ _ ellW (IsEllSequence.smul IsEllSequence.normEDS _)`

The sibling `IsEllDivSequence.smul` (line 631) also consumes it via `h.left.smul x`. Fork copy
`EllipticDivisibilitySequenceOriginal.lean:1207` uses its own copy (`IsEllSequence.normEDS.smul _`) —
not a consumer of *this* decl, but evidence the lemma is needed across the fork.
Inline-derivation grep: invoked by name, not re-derived inline. (none)

#### Composition

Moot — Phase 5 found the **exact** decl in mathlib. The "composition" is the trivial identity: the
project's lemma *is* mathlib's lemma. Nothing to assemble from primitives.

Conclusion: **n/a (NO-mathlib-has-it supersedes)** — mathlib has the exact statement.

---

## Verdict: `IsEllSequence.smul`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature (Phase 3): folklore (Ward/Shipsey/Stange EDS theory); the EDS relation is degree-4
  homogeneous, so scaling preserves it — and mathlib already encodes exactly this.
- Generality (Phase 4): MAXIMALLY GENERAL; identical to mathlib's `[CommRing R]` form; no modern-idiom
  improvement (mathlib is the modern idiom).
- Mathlib search (Phase 5): **found as `IsEllSequence.smul`** at
  `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:106` — identical statement, namespace,
  `CommRing` context, equivalent proof.
- Composition (Phase 6): n/a — exact decl already in mathlib.

**Rationale:**

The NagellLutz project forks mathlib's elliptic-divisibility-sequence theory
(`Mathlib.NumberTheory.EllipticDivisibilitySequence`, by David Kurniadi Angdinata) into its own file
instead of importing it, and `IsEllSequence.smul` at line 621 is a **verbatim duplicate** of the
mathlib lemma at line 106. They share the same qualified name, the same ambient context
(`{R} [CommRing R]`, `W : ℤ → R`, `{W}`), the same signature
(`(h : IsEllSequence W) (x : R) : IsEllSequence (x • W)`), and the same degree-4-homogeneity proof —
differing only cosmetically in where the `Pi.smul_apply`/`smul_eq_mul` rewrite sits relative to
`linear_combination`. This is the textbook scaling-closure of elliptic sequences; mathlib has had it
since the EDS theory landed.

**WHY not (refactor-actionable):**
Mathlib already provides this lemma identically. The project carries it only because the whole
`IsEllSequence`/`Rel₃`/`normEDS` block was forked (the file imports neither
`Mathlib.NumberTheory.EllipticDivisibilitySequence` nor the `DivisionPolynomial` track, and a second
copy lives in `EllipticDivisibilitySequenceOriginal.lean:596`). The project's form follows from
mathlib's in **0 lines** — it *is* mathlib's lemma:
```lean
example {R : Type*} [CommRing R] {W : ℤ → R} (h : IsEllSequence W) (x : R) :
    IsEllSequence (x • W) := h.smul x   -- mathlib's IsEllSequence.smul
```

Existing mathlib decl:        `IsEllSequence.smul`
Located at:                   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:106`
Call sites in our project (Phase 6.0):  K = 1 (line 1271 here; the line-631 sibling also consumes it
                              via `h.left.smul`; plus 1 in the sibling fork copy)

Refactor plan — this is **dedup-against-mathlib**, NOT an upstreaming target (do **not** open a mathlib
PR; mathlib already has it). Collapse the fork onto the upstream theory:
1. Depend on mathlib's `Mathlib.NumberTheory.EllipticDivisibilitySequence` for the EDS predicates and
   their closure lemmas (`IsEllSequence`, `IsDivSequence`, `IsEllDivSequence`, the three `.smul`
   lemmas, the `.map` lemmas, `isEllSequence_id`, …) instead of redeclaring them.
2. **Divergence caveat (does not affect this lemma).** The fork's `IsDivSequence` is ℤ-indexed
   (project line 602) whereas mathlib's is ℕ-indexed (mathlib line 87). That divergence lives in
   `IsDivSequence`, NOT in `IsEllSequence` or its `.smul` — so `IsEllSequence.smul` is unambiguously
   already in mathlib and unaffected.
3. Call site line 1271 (and `EllipticDivisibilitySequenceOriginal.lean:1207`) already use the mathlib
   API shape (`IsEllSequence.smul …`); once the import replaces the local redeclaration they resolve to
   mathlib's lemma unchanged. No argument-order edits needed.
4. Delete the local `IsEllSequence.smul` (line 621) once the fork imports the upstream file.

Caveat for the de-fork: the file is a forked/extended track that adds substantial *new* theory (`rel₄`,
the odd/even-recurrence ⇒ `IsEllSequence` bridge `of_oddRec_evenRec`, `normEDS` being an EDS). De-forking
is a larger structural task than this one lemma; the per-decl verdict is simply that **this specific
lemma is redundant with mathlib** and should not be re-contributed. Mechanical action: "delete on
de-fork; it already exists upstream."

---

## Next step

Do not open a mathlib PR — `IsEllSequence.smul` is already in mathlib at
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:106`, identical. Delete the project's duplicate
(line 621) as part of collapsing the forked EDS block onto an `import` of
`Mathlib.NumberTheory.EllipticDivisibilitySequence`; the in-file call site (line 1271) already uses the
mathlib API shape and needs no change. The `IsDivSequence` ℤ-vs-ℕ divergence is a separate consolidation
concern and does not touch this lemma.
