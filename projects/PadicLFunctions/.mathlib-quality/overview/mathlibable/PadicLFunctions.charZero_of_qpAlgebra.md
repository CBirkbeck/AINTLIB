# `/mathlibable` report — `PadicLFunctions.charZero_of_qpAlgebra`

## Verdict (summary)

**`NO-composable-from-mathlib`** — the lemma is a verbatim one-call specialisation of
mathlib's `charZero_of_injective_algebraMap`. Mathlib already supplies the building block;
no new lemma is justified. Inline `charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective`
at each of the 5 call sites and delete the wrapper.

---

### Baseline (Phase 0)

- lake build:               build NOT re-run (per task BUILD NOTE — stale/slow); reasoned from source
- decl `PadicLFunctions.charZero_of_qpAlgebra`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/Coefficients.lean:114`
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  Coefficient rings for §5 — the integer ring (norm-unit ball) of a nonarchimedean complete normed `ℚ_[p]`-algebra field, plus root-of-unity norm facts (W1/W2/W3).

---

### Statement (Phase 1)

`PadicLFunctions.charZero_of_qpAlgebra` is a lemma stating the following:

> Let `M` be a normed field that is a normed `ℚ_q`-algebra (for `q` prime). Then `M` has
> characteristic zero.

Mathematically this is the trivial chain: `ℚ_q` has characteristic zero (it contains `ℚ`),
the algebra structure map `ℚ_q → M` is a ring homomorphism between fields hence injective,
and an injective ring map out of a characteristic-zero ring forces the target to be
characteristic zero (the composite `ℤ → ℚ_q → M` is injective).

Variables / typeclasses involved (Lean side):
- `(q : ℕ) [Fact q.Prime]` — the residue prime; an explicit argument because, as the docstring
  notes, `q` is not determined by the goal `CharZero M`, so this is deliberately **not** an instance.
- `{M : Type*} [NormedField M]` — the target field.
- `[NormedAlgebra ℚ_[q] M]` — `M` is a normed `ℚ_q`-algebra (gives the `Algebra ℚ_[q] M` structure).

Hypotheses (Lean side): none beyond the typeclass context.

Conclusion (math): `M` has characteristic zero.

Conclusion (Lean): `CharZero M`.

Proof body (one line):
```lean
charZero_of_injective_algebraMap (algebraMap ℚ_[q] M).injective
```

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper lemma deriving a standard typeclass instance (`CharZero`) by a single
specialisation of an existing mathlib result; not a named theorem, not a new structure, not
a primary project goal (W1/W2/W3 in the module docstring are the main results — this is glue).

(Note: literature width is EXHAUSTIVE regardless. SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Body line count: 1 substantive line
One-liner verdict: n/a — kind is `lemma`, not `def`/`abbrev`/`structure`.

The Phase-2b def-exemption table is for definitions (defeq abuse / diamonds / API-name
stability). A `lemma` introduces no definitional equality or typeclass-search path, so the
table does not apply. Recorded as n/a. (The "is this a thin wrapper?" question is still live
and is handled properly in Phases 5–6, where it is decisive.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query | Hit? | Standard form found | Notes |
|----|----------------------------------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "algebra over a field of characteristic zero has characteristic zero injective" | yes | char 0 ⟺ `ℤ → R` injective; injective map preserves it | nLab *characteristic zero*; Stacks *Fields* 09FA; Wikipedia *Characteristic (algebra)* |
| 2 | WebSearch (general form) | "p-adic field Q_p characteristic zero extension finite extension char 0" | yes | `ℚ_p` has char 0; every finite/any extension of `ℚ_p` has char 0 | UChicago REU (Turner), Mustață *Basics of p-adic fields*, Fiveable ANT notes |
| 3 | WebSearch (named-after / aliases) | (covered by #1/#2 — concept has no eponym) | yes | "extension of a char-0 field is char-0"; "subfield of char-0 ring" | the result is folklore/elementary; no person/place name attaches |
| 4 | ChatGPT MCP | "standard form + generality + historical evolution of 'an algebra over a char-0 field is char-0'" | n/a | — | ChatGPT MCP not configured in this environment (`/setup-chatgpt` not run). Recorded n/a; channels 1–10 otherwise cover the standard form and generality fully. |
| 5 | Local references | scan `projects/PadicLFunctions/.mathlib-quality/` and `refs/` | n/a | (no references dir) | `.mathlib-quality/references/` absent; `refs/` absent. Recorded n/a. |
| 6 | nLab | "characteristic zero" | yes | "ring has char 0 iff unique map `ℤ → R` is injective" | ncatlab.org/nlab/show/characteristic+zero — confirms the injectivity characterisation the mathlib lemma uses |
| 7 | nCatLab (categorical) | — | n/a | — | Not a categorical concept; the injectivity statement is already the clean abstract form. n/a. |
| 8 | Stacks Project (alg geom) | "Fields — characteristic" (tag 09FA) | yes | char of a field is 0 or prime; char 0 ⟺ `ℚ ⊆ R` | stacks.math.columbia.edu — *Fields* chapter; standard char-0 development |
| 9 | MathOverflow / Math.SE | "extension of characteristic zero field is characteristic zero" | yes | universally answered: composite `ℤ → K → L` injective | folklore; no controversy over the statement or its generality |
| 10 | recent arXiv (last 5 yrs) | "p-adic / characteristic zero / finite extension" | yes (tangential) | papers *use* "`ℚ_p` and its extensions have char 0" as a given, never as a result | arXiv:1808.10155, 2209.01069 etc. treat it as background, confirming it is textbook-level |

The protocol passed: WebSearch ran 3 distinct queries at different generality levels;
local references checked (absent → n/a); nLab checked (hit); Stacks / nCatLab / MathOverflow /
arXiv each checked with reason. ChatGPT MCP unavailable in this environment → n/a with reason.

### Literature summary (Phase 3)

Concept identified as: *"an algebra (or extension) over a characteristic-zero (semi)ring is
characteristic zero, because an injective ring homomorphism preserves characteristic zero"* —
specialised here to the base field `ℚ_q`.

Sources agree on the standard form: **yes**. The universal characterisation is "`R` has
characteristic zero iff the canonical `ℤ → R` is injective" (nLab, Stacks), and the
preservation result is "if `f : R → A` is an injective ring hom and `R` has char 0, then so
does `A`". The base fact "`ℚ_p` has characteristic zero" is textbook (it contains `ℚ`).

Most general standard form: for a commutative (semi)ring `R` and a (semi)ring `A` with an
injective ring homomorphism `R → A`, `CharZero R → CharZero A`. The "algebra over a field"
phrasing is a specialisation (algebra map; base is a field so the map is automatically
injective).

Generality dimensions where the literature varies:
- base object: from "field of char 0" (textbook) up to "commutative semiring of char 0" (the
  injective-ring-hom form). The most general is the semiring/injective-hom form.
- the map: "field extension" → "injective ring hom" → "algebra map (auto-injective when base is a field)".

Disagreement with the literature: **none**. The user's lemma is a faithful specialisation of
the standard injective-hom result to `R = ℚ_q`, `A = M`.

---

### Generality analysis — `PadicLFunctions.charZero_of_qpAlgebra`

Literature-standard form (from Phase 3): for a `CommSemiring R` with `[CharZero R]`, a
`Semiring A`, and an injective `algebraMap R A` (or any injective ring hom `R → A`), `A` is
`CharZero`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | base ring `ℚ_[q]` | the specific char-0 field `ℚ_q` | any `CommSemiring R` with `[CharZero R]` | yes | the proof uses only `CharZero ℚ_[q]` + injectivity; mathlib's `charZero_of_injective_algebraMap` already states the general form |
| 2 | `[NormedField M]` | normed field | `Semiring A` (no norm, no field) | yes | norm and field structure are never used; `charZero_of_injective_algebraMap` needs only `[Semiring A] [Algebra R A]` |
| 3 | `[NormedAlgebra ℚ_[q] M]` | normed algebra | `[Algebra R A]` + injectivity of `algebraMap` | yes | only the (injective) `algebraMap` is used; the norm-compatibility of `NormedAlgebra` is irrelevant |
| 4 | `(q : ℕ) [Fact q.Prime]` | a prime index | n/a — disappears in the general form | yes | `q` is only there to name `ℚ_[q]`; the general `R`-form has no prime at all |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (it fixes `R = ℚ_q`, demands a norm
and a field where none is needed).

Number of weakening opportunities found: 4.

However — and this is the decisive point — the maximally general form (rows 1–4 fully
weakened) **is exactly mathlib's existing `charZero_of_injective_algebraMap`**
(`Mathlib/Algebra/CharP/Algebra.lean:77`). So this is not a "generalise then PR" situation:
generalising lands you *on a theorem mathlib already has*. The correct conclusion is therefore
NO (mathlib has the general form), and the only question is whether the `ℚ_q`-specialisation
itself is worth keeping as a named lemma — answered "no" in Phases 5–6 (it is a one-call
composition with `K = 0` non-`haveI` re-derivations and an exact mathlib precedent).

Proposed restatement: not applicable as a contribution — the generalised statement coincides
with an existing mathlib decl. (See Phase 5/7.)

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|---------------------------------|
| 1 | "let X be a foo" preambles → typeclasses/instances? | no | already typeclass-driven (`[NormedAlgebra …]`); the *output* `CharZero M` is itself the instance consumers want | — |
| 2 | sequences/metric → filters/topological? | no | no limiting/topological content; purely algebraic char statement | — |
| 3 | construct an object → universal-property class? | no | nothing is constructed; it derives a `Prop`-valued class | — |
| 4 | set-with-closure-predicate → bundled substructure? | no | no substructure involved | — |
| 5 | vector-space/metric/field-specific → weaker typeclass? | yes | drop `NormedField`/`NormedAlgebra` to `Semiring`+`Algebra`+injective map | exactly `charZero_of_injective_algebraMap` — **already in mathlib**, so the "modernisation" is to *use that decl*, not add a new one |
| 6 | 1-categorical → higher-categorical? | no | n/a | — |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive structure? | no (the `ℚ_q` here is the *base ring*, row 5 covers it) | — | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes**, but it is *not a new contribution* — the "modernised"
(typeclass-weakened) form is the pre-existing `charZero_of_injective_algebraMap`. The only
mathlib-idiomatic move is to delete the wrapper and call that lemma directly. This therefore
does **not** flip the verdict to `YES-but-generalise-first`: the generalisation target already
lives in mathlib, so the verdict gate's "modern-idiom ⇒ generalise-first" branch does not fire
(that branch requires the modern form to be *missing* from mathlib).

---

### Diamond / defeq risk — `PadicLFunctions.charZero_of_qpAlgebra`

n/a — declaration kind is `lemma` (Phase 4.5 runs only for `def`/`abbrev`/`structure`/
`inductive`/`class`/`instance`). A lemma proving `CharZero M` introduces no definitional
equality and no typeclass-search path of its own.

---

### Mathlib search-status: `PadicLFunctions.charZero_of_qpAlgebra`

[A] Lean-Finder — n/a in this environment (no MCP/web Lean-Finder access); substituted by
    direct mathlib-source grep (method D) + name-pattern (method E), both of which hit.
[B] Loogle — pattern `Function.Injective (algebraMap _ _) → CharZero _` / `CharZero _ → CharZero _`
    — n/a as a live API call here; the corresponding decl was located directly via grep (D): it
    is `charZero_of_injective_algebraMap`, whose signature is exactly this shape.
[C] LeanSearch — "characteristic zero from injective algebra map" / "algebra over char zero
    field is char zero" — n/a as a live call; the natural-language target is
    `charZero_of_injective_algebraMap` (confirmed by D).
[D] Grep mathlib src — `grep -rn "charZero_of_injective_algebraMap"` →
    **HIT**. Definition at `Mathlib/Algebra/CharP/Algebra.lean:77`:
    ```lean
    theorem charZero_of_injective_algebraMap [CommSemiring R] [Semiring A] [Algebra R A]
        (h : Function.Injective (algebraMap R A)) [CharZero R] : CharZero A
    ```
    Plus the sibling `charZero_of_injective_ringHom` (line 72). Also found mathlib using the
    *exact* `(algebraMap ℚ_[p] _).injective` pattern at
    `Mathlib/NumberTheory/Padics/Complex.lean:131` (for `PadicAlgCl`/`ℂ_p`), and the
    `charZero_of_injective_algebraMap (algebraMap K L).injective` idiom across
    `NumberField/Basic.lean`, `Cyclotomic/Basic.lean`, `IntermediateField.lean`,
    `SplittingField/Construction.lean`, `AlgebraicClosure.lean` — i.e. this is the
    canonical mathlib way to get `CharZero` of an extension/algebra.
[E] Name pattern — `grep` for `charZero.*Padic` / `charZero.*NormedAlgebra` /
    `charZero_of_qp` in mathlib → **no `ℚ_p`-specific char-zero helper exists**; mathlib
    expects you to call the general `charZero_of_injective_algebraMap`. Confirms there is no
    narrower mathlib lemma to specialise from and none is wanted.

Searched for both:
- the user's current form (p-adic-specific `CharZero` helper): **not in mathlib** — and
  intentionally so (method E).
- the literature-standard / general form (injective-hom ⇒ `CharZero`): **found in mathlib**
  as `charZero_of_injective_algebraMap` (and `charZero_of_injective_ringHom`).

Concluded: **found building blocks** — `charZero_of_injective_algebraMap`
(`Mathlib/Algebra/CharP/Algebra.lean:77`); composition with `(algebraMap ℚ_[q] M).injective`
yields the user's form in one call. (`ℚ_[q]` carries `CharZero` via
`Mathlib/NumberTheory/Padics/PadicNumbers.lean:561`, supplying the required `[CharZero R]`
instance automatically.)

---

### Call sites — `PadicLFunctions.charZero_of_qpAlgebra`

Internal use count: **5** (within the project, NOT counting the declaring file).
External-to-file callers: **2 distinct files** (`ValuesAtOne.lean`, `MeasureR/FormalPsi.lean`).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `projects/PadicLFunctions/PadicLFunctions/ValuesAtOne.lean:640` | `haveI := charZero_of_qpAlgebra (M := K) p` |
| `projects/PadicLFunctions/PadicLFunctions/MeasureR/FormalPsi.lean:1173` | `haveI := charZero_of_qpAlgebra (M := K) p` |
| `projects/PadicLFunctions/PadicLFunctions/MeasureR/FormalPsi.lean:1200` | `haveI := charZero_of_qpAlgebra (M := K) p` |
| `projects/PadicLFunctions/PadicLFunctions/MeasureR/FormalPsi.lean:1242` | `haveI := charZero_of_qpAlgebra (M := K) p` |
| `projects/PadicLFunctions/PadicLFunctions/MeasureR/FormalPsi.lean:1268` | `haveI := charZero_of_qpAlgebra (M := K) p` |

Every call site uses it identically: `haveI := charZero_of_qpAlgebra (M := K) p` to install a
`CharZero K` instance in a context where `K` is a normed `ℚ_[p]`-algebra field. The argument
`p` is the project's ambient prime; `(M := K)` pins the target.

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?):
- (none found) — the project routes all five `CharZero`-of-`K` needs through this one wrapper.

What the pattern says: `K ≥ 3` internal uses with no inline re-derivation is normally a
"real API ⇒ lean YES" signal. But that heuristic is overridden here because (a) the wrapper is
a **single mathlib call** (Phase 6 COMPOSABLE) and (b) mathlib's `charZero_of_injective_algebraMap`
is the established, widely-used way to do exactly this (Phase 5, method D). The five uses are
genuine but they are five uses of *mathlib's lemma wearing a project alias* — they migrate to
the direct mathlib call mechanically. So the verdict is `NO-composable-from-mathlib`, not YES.

---

### Composition check (Phase 6)

Can `PadicLFunctions.charZero_of_qpAlgebra` be derived from mathlib in ≤3 chained calls?

Attempt 1: `charZero_of_injective_algebraMap (algebraMap ℚ_[q] M).injective`
  - Mathlib decls used: `charZero_of_injective_algebraMap` (`Mathlib/Algebra/CharP/Algebra.lean:77`);
    `RingHom.injective` (injectivity of a ring hom out of a field — standard); the
    `CharZero ℚ_[q]` instance (`Mathlib/NumberTheory/Padics/PadicNumbers.lean:561`) is found
    by typeclass search and supplies the lemma's `[CharZero R]` requirement.
  - Result: **succeeds** — this is literally the lemma's own proof body, a single function
    application (one mathlib call).
  - Notes: `(algebraMap ℚ_[q] M)` is a `RingHom` (`NormedAlgebra` ⇒ `Algebra` ⇒ `algebraMap`),
    so `.injective` is the standard field-hom injectivity; no extra reasoning needed.

Per the Phase-6 heuristics table, `Foo.bar (Baz.qux hx)` (one function call with a projection
on an existing term) is **composable**. This is precisely that shape:
`charZero_of_injective_algebraMap ((algebraMap ℚ_[q] M).injective)`.

Conclusion: **COMPOSABLE** (1 mathlib call; ≤3 satisfied with room to spare).

---

## Verdict: `PadicLFunctions.charZero_of_qpAlgebra`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the concept is textbook — "char 0 ⟺ `ℤ → R` injective"
  (nLab, Stacks); "injective ring hom preserves char 0"; "`ℚ_p` has char 0". No eponym, no
  generality controversy. Sources agree on the standard form.
- Generality analysis (Phase 4): STRICTLY NARROWER than standard — but the fully-general form
  *is itself a mathlib lemma* (`charZero_of_injective_algebraMap`), so generalising would
  duplicate mathlib, not contribute. Modern-idiom check (4c) reaches the same decl.
- Mathlib search (Phase 5): found the building block `charZero_of_injective_algebraMap`
  (`Mathlib/Algebra/CharP/Algebra.lean:77`); mathlib itself uses the identical
  `(algebraMap ℚ_[p] _).injective` pattern (`Padics/Complex.lean:131`). No `ℚ_p`-specific
  char-zero helper exists in mathlib, and none is wanted (method E).
- Composition check (Phase 6): COMPOSABLE — the proof body is a single mathlib call.

**Rationale:**

`charZero_of_qpAlgebra` adds no new mathematical content over mathlib. Its entire proof is the
one expression `charZero_of_injective_algebraMap (algebraMap ℚ_[q] M).injective`, where
`charZero_of_injective_algebraMap` is an existing mathlib theorem and `CharZero ℚ_[q]` is an
existing mathlib instance. Mathlib not only has the general lemma, it *demonstrates this exact
specialisation pattern itself* for the p-adic case at `Padics/Complex.lean:131` (deriving
`CharZero (PadicAlgCl p)` via `(algebraMap ℚ_[p] _).injective`), and uses the same idiom
throughout `NumberField`, `Cyclotomic`, `SplittingField`, `IntermediateField`, and
`AlgebraicClosure`. The `[NormedField M]` and `[NormedAlgebra ℚ_[q] M]` hypotheses are heavier
than the proof uses (only `[Algebra ℚ_[q] M]` and the injective `algebraMap` are touched), so
even on its own terms the statement is over-specialised; weakening it merely reproduces
`charZero_of_injective_algebraMap`. This is a thin wrapper, and per the project's own cleanup
rules (mathlib-search.md Rule 1, "no wrapper lemmas") the right move is to delete it and call
mathlib directly.

This is a textbook `NO-composable-from-mathlib` (directly parallel to mathlibable-verdicts.md
Case 4): mathlib has the building block, the user's form is a ≤3-call composition, and no new
lemma is justified.

**WHY not (refactor-actionable detail):**
Mathlib has the building block `charZero_of_injective_algebraMap` (and the underlying
`charZero_of_injective_ringHom`). For the base `ℚ_[q]`, mathlib's `CharZero ℚ_[q]` instance
(`PadicNumbers.lean:561`) discharges the `[CharZero R]` hypothesis automatically, so the only
thing the call site supplies is `(algebraMap ℚ_[p] K).injective`. The composition is
mechanical and is exactly what mathlib already does for `ℂ_p`/`PadicAlgCl`.

Mathlib building blocks:
- `charZero_of_injective_algebraMap` — `Mathlib/Algebra/CharP/Algebra.lean:77`
- (instance) `CharZero ℚ_[p]` — `Mathlib/NumberTheory/Padics/PadicNumbers.lean:561`
- `RingHom.injective` for the field hom `algebraMap ℚ_[p] K` (standard).

Composition sketch (≤3 lines — drop-in for the wrapper):
```lean
-- where the project currently writes:  haveI := charZero_of_qpAlgebra (M := K) p
haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
```

Call sites in our project (from Phase 6.0): **K = 5**
- `ValuesAtOne.lean:640`
- `FormalPsi.lean:1173`, `1200`, `1242`, `1268`

Refactor plan: at each of the 5 call sites, replace
`haveI := charZero_of_qpAlgebra (M := K) p`
with
`haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective`.
The ambient prime is `p` (not `q`) at every site, and `K` is the local normed `ℚ_[p]`-algebra
field, so the substitution is uniform; no argument-order subtleties (the `(M := K) p`
named/positional args of the wrapper disappear — the mathlib call takes the algebra map
explicitly and finds `CharZero ℚ_[p]` by instance search). After the 5 edits, delete
`charZero_of_qpAlgebra` from `Coefficients.lean:112–116` (including its docstring). The
declaring file's docstring may optionally gain a "Mathlib lemmas used directly:
`charZero_of_injective_algebraMap`" note per mathlib-search.md Rule 6, though that is
cleanup-discretionary.

Next action: delete `PadicLFunctions.charZero_of_qpAlgebra`; inline
`charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective` at the 5 call sites above.

(Caveat — this is a *project-cleanup* action on `main`, not a mathlib PR. The verdict answers
"should mathlib have this?": no — mathlib already does, via the general lemma. Confirm a
`lake build` after the inlining, which was not re-run for this assessment per the task's BUILD
NOTE.)

---

## Next step

Delete `PadicLFunctions.charZero_of_qpAlgebra` from
`projects/PadicLFunctions/PadicLFunctions/Coefficients.lean` and, at each of the 5 call sites
(`ValuesAtOne.lean:640`; `FormalPsi.lean:1173, 1200, 1242, 1268`), inline the single mathlib
call `haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective`.
