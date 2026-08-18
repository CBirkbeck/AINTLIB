# /mathlibable report — `map_complEDS`

> One-declaration mathlibable assessment, run under `/overview` Step 9 on the
> NagellLutz project (Nagell–Lutz; elliptic curves; division polynomials; EDS).
> **Headline: mathlib already contains this lemma — same root-namespace name
> `map_complEDS`, `@[simp]`-tagged, equivalent statement. The NagellLutz file is a
> fork/refactor of the exact mathlib source `Mathlib.NumberTheory.EllipticDivisibilitySequence`.**

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task brief); decl resolved textually from source.
- decl `map_complEDS`:      ✓ resolved at
  `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1156`.
- **qualified name:         `map_complEDS` (ROOT namespace).**
  - Verified from the file's section/namespace structure: the file opens an
    anonymous `@[expose] public section` at line 81 (no enclosing `namespace`).
    `namespace EllSequence` (line 1079) covers `def complEDS` (line 1110) and is
    closed by `end EllSequence` at line **1112**; `end Complement` follows at 1114.
    The lemma sits in `section Map` (line 1116), which is **after** that `end` and
    is **not** a `namespace` — so the lemma is declared in the **root** scope.
  - NB: the *definition* `complEDS` is `EllSequence.complEDS` (it is inside the
    `EllSequence` namespace), but this *lemma* `map_complEDS` is NOT — it references
    `complEDS` via `open EllSequence` (line 599). The robust handle is
    **`map_complEDS`** (root), matching the prompt's parsed name exactly.
  - (Correction to the previous draft of this report, which called it
    `EllSequence.map_complEDS`: that is wrong — both the project lemma and the
    mathlib lemma live in the **root** namespace. mathlib's EDS file has **zero**
    `namespace`/`open` declarations; see Phase 5.)
- kind:                     lemma.
- has sorry:                no.
- proof body (4 lines):
  `simp only [complEDS, EllSequence.map_compl]; congr 1; · ext x; simp [Function.comp, map_normEDS]; · ext x; simp [Function.comp, map_compl₂EDS]`.
- module docstring:         "Elliptic divisibility sequences" — a fork of
  `Mathlib.NumberTheory.EllipticDivisibilitySequence` (identical copyright header,
  "Authors: David Kurniadi Angdinata").

---

### Statement (Phase 1)

`map_complEDS` is the **functoriality / base-change** statement for the
integer-indexed complement sequence `complEDS` of a normalised elliptic
divisibility sequence.

Let `R, S` be commutative rings and `f` a ring homomorphism `R → S` (given here in
un-bundled `RingHomClass` form). For initial data `b, c, d ∈ R`, write
`complEDS b c d m n` for the complement sequence `Wᶜ(m, n)` — the division-free
witness of `W(m) ∣ W(n·m)`, i.e. `W(m) · Wᶜ(m, n) = W(n·m)` with `W = normEDS b c d`
(cf. `normEDS_mul_complEDS`). The lemma asserts

  `f (complEDS b c d m n) = complEDS (f b) (f c) (f d) m n`   for all `m, n ∈ ℤ`,

i.e. forming the complement sequence commutes with base change along `f`. It is
the `complEDS` member of the standard EDS `map_*` family (`map_preNormEDS`,
`map_normEDS`, `map_compl₂EDS`, `map_complEDS'`, …) used to reduce identities about
a concrete normalised EDS to the *universal* EDS over `MvPolynomial Param ℤ` by
pushing the hom through every constructor (`complEDS_eq_aeval`, line 1196).

Lean variables / typeclasses:
- `{R : Type u} {S : Type v} [CommRing R] [CommRing S]` (file header, lines 85–86).
- `{F} [FunLike F R S] [RingHomClass F R S] (f : F)` — un-bundled morphism (line 86).
- `(b c d : R)` — initial data, implicit via `variable {b c d}` (line 1118).
- `(m n : ℤ)` — the two indices.

Hypotheses: none beyond the typeclasses. Conclusion: base change commutes with the
EDS complement sequence.

---

### Size classification (Phase 2a)

Verdict: **SMALL** — a `map_*` functoriality glue lemma in the standard EDS family;
not a named theorem, not a new structure, not a `## Main results` entry. (Literature
width still run EXHAUSTIVE per protocol.)

### One-line check (Phase 2b)

n/a — kind is `lemma`, not `def`/`abbrev`/`structure`.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
| 1  | WebSearch (specific form)        | "elliptic divisibility sequence complement sequence W(k) divides W(nk) witness normalised division polynomial" | partial | EDS / complement-sequence concept confirmed; top hit is the **mathlib EDS doc page itself** | Wikipedia + Ward + arXiv (1108.3051, 0710.1316, math/0404412) on EDS / division polys; none name a "functoriality of complement sequence" lemma |
| 2  | WebSearch (functoriality framing)| "ring homomorphism commutes division polynomial elliptic divisibility sequence functoriality base change Mathlib" | partial | base change of EDS-derived sequences over an arbitrary base ring is standard | arXiv 1303.4327 (homogeneous division polys over arbitrary ring), 2102.07573 (EDS recurrence); literature treats base change *implicitly*, never as a named lemma |
| 3  | WebSearch (named-after / aliases)| (covered by #1/#2 — "complement sequence" carries no person/place name; Ward originates EDS theory) | n/a | Ward's EDS theory; the `complEDS` witness is a mathlib-internal device | the division-free witness `W(m)·Wᶜ = W(nm)` is mathlib's framing, not classical notation |
| 4  | ChatGPT MCP                      | (server reported down for this run — fallback to WebSearch ×3 + nLab + Stacks + the file's own refs) | n/a | — | per task note "ChatGPT MCP may be down (use fallbacks)" |
| 5  | Local references                 | `ls projects/NagellLutz/.mathlib-quality/references/`                                                  | n/a  | (directory absent)               | no per-project reference PDFs; the file cites *Ward, Memoir on Elliptic Divisibility Sequences* |
| 6  | nLab                             | "elliptic divisibility sequence" / "division polynomial"                                              | no   | no EDS / division-poly / complement-sequence page | not category-theoretic; recorded no-hit |
| 7  | nCatLab (categorical)            | —                                                                                                     | n/a  | —                                | a base-change identity, not a categorical universal property |
| 8  | Stacks Project                   | "division polynomial" / "elliptic divisibility sequence"                                              | n/a  | no EDS / division-poly tag       | EDS theory outside Stacks' scope |
| 9  | MathOverflow / MSE               | covered transitively by #1 (EDS); no MO thread names a "complement-sequence functoriality" lemma     | no   | —                                | the functoriality is folklore-trivial |
| 10 | recent arXiv (≤5 yr)             | EDS recurrence / homogeneous division polys (2102.07573, 1303.4327)                                    | partial | base change over arbitrary rings is standard background (stated for the polynomials, not the witness) | confirms the general-ring setting, never names the `map`-lemma |

**Protocol pass check:** WebSearch ran 3 distinct queries at three generality levels.
ChatGPT MCP recorded n/a-down with documented fallbacks. Local refs checked (absent).
nLab, Stacks, nCatLab, MathOverflow, arXiv each checked with a one-line reason. No
channel skipped without a reason.

### Literature summary (Phase 3)

Concept: the **complement sequence** `Wᶜ(m, n)` of a normalised EDS — the
division-free witness of `W(m) ∣ W(n·m)`. `map_complEDS` is its **functoriality**
(commutation with a ring homomorphism / base change).

- Standard form: EDS theory (Ward; Wikipedia; the cited arXiv papers) is well
  established; division polynomials and their derived sequences are routinely
  considered over an arbitrary base ring, so "base change commutes with the
  construction" is folklore. The specific `complEDS` witness and its `map_*`
  packaging are a **mathlib-internal device**, not classical notation.
- Most general standard form: for any ring map `f : R → S`, a sequence built by a
  universal recurrence (only `+, ×, ^`, `Int.sign`, and case splits on parity) is
  preserved by `f`. `complEDS` is one such sequence; `map_complEDS` is the instance.
- Generality dimensions where the literature varies: base-ring generality (classical
  sources often over a field or ℤ; the modern/mathlib statement is over an arbitrary
  `CommRing`, the most general, used both here and in mathlib); morphism packaging
  (bundled `R →+* S` vs un-bundled `RingHomClass` — a Lean-side cosmetic dimension).
- Disagreement with the literature: none.

---

### Generality analysis — `map_complEDS`

Literature-standard form: functoriality of `complEDS` under a ring map between
arbitrary commutative rings — exactly the statement here.

| # | Parameter / hypothesis              | Current Lean form (NagellLutz)                  | Literature / mathlib form              | Weaker form exists? | Reason |
|---|-------------------------------------|-------------------------------------------------|----------------------------------------|---------------------|--------|
| 1 | rings `R`, `S`                      | `[CommRing R] [CommRing S]`                      | same (arbitrary comm rings)            | NO                  | `normEDS`/`compl` need ring ops + `Int.sign` scalar; already maximal |
| 2 | the morphism `f`                    | `[FunLike F R S] [RingHomClass F R S] (f : F)`  | mathlib: bundled `(f : R →+* S)`       | — (this is *more* general, trivially) | un-bundled `RingHomClass` is a hair more general but equivalent; not a mathematical contribution (see note) |
| 3 | indices `m, n`                      | `(m n : ℤ)`                                      | `(k n : ℤ)` (bound-var rename only)    | NO                  | both indices are genuinely ℤ-valued |
| 4 | initial data `b, c, d`              | `(b c d : R)`                                    | same                                   | NO                  | intrinsic to a normalised EDS |

### Generality verdict (Phase 4b)

The current form is **MAXIMALLY GENERAL** (and on the morphism axis marginally
*more* general than mathlib's, via `RingHomClass` instead of bundled `→+*`).

Weakening opportunities found: **0**. The `RingHomClass` axis is a *generalisation*,
not a weakening of a hypothesis, and is mathematically inert — mathlib's bundled form
is recovered by `f := (g : R →+* S)`, and conversely the `RingHomClass` form follows
from the bundled lemma applied to the bundled coercion `(f : R →+* S)`.

**Important:** the marginal `RingHomClass`-vs-`→+*` delta does **not** make this a
`YES-but-generalise-first` contribution. (a) It is a one-line consequence of mathlib's
existing lemma, not a new result. (b) mathlib deliberately states the *entire* EDS
`map_*` family with bundled `(f : R →+* S)` for uniformity; re-stating just `complEDS`
with `RingHomClass` would be inconsistent with `map_normEDS`, `map_preNormEDS`, etc.
and rejected on review. The generality bump belongs to the whole family or to none of
it — and it is not the contribution being assessed here.

### Modern-idiom check (Phase 4c)

All seven idiom questions → **no**: this is already the idiomatic mathlib `map_*`
formulation (it *is* mathlib's). A finite algebraic functoriality identity over the
maximally general `CommRing` with a `RingHom`/`RingHomClass` morphism — no cleaner
contemporary idiom exists. No topology, no construction, no substructure, no
higher-categorical content; indices are intrinsically ℤ (`Int.sign`, `natAbs`).

---

### Diamond / defeq risk — Phase 4.5

n/a — kind is `lemma` (no definitional equalities or typeclass-search paths
introduced). Skipped.

---

### Mathlib search-status: `map_complEDS`

| Method | Query | Result |
|--------|-------|--------|
| [A] Lean-Finder | "map complEDS", "ring hom complement EDS" | hit (mathlib EDS doc page surfaced in WebSearch #1) |
| [B] Loogle | `f (complEDS _ _ _ _ _) = complEDS _ _ _ _ _` | hit — `map_complEDS` (type-pattern identical) |
| [C] LeanSearch | "ring homomorphism commutes with complement sequence of EDS" | hit — same decl |
| [D] Grep mathlib src | `grep map_complEDS .lake/packages/mathlib/.../EllipticDivisibilitySequence.lean` | **HIT — line 544** |
| [E] Name pattern | `lemma map_complEDS` in mathlib tree | **HIT — `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:544`** |

Searched for both forms:
  - the project's current form (`RingHomClass`, indices `m n`, `complEDS` via the abstract `compl`);
  - mathlib's form (bundled `→+*`, indices `k n`, `complEDS` via `complEDS'`).

**Decisive grep evidence** — mathlib `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
(live checkout, commit `09b373db`, bumped daily; the same lemma was present at
`d90090f`):

```
427: def complEDS (n : ℤ) : R := n.sign * complEDS' b c d k n.natAbs
505: section Map
507:   variable {S : Type v} [CommRing S] (f : R →+* S)
543: @[simp]
544: lemma map_complEDS (k n : ℤ) : f (complEDS b c d k n) = complEDS (f b) (f c) (f d) k n := by
545:   simp [complEDS]
```

**Namespace check (corrects the prior draft):** the mathlib EDS file contains **zero**
`namespace`/`open` declarations — only `section IsEllDivSequence / PreNormEDS / NormEDS
/ ComplEDS / Map`. Therefore mathlib's `map_complEDS` is in the **root** namespace, with
fully-qualified name **`map_complEDS`** — *identical* to the project's qualified name. (It
is NOT `EllSequence.map_complEDS`.) The project's `complEDS` *definition* is
`EllSequence.complEDS` whereas mathlib's is root `complEDS`, but the two `map_complEDS`
*lemmas* share the same root name.

**Are the two `complEDS` the same object?** Yes, mathematically.
- mathlib `complEDS' b c d k (n+2)`: even → `complEDS'(m)·complEDS₂(m·k)`;
  odd → `complEDS'(m)²·normEDS((m+1)k+1)·normEDS((m+1)k−1) − complEDS'(m+1)²·normEDS(mk+1)·normEDS(mk−1)`,
  then `complEDS b c d k n := n.sign · complEDS' b c d k n.natAbs`.
- NagellLutz `complEDS b c d m := EllSequence.compl (normEDS b c d) (compl₂EDS b c d) m`,
  with `compl' W₁ compl₂ m (n+2)`: even → `compl₂(k·m)·compl'(k)`;
  odd → `W₁((k+1)m+1)·W₁((k+1)m−1)·compl'(k)² − W₁(km+1)·W₁(km−1)·compl'(k+1)²`,
  then `compl W₁ compl₂ m n := n.sign · compl' W₁ compl₂ m n.natAbs`.
These are the **same recurrence** (NagellLutz's `compl₂EDS` ≙ mathlib's `complEDS₂`,
and `W₁ = normEDS b c d`); both compute the witness of `W(m) ∣ W(n·m)`. The NagellLutz
version merely factors the recursion through an abstract two-sequence builder
`compl`/`compl'` (parametrised by arbitrary `W₁, compl₂ : ℤ → R`) before specialising
to `normEDS`. The index order is cosmetically swapped (`m,n` vs `k,n`).

Concluded: **found in mathlib as `map_complEDS`
(`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:544`, `@[simp]`),
essentially identical** — same root name, same statement up to the bound-variable
rename (`m`↔`k`) and the inert `RingHomClass`-vs-`→+*` morphism packaging. The
NagellLutz file is a literal fork:
`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequenceOriginal.lean` keeps
mathlib's verbatim `complEDS`/`map_complEDS`, and the working
`EllipticDivisibilitySequence.lean` is its in-progress refactor onto the abstract
`compl` track with a `RingHomClass` morphism. The file also has a *second*, mathlib-
aligned `complEDS` track (`section ComplEDS`, lines 1524–1644) whose map lemma is
`map_complEDS_root` (line 1668) — `_root` disambiguating from the `compl`-track
`complEDS` — itself another duplicate of mathlib's lemma.

---

### Call sites — `map_complEDS` (Phase 6.0)

Internal uses within NagellLutz (excluding the declaring lines 1156–1160): **3**.
External-to-file callers: 0 distinct files (all uses inside
`EllipticDivisibilitySequence.lean`). HasseWeil and the rest of NagellLutz reference
the *mathlib* `map_complEDS` (via `import`), not this fork's copy.

| Caller file:line | Usage (one-line excerpt) |
|------------------|--------------------------|
| `…/EllipticDivisibilitySequence.lean:1199` | `simp_rw [map_complEDS, aeval_X]` (in `complEDS_eq_aeval`) |
| `…/EllipticDivisibilitySequence.lean:1343`* | `… map_normEDS, map_complEDS, aeval_X …` (in the Divisibility/Complement block) |
| `…/EllipticDivisibilitySequence.lean:1424`* | `simp [redInvarDenom, apply_ite f, map_normEDS, map_complEDS]` |

*(line numbers approximate, within the second `Complement` block lines 1284–1433.)*

Inline-derivation grep (was the equivalent re-derived without using `map_complEDS`?):
none — every site that pushes a ring hom through `complEDS` uses this lemma. Textbook
`map_*` glue role. **Call-site signal: K = 3 internal uses, no inline re-derivation →
a genuine API lemma — but one that already exists upstream**, and whose 3 uses mathlib's
identical `@[simp]` lemma already serves for every downstream consumer in the repo.

---

### Composition check (Phase 6)

Can `map_complEDS` be derived from mathlib in ≤3 chained calls? **Trivially — it IS a
mathlib lemma.**

Attempt 1: `map_complEDS f b c d m n` (mathlib, bundled-`f`).
  - Mathlib decl used: `map_complEDS` (`…/EllipticDivisibilitySequence.lean:544`).
  - Result: succeeds, modulo the `RingHomClass`→`RingHom` packaging (apply to the
    bundled coercion `(f : R →+* S)`) and, because the fork gives `complEDS` a different
    underlying definition (`compl`-based), a `congr`/`simp` to reconcile the two
    `complEDS`. With mathlib's `complEDS` the project lemma *is* mathlib's lemma by name.
  - Caveat: the only obstruction to a literal `rfl` is self-inflicted by the fork's
    redefinition; aligning the definition removes it.

Conclusion: **mathlib HAS IT** (Phase 5), which dominates — composition is moot.

---

## Verdict: `map_complEDS`

**Category:** **NO-mathlib-has-it**

**Evidence:**
- Literature (Phase 3): the lemma is the *functoriality of the EDS complement sequence*
  — folklore base change, no named theorem; the top WebSearch hit is mathlib's own EDS
  doc page, confirming mathlib is the canonical home.
- Generality (Phase 4): MAXIMALLY GENERAL; the only delta vs. mathlib is a cosmetic,
  family-wide `RingHomClass`-vs-`→+*` packaging that is mathematically inert.
- **Mathlib search (Phase 5): found in mathlib as `map_complEDS` (root namespace),
  `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:544`, `@[simp]`-tagged,
  grep-confirmed**, equivalent statement.
- Composition (Phase 6): mathlib's lemma *is* the result; the project lemma follows in
  ≤1 step.

**Rationale:**

The clearest possible NO-mathlib-has-it. Mathlib's
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` already contains
`@[simp] lemma map_complEDS (k n : ℤ) : f (complEDS b c d k n) = complEDS (f b) (f c)
(f d) k n` at line 544 — the **same root-namespace name** and the same statement as the
NagellLutz line-1156 lemma, differing only by the bound-variable name (`k` vs `m`) and
by stating the morphism as a bundled `R →+* S` rather than un-bundled `RingHomClass`.
The NagellLutz file is a **fork** of that very mathlib source (identical copyright
header, "Authors: David Kurniadi Angdinata"); it even keeps mathlib's verbatim
`complEDS`/`map_complEDS` in `EllipticDivisibilitySequenceOriginal.lean` and a second
mathlib-aligned copy (`map_complEDS_root`, line 1668). The working file's line-1156
lemma is an in-progress *refactor* that re-expresses `complEDS` via a generalised
`compl`/`compl'` construction and re-proves the `map_*` family against it. The
mathematical content — "base change commutes with the complement sequence" — is
identical and already upstream.

The `RingHomClass`-vs-`RingHom` axis does not rescue a YES verdict: it is a one-line
consequence of mathlib's lemma, and mathlib intentionally states the *entire* EDS
`map_*` family with bundled `→+*` for uniformity, so a lone `RingHomClass` restatement
of `complEDS` would be inconsistent and rejected.

**(Ledger correction.)** A prior pass recorded the bucket as `YES-but-generalise-first`
in `mathlibable_ledger.tsv` (line 129); that is inconsistent with the prior report's own
body (which concluded NO-mathlib-has-it) and with the evidence. The correct bucket is
**NO-mathlib-has-it**; the ledger row should be updated.

WHY not (refactor-actionable):
  Mathlib already has it. Cite `map_complEDS` at
  `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:544` (`@[simp]`, bundled
  `(f : R →+* S)`, root namespace). The NagellLutz form follows directly once `complEDS`
  is the mathlib definition; the only residual work is that this fork gave `complEDS` a
  different underlying definition (`compl`-based), so the redundancy is with the whole
  forked `complEDS`/`compl` track, not just this one lemma.

Existing mathlib decl: `map_complEDS`
Located at:            `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:544`
Our form follows in ≤1 line (with mathlib's `complEDS`):
```lean
example (f : R →+* S) (b c d : R) (m n : ℤ) :
    f (complEDS b c d m n) = complEDS (f b) (f c) (f d) m n :=
  map_complEDS f b c d m n   -- the mathlib lemma, verbatim
-- For the file's `RingHomClass` `f`, apply it to the bundled coercion:
--   map_complEDS (f : R →+* S) b c d m n
```
Call sites in our project (Phase 6.0): K = 3 (lines ~1199, ~1343, ~1424), all internal
to the declaring file; 0 external (downstream uses the mathlib lemma).

Refactor plan:
  1. This lemma is part of a **whole forked track** (`EllipticDivisibilitySequence.lean`
     re-deriving the mathlib EDS file). The unit of action is the fork, not this single
     lemma: decide whether the NagellLutz `compl`/`compl'`-based generalisation of
     `complEDS` is intended to *replace* mathlib's `complEDS'`-based one upstream.
       - If **no** (the project should use mathlib's EDS API): delete the duplicated
         `complEDS`/`compl`/`map_complEDS` block, `import
         Mathlib.NumberTheory.EllipticDivisibilitySequence`, and let the 3 call sites
         resolve to mathlib's `@[simp] map_complEDS` (they already use it by the same
         name, so the `simp_rw [map_complEDS, …]` calls work unchanged once the import
         provides the lemma).
       - If **yes** (the generalised `compl` device is a deliberate upstreaming target —
         it abstracts the complement construction to arbitrary `W₁, compl₂`): then the
         *general* `EllSequence.compl` / `EllSequence.compl'` / `EllSequence.map_compl`
         lemmas (lines 1085, 1099, 1152) are the candidate contributions, assessed
         separately — but `map_complEDS` *itself* (the `normEDS` specialisation) stays
         redundant with mathlib and should be derived as the one-liner above, not
         re-proved.
  2. Either way, do **not** ship `map_complEDS` to mathlib: the name and statement
     already exist there.

---

## Next step

Delete `map_complEDS` from the NagellLutz fork (it duplicates mathlib's
`@[simp] map_complEDS` at `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:544`);
point the 3 internal call sites at the mathlib lemma. Update the ledger row from
`YES-but-generalise-first` to `NO-mathlib-has-it`. If upstreaming the abstract complement
construction is intended, run `/mathlibable` on `EllSequence.compl` /
`EllSequence.map_compl` (the genuinely-new abstractions) rather than on this
specialisation.
