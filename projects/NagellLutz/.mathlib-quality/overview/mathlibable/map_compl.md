# /mathlibable report — `EllSequence.map_compl`

> One-declaration mathlibable assessment, run under `/overview` Step 9 on the
> NagellLutz project (Nagell–Lutz; elliptic curves; division polynomials; EDS).
> Run manually (local build stale per task note; ChatGPT MCP down — WebSearch +
> direct read of the pinned mathlib EDS source used as the fallbacks).
>
> **Headline: this is the ℤ-indexed naturality lemma for the project's *abstract*
> complement sequence `EllSequence.compl` (parametrised over two arbitrary input
> sequences `W₁, compl₂`). Mathlib has only the `normEDS`-hardwired specialisation
> `map_complEDS`; the object `EllSequence.compl` is NOT in mathlib, so the general
> statement cannot even be phrased there. Verdict: YES-but-generalise-first —
> consistent with the sibling `map_compl'` (ℕ version) and `compl'` verdicts, and
> deliberately *correcting* the prior 2026-06-18 `map_compl.md` (which read
> NO-mathlib-has-it and was inconsistent with its own ℕ sibling).**

---

### Baseline (Phase 0)

- lake build:               not run (env build stale — task-permitted; reasoned from source).
- decl `EllSequence.map_compl`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1152` (the
  `lemma` line; the prompt's line 1153 is the statement body).
- qualified name **VERIFIED**: `EllSequence.map_compl`. The lemma re-states its
  namespace explicitly (`lemma EllSequence.map_compl …`) and sits in `section Map`
  (opened line 1116); the enclosing `namespace EllSequence` (opened line 1079) was
  closed at line 1112, so the explicit `EllSequence.` prefix is what fixes the
  fully-qualified name. Parsed prompt guess `EllSequence.map_compl` confirmed.
- kind:                     lemma (no `@[simp]` in the fork; its mathlib siblings
                            in the `map_*` family are `@[simp]`).
- has sorry:                no.
- module docstring summary: "Elliptic divisibility sequences" — defines EDSs and
  builds normalised EDSs from initial terms. The file is an **extended fork** of
  `Mathlib.NumberTheory.EllipticDivisibilitySequence` (same copyright header,
  "Authors: David Kurniadi Angdinata"; same Ward reference), adding the
  `addMulSub`/`net`/`rel₄`/`invarNum`/`universalNormEDS` apparatus *and* the
  generic `EllSequence.compl` layer, all in service of Nagell–Lutz.

---

### Statement (Phase 1)

```lean
-- file header (lines 85–86):
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (W : ℤ → R)
variable {F} [FunLike F R S] [RingHomClass F R S] (f : F)

-- the generic complement construction (lines 1085, 1099):
def compl' (W₁ compl₂ : ℤ → R) (m : ℤ) : ℕ → R    -- division-free quartic strong recursion
  | 0 => 0 | 1 => 1 | (n + 2) => …
def compl  (W₁ compl₂ : ℤ → R) (m : ℤ) (n : ℤ) : R := n.sign * compl' W₁ compl₂ m n.natAbs

-- the lemma under assessment (lines 1152–1154):
lemma EllSequence.map_compl (W₁ compl₂ : ℤ → R) (m n : ℤ) :
    f (compl W₁ compl₂ m n) = compl (f ∘ W₁) (f ∘ compl₂) m n := by
  simp [compl, map_compl']
```

`EllSequence.map_compl` is the **naturality / base-change** lemma for the
integer-indexed complement sequence `compl W₁ compl₂ m`: pushing a ring hom `f`
through the construction is the same as building it from the pushed-forward input
sequences `f ∘ W₁`, `f ∘ compl₂`. It is the ℤ-extension of the ℕ-indexed
`EllSequence.map_compl'` (line 1140), which carries the actual strong-induction
content; the ℤ version is two lines (`simp [compl, map_compl']`), handling only the
`Int.sign`/`natAbs` wrapper.

Semantics of `compl`: for the intended inputs `W₁ ≈ W(·)/W(1)` and
`compl₂ ≈ W(2·)/W(·)`, `compl W₁ compl₂ m n` represents `W(n·m)/W(m)` for an
**arbitrary** elliptic sequence `W` — computed in a division-free way (no ring
division required). This is exactly the abstraction that lets the project prove the
divisibility witness for *arbitrary* elliptic sequences (Phase 6.0).

Variables / typeclasses:
- `[CommRing R] [CommRing S]` — source/target commutative rings.
- `{F} [FunLike F R S] [RingHomClass F R S] (f : F)` — the morphism, in **un-bundled
  `RingHomClass`** form (file header) rather than mathlib's bundled `R →+* S`.
- `(W₁ compl₂ : ℤ → R)` — the **two arbitrary input sequences** (the generalisation).
- `(m n : ℤ)` — the two integer indices.

Hypotheses: none beyond the typeclasses (in particular **no `IsEllSequence`
hypothesis** — `map_compl` is pure plumbing about the recursion shape and holds for
*any* `W₁, compl₂`).

---

### Size classification (Phase 2a)

Verdict: **SMALL** (structurally load-bearing).
Reason: a `map_*` naturality glue lemma in the standard EDS family; not a named
theorem, not a `## Main results` entry. But it is a satellite of a ~70-line
*definitional generalisation* (`compl'`/`compl`) of an existing mathlib API, so the
literature width was still run EXHAUSTIVE per protocol (the def it generalises is
the subject of current research — see Phase 3).

### One-line check (Phase 2b)

n/a — kind is `lemma`, not `def`/`abbrev`/`structure`. (For the record the proof
body is the single tactic line `simp [compl, map_compl']`.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                           | Query                                                                                                   | Hit? | Standard form found | Notes |
|----|-----------------------------------|---------------------------------------------------------------------------------------------------------|------|---------------------|-------|
| 1  | WebSearch (specific form)         | "elliptic divisibility sequence complement sequence W(nm)/W(m) division-free recurrence ring homomorphism functoriality" | partial | EDS / complement-sequence concept confirmed; **top hit is mathlib's own EDS doc page** | Wikipedia + Ward + Warwick CM-EDS notes + arXiv (0710.1316, 1108.3051, math/0402415) all on EDS/division polys; none name a "complement-sequence functoriality" lemma — it is folklore plumbing |
| 2  | WebSearch (generic-ring framing)  | "\"elliptic sequences\" over commutative rings arbitrary sequence divisibility witness arXiv"            | **HIT** | **arXiv:2604.05280, "On Elliptic Sequences over Commutative Rings", J. Xu** — elliptic sequences over an arbitrary commutative ring; classification; standard EDSs are elliptic by purely-algebraic implications among the quartic relations | This is the mathematical backing for the project's `EllSequence.compl` abstraction (Xu is a mathlib contributor; plausibly the author behind this formalisation). The *abstract* (arbitrary-sequence) angle is genuinely a research object, not just Lean sugar |
| 3  | WebSearch (named-after / aliases) | (covered by #1/#2 — "complement sequence" carries no person/place name; Ward originates EDS theory)      | n/a  | concept is Ward's EDS theory; the division-free *complement-witness* packaging `W(m)·Wᶜ = W(nm)` is a mathlib-internal device | the abstraction "over two arbitrary input sequences" is the Xu generic-ring viewpoint |
| 4  | ChatGPT MCP                       | (server down for this run — fallback to WebSearch ×3 + the arXiv hit + direct mathlib-source read)       | n/a  | — | per task note "ChatGPT MCP may be down (use fallbacks)" |
| 5  | Local references                  | `ls projects/NagellLutz/.mathlib-quality/references/`                                                    | n/a  | (directory absent)  | no per-project reference PDFs; file's own `## References` cites *Ward, Memoir on EDS* |
| 6  | nLab                              | "elliptic divisibility sequence" / "division polynomial" / "complement sequence"                        | no   | nLab has no EDS / division-polynomial / complement-sequence page | not a category-theoretic concept; recorded no-hit |
| 7  | nCatLab (categorical)             | —                                                                                                       | n/a  | — | `map_compl` is a base-change identity, not a categorical universal property |
| 8  | Stacks Project (alg geom)         | "division polynomial" / "elliptic divisibility sequence"                                                | n/a  | Stacks has no EDS / division-polynomial tag | outside Stacks' scope |
| 9  | MathOverflow / MSE                | covered transitively by WebSearch #1/#2 — no thread names a "complement-sequence naturality" lemma       | no   | — | the naturality is folklore-trivial; nobody writes it as a result |
| 10 | recent arXiv (last 5 years)       | EDS recurrence / elliptic sequences over rings (2102.07573, 2604.05280)                                  | **partial→HIT** | generic-ring elliptic sequences (2604.05280) is the relevant modern setting; base change is background there | confirms the general-ring viewpoint motivating the abstraction |

**Protocol pass check:** WebSearch ran 3 distinct queries at different generality
levels (specific complement form; generic-ring framing; named-after/aliases).
ChatGPT MCP recorded n/a-down with documented fallbacks. Local refs checked
(absent). nLab, Stacks, nCatLab, MathOverflow, arXiv each checked with a one-line
reason. No channel skipped without a reason.

### Literature summary (Phase 3)

Concept identified as: the **complement sequence** `Wᶜ(m, n) = W(n·m)/W(m)` of an
elliptic sequence — the division-free witness of `W(m) ∣ W(n·m)` — together with
its **naturality** under a ring homomorphism. `map_compl` is that naturality, for
the construction taken over **two arbitrary input sequences** `W₁, compl₂` rather
than the canonical `normEDS`.

Sources agree on the standard form: **partly.** EDS theory (Ward; Wikipedia;
Warwick notes) is well established and treats the complement / divisibility
*concretely*, via division polynomials and the normalised EDS. The "naturality
commutes with base change" fact is folklore (every recurrence built from `+, ·, ^,
1, ite` commutes with a ring map). The **generic-ring / arbitrary-sequence**
viewpoint that the project's `EllSequence.compl` formalises *is* a recognised
research object — **arXiv:2604.05280, "On Elliptic Sequences over Commutative
Rings" (J. Xu)** — but the specific *complement-witness* sequence and its `map_*`
packaging remain a mathlib-internal device, not classical notation.

Most general standard form: the construction (and hence its naturality) makes sense
for any pair of input sequences over any `CommRing` and any ring map between them —
which is exactly the Lean form here. There is no *more*-general literature form to
move to; the fork already sits at the maximally-general level (arbitrary `W₁,
compl₂`, arbitrary `CommRing`s, `RingHomClass` morphism).

Generality dimensions where the literature varies:
  - base-ring generality: classical sources use ℤ or a field; mathlib + Xu use an
    arbitrary `CommRing` — the form here.
  - input data: classical/mathlib fix the canonical `normEDS`; the project
    abstracts to two arbitrary sequences — *strictly more general* (this is the
    contribution).
  - morphism packaging: bundled `R →+* S` (mathlib) vs un-bundled `RingHomClass`
    (here) — a Lean-side cosmetic axis only (Phase 4).

Disagreement with the literature: none. The lemma is the natural, correct
naturality statement.

---

### Generality analysis — `EllSequence.map_compl`

Literature/mathlib-standard form (Phase 3): naturality of the complement sequence
under a ring map. Mathlib's instance fixes the inputs to `normEDS`/`complEDS₂`
(`map_complEDS`); the project's `map_compl` keeps them as free parameters.

| # | Parameter / hypothesis            | Current Lean form (NagellLutz)                 | Mathlib's nearest form (`map_complEDS`)     | More general here? | Reason |
|---|-----------------------------------|------------------------------------------------|----------------------------------------------|--------------------|--------|
| 1 | rings `R`, `S`                    | `[CommRing R] [CommRing S]`                    | same                                         | no (already max)   | `compl`/`Int.sign` scalar need ring ops; maximal |
| 2 | input sequences                   | **arbitrary** `W₁ compl₂ : ℤ → R`              | **hardwired** `normEDS b c d`, `complEDS₂ b c d` | **YES — strictly more general** | the whole point: `complEDS b c d m = compl (normEDS b c d) (compl₂EDS b c d) m` (line 1110) recovers mathlib's case |
| 3 | the morphism `f`                  | `[FunLike F R S] [RingHomClass F R S] (f : F)` | bundled `(f : R →+* S)`                       | marginally (cosmetic) | un-bundled is a hair more general but mathematically inert (Phase 4b note) |
| 4 | indices `m, n`                    | `(m n : ℤ)`                                    | `(k n : ℤ)` (bound-var rename only)          | no                 | both indices intrinsically ℤ (`Int.sign`, `natAbs`) |

### Generality verdict (Phase 4b)

The current form is **MAXIMALLY GENERAL** and is *strictly more general than
mathlib's `map_complEDS`* along axis 2 (arbitrary input sequences vs. hardwired
`normEDS`). Weakening opportunities on the project's own statement: **0** — there is
nothing left to weaken; the contribution is precisely that this *is* the weakened
(parametrised) form of mathlib's lemma.

The `RingHomClass`-vs-`R →+*` axis (3) is a generalisation, not a weakening, and is
mathematically inert: mathlib's bundled form is recovered by `f := (g : R →+* S)`,
and conversely the `RingHomClass` form follows from a bundled lemma applied to the
coercion `(f : R →+* S)`. It does **not** by itself drive the verdict, and mathlib
deliberately states the *entire* EDS `map_*` family with bundled `→+*` for
uniformity — so any restatement should match that convention, not splinter it.

Proposed restatement: **generalise mathlib's own `complEDS`/`map_complEDS` family**
to take the two input sequences as parameters (i.e. upstream `EllSequence.compl` /
`map_compl` as the generic API), then recover `complEDS`/`map_complEDS` as the
`normEDS`/`complEDS₂` specialisation (one-line corollaries). Cost: moderate (touches
the whole `complEDS'`/`complEDS`/`map_complEDS'`/`map_complEDS` block in
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`), but the project has
already done the work — the generalisation is exactly what this fork performs.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Note |
|----|--------------------------------------------------------------------------|----------|------|
| 1  | "let X be a foo" preamble → typeclass?                                    | no       | already typeclass-based (`CommRing`, `RingHomClass`) |
| 2  | sequences/metric → filters/topological?                                  | no       | purely algebraic identity |
| 3  | construction → universal property class?                                 | no       | this is a `map`-lemma, not a construction (the *def* `compl` is the construction) |
| 4  | set-with-closure-predicate → bundled substructure?                       | no       | not a substructure statement |
| 5  | field/VS-specific → module/(semi)ring weakening?                          | no       | already over arbitrary `CommRing` |
| 6  | 1-categorical → higher-categorical?                                       | no       | a single base-change equation |
| 7  | concrete index (ℕ/ℤ) → arbitrary additive group?                          | no       | indices intrinsically ℤ (`Int.sign`, `natAbs`) |

Modern-idiom verdict: **no** stronger idiom. This already *is* mathlib's `map_*`
idiom; the only move is the parameter-generalisation captured under Phase 4b.

---

### Diamond / defeq risk — Phase 4.5

n/a — declaration kind is `lemma` (introduces no definitional equalities or
typeclass-search paths). Skipped. (The defeq question lives with the *def*
`EllSequence.compl`, assessed separately in `compl.md`.)

---

### Mathlib search-status: `EllSequence.map_compl`

Searched for **both** the project's general form (`compl`, arbitrary `W₁ compl₂`,
`RingHomClass`) and mathlib's concrete form (`complEDS`, hardwired `normEDS`,
bundled `→+*`).

[A] Lean-Finder       "map complement EDS", "ring hom complement sequence"   concept hit → mathlib EDS doc page (concrete `map_complEDS`)
[B] Loogle (pattern)  `f (?C _ _ _ _) = ?C (⇑f ∘ _) (⇑f ∘ _) _`             **no** general hit (no `compl`-over-arbitrary-sequences in mathlib); the *concrete* pattern `f (complEDS …) = complEDS (f _) …` hits `map_complEDS`
[C] LeanSearch        "ring homomorphism commutes with complement sequence of an elliptic sequence"  concrete hit (`map_complEDS`); no parametrised version
[D] Grep mathlib src  `grep -nE "compl'|namespace EllSequence|W₁|f ∘ W" …/EllipticDivisibilitySequence.lean`  **NO general match** — mathlib has no `EllSequence.compl`/`compl'`/`map_compl`
[E] Grep mathlib src  `grep -n "map_complEDS" …/EllipticDivisibilitySequence.lean`  **HIT line 544** — the *concrete* specialisation only

**Decisive grep evidence** (mathlib `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`):

```
388: def complEDS' : ℕ → R           -- recursion with normEDS b c d / complEDS₂ b c d INLINED (no W₁, compl₂ params)
392:   | (n + 2) => let m := n/2+1; if Even n then complEDS' m * complEDS₂ b c d (m*k) else …
427: def complEDS (n : ℤ) : R := n.sign * complEDS' b c d k n.natAbs
507: variable {S : Type v} [CommRing S] (f : R →+* S)
533: @[simp] lemma map_complEDS' (k : ℤ) (n : ℕ) : f (complEDS' b c d k n) = complEDS' (f b) (f c) (f d) k n
543: @[simp] lemma map_complEDS  (k n : ℤ) : f (complEDS  b c d k n) = complEDS  (f b) (f c) (f d) k n := by simp [complEDS]
```

Concluded: mathlib has **only the `normEDS`-specialised** complement sequence and
its naturality (`map_complEDS`, line 544, `@[simp]`; `map_complEDS'`, line 534).
Mathlib's `complEDS'` **inlines** `normEDS b c d` / `complEDS₂ b c d` into the
recursion and has **no parametrisation** over arbitrary input sequences. Therefore
the object `EllSequence.compl` — and hence the *statement* of `EllSequence.map_compl`
— **does not exist in mathlib**. The project recovers mathlib's concrete lemma:
`complEDS b c d m := compl (normEDS b c d) (compl₂EDS b c d) m` (line 1110), and the
fork's own `map_complEDS` (line 1156) is *derived from* `EllSequence.map_compl`
(`simp only [complEDS, EllSequence.map_compl]; congr 1; ext …`).

So `EllSequence.map_compl` is the **naturality engine for a generalisation mathlib
does not have**, and mathlib's `map_complEDS` is its `normEDS`-instance.

---

### Call sites — `EllSequence.map_compl` (Phase 6.0)

Internal use count (within NagellLutz, excluding the declaring lines 1152–1154):

| Caller file:line                                                       | Usage pattern |
|------------------------------------------------------------------------|----------------|
| projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1157  | `simp only [complEDS, EllSequence.map_compl]` — used to **derive the concrete `map_complEDS`** (the fork's reproduction of mathlib's lemma) |

Indirect / motivating consumer: the abstract divisibility witness
`IsEllSequence.mul_compl_eq_apply_mul_of_mem_nonZeroDivisors` (line 1296),
`W m * compl W₁ compl₂ m n = W (n·m)` for an **arbitrary** elliptic sequence `W`
with `W m ∈ R⁰` — the result that *requires* the abstract `compl`, and from which
`normEDS_mul_complEDS` (line 1338, the mathlib-equivalent divisibility statement) is
recovered via `aeval` on the universal EDS (lines 1322–1344). This is the entire
reason the `compl`/`map_compl` abstraction layer exists.

Inline-derivation grep (re-derived elsewhere without `map_compl`?): none — every
push of a ring hom through `compl` routes through this lemma (directly, or through
`map_complEDS` which is built on it).

Call-site signal: K = 1 *direct* internal use, but it is **load-bearing for the
generalised divisibility theory** (not dead code). It is the abstract analogue of a
lemma mathlib already has only in specialised form — so the API need is real, and
the right home is a *generalisation* of mathlib's existing API.

---

### Composition check (Phase 6)

Can `map_compl` be derived from mathlib in ≤3 chained calls? **No — at the level
that matters.**

- The *proof* is the 2-line `simp [compl, map_compl']`. But that references
  `EllSequence.compl` and `EllSequence.map_compl'`, **neither of which is in
  mathlib** (Phase 5, grep [D]). You cannot even *state* `map_compl` from mathlib
  primitives without first porting `compl'`/`compl`/`map_compl'`.
- Mathlib's `map_complEDS` (line 544) gives only the `normEDS` *instance*; it does
  not, and cannot, yield the parametrised statement (the extra generality is real —
  axis 2 of Phase 4).
- So `map_compl` is **inseparable from the generic-`compl` API**; it is a satellite
  of a ~70-line definitional generalisation, not a standalone composable corollary.

Conclusion: not composable from mathlib (the object it is about is absent). Mathlib
does **not** have *this* (general) lemma — it has only the specialisation.

---

## Verdict: `EllSequence.map_compl`

**Category:** **YES-but-generalise-first**

**Evidence:**
- Literature (Phase 3): naturality of the complement sequence is folklore plumbing,
  but the **generic-ring / arbitrary-sequence** viewpoint the underlying
  `EllSequence.compl` formalises is a recognised research object
  (**arXiv:2604.05280, "On Elliptic Sequences over Commutative Rings", J. Xu**); the
  abstraction is mathematically justified, not gratuitous Lean sugar.
- Generality (Phase 4): **MAXIMALLY GENERAL and strictly more general than mathlib's
  `map_complEDS`** — arbitrary input sequences `W₁, compl₂` vs. hardwired `normEDS`;
  0 weakenings left on the project's own statement.
- Mathlib search (Phase 5): mathlib has **only the `normEDS`-specialisation**
  (`map_complEDS`, `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:544`,
  `@[simp]`; `map_complEDS'` line 534). The object `EllSequence.compl` and the
  general statement are **absent** (grep-confirmed).
- Composition (Phase 6): **fails** — cannot state/derive `map_compl` from mathlib
  without first porting the `compl` family; the extra generality is genuine.

**Rationale:**

Mathlib already proves the *naturality fact for the concrete `normEDS` complement
sequence* (`map_complEDS`). What it does **not** have is the **parametrised**
statement: mathlib's `complEDS'`/`complEDS` inline `normEDS b c d` and
`complEDS₂ b c d` into the recursion, with no abstraction over the two input
sequences. `EllSequence.map_compl` is naturality for the complement of an
**arbitrary** pair `W₁, compl₂` — strictly more general — and it is the engine for
the project's divisibility witness over *arbitrary* elliptic sequences
(`IsEllSequence.mul_compl_eq_apply_mul_of_mem_nonZeroDivisors`, line 1296), a result
mathlib lacks and which is precisely the generic-ring viewpoint of arXiv:2604.05280.
You cannot phrase `map_compl` in mathlib without first porting the `compl` family,
so it is neither NO-mathlib-has-it (mathlib lacks *this* general lemma) nor
NO-composable (its very statement needs an object mathlib doesn't have).

This is the **same situation, at index type ℤ, as the sibling `map_compl'` (ℕ),
which the house assessed YES-but-generalise-first**, and as the underlying `compl'`
def (also YES-but-generalise-first). `map_compl` is just `map_compl'` wrapped with
the `Int.sign`/`natAbs` extension; there is no principled reason for the two
naturality lemmas to land in different buckets. **This report therefore corrects the
prior 2026-06-18 `map_compl.md`, which read NO-mathlib-has-it** by weighting "the
naturality *fact* is covered by `map_complEDS`" — that conflates the concrete fact
with the strictly-more-general statement, and is inconsistent with its own ℕ
sibling. Under the protocol, when mathlib holds only a strict specialisation and the
general form (a) is genuinely more general, (b) is load-bearing for results mathlib
lacks, and (c) cannot be stated/composed from mathlib, the bucket is
**YES-but-generalise-first**.

**Why "generalise-first" (not YES-add-as-is):** adding a parallel
`EllSequence.compl`/`map_compl` next to mathlib's `complEDS`/`map_complEDS` would
**duplicate** the existing complement-sequence API. The correct contribution is to
**generalise mathlib's own `complEDS'`/`complEDS` (and the `map_complEDS'`/
`map_complEDS` family) to take the two input sequences as parameters**, prove
`map_compl`/`map_compl'` over the general recursion (these proofs), and recover the
present concrete `complEDS`/`map_complEDS` as one-line `normEDS`/`complEDS₂`
specialisations — exactly the refactor this fork already performs across the file
(`compl'`→`complEDS`, `map_compl'`/`map_compl`→`map_complEDS'`/`map_complEDS`). The
upstreamed `map_compl` would carry `@[simp]` like its mathlib siblings, and the
morphism should keep mathlib's bundled `R →+*` packaging for family uniformity (the
`RingHomClass` axis is inert and not the contribution).

**Why not BORDERLINE:** the action is unambiguous — generalise the existing mathlib
def + naturality family by abstracting the two input sequences; only a routine
naming/namespace nod is needed (likely keep mathlib's `complEDS` spelling for the
specialisation and introduce the generic `compl` with sequence arguments). The genuine
taste/policy call (does mathlib *want* a new public generic `compl` *name*?) sits with
the **def** `EllSequence.compl` (assessed BORDERLINE in `compl.md`); the *naturality
lemma* rides along with whatever that decision is and is itself a clean
generalise-first, mirroring `map_compl'`.

**Existing mathlib decl (the specialisation):** `EllSequence.map_complEDS`
(`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:544`, `@[simp]`, bundled
`(f : R →+* S)`), built on `complEDS'`/`map_complEDS'` (lines 392/534). The present
general lemma reduces to it via
`complEDS b c d m := compl (normEDS b c d) (compl₂EDS b c d) m` + `map_normEDS` +
`map_compl₂EDS` (the fork's own derivation at line 1156).

**Recommendation / next step:** upstream as the **generalisation of**
`Mathlib.NumberTheory.EllipticDivisibilitySequence.complEDS'`/`complEDS` and the
`map_complEDS'`/`map_complEDS` family — abstract the two input sequences into
explicit parameters (`compl'`/`compl`), prove `map_compl'` (strong induction) and
`map_compl` (its `Int.sign`/`natAbs` two-liner) over the general recursion, and
recover the concrete `complEDS`/`map_complEDS` as `normEDS`/`complEDS₂`
specialisations (one-line corollaries). Assess this *together with* `compl`/`compl'`/
`map_compl'` as one API-generalisation unit, not as four independent decls. Do **not**
add `EllSequence.map_compl` as a standalone parallel lemma (it would duplicate
mathlib's complement-sequence naturality API).
