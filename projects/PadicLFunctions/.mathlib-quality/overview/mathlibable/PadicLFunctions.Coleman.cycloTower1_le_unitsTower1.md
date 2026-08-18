# `/mathlibable` report — `PadicLFunctions.Coleman.cycloTower1_le_unitsTower1`

**Final verdict: `NO-composable-from-mathlib`**

---

### Baseline (Phase 0)

- lake build:               build not re-run; reasoned from source (per task build note — a fresh
  `CyclotomicUnits.olean` is present under `.lake/build/lib/lean/PadicLFunctions/Iwasawa/`; the file's
  only recent commits are the daily mathlib bump and a golf cleanup, no new math, so it is in a built
  state).
- decl `PadicLFunctions.Coleman.cycloTower1_le_unitsTower1`: resolved at
  `projects/PadicLFunctions/PadicLFunctions/Iwasawa/CyclotomicUnits.lean:239`
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  Cyclotomic units — the global modules `𝒟_n` and their local closures `𝒞`
  (RJW arXiv:2309.15692 §11.3); culminates in the milestone that the Coleman-map inputs `c_n(a)`
  live in `𝒞_{∞,1} ≤ 𝒰_{∞,1}`.

The full text:

```lean
lemma cycloTower1_le_unitsTower1 : cycloTower1 p ≤ unitsTower1 p :=
  fun _ hu n hn => (Subgroup.mem_inf.1 (hu n hn)).2
```

---

### Statement (Phase 1)

`cycloTower1_le_unitsTower1` is a theorem stating the following:

The inverse-limit tower of cyclotomic-unit local closures `𝒞_{∞,1}` is contained in the inverse-limit
tower of principal local units `𝒰_{∞,1}`, both regarded as subgroups of the norm-compatible system
group `𝒰_∞ = NormCompatUnits p`. In symbols: `𝒞_{∞,1} ≤ 𝒰_{∞,1}` (RJW arXiv:2309.15692, TeX 3092 /
the milestone line TeX 3084).

Mathematically this is the trivial "image" half of the milestone: at every level `n ≥ 1` the closure
`𝒞_{n,1}` is *defined* as `𝒞_n ∩ 𝒰_{n,1}` (an intersection that explicitly carries `𝒰_{n,1}` as one
of its two factors), so its second projection lands in `𝒰_{n,1}`; reading this off at every level `n`
gives the tower inclusion. The genuine mathematical content — that the cyclotomic units actually *are*
principal units (`‖c_n(a) − 1‖ < 1`) — lives in the *sibling* results
`norm_cycloUnit_sub_one_lt_one` / `cyclo_mem_cycloTower1`, **not** here. This lemma is pure
order-theoretic bookkeeping on top of those.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the fixed prime (section variables).

Hypotheses (Lean side):
- none beyond the section variables (the membership hypothesis `hu` is the `≤`-unfolded argument).

Conclusion (math): `𝒞_{∞,1} ⊆ 𝒰_{∞,1}` inside `𝒰_∞`.

Conclusion (Lean): `cycloTower1 p ≤ unitsTower1 p`, i.e.
`∀ u, (∀ n, 1 ≤ n → u.elems n ∈ cycloClosureOne p n) → (∀ n, 1 ≤ n → u.elems n ∈ localUnitsOne p n)`.

Key definitional facts (all project-local; see `Iwasawa/CyclotomicUnits.lean` and `Iwasawa/LocalUnits.lean`):
- `cycloTower1 p`  := `{u | ∀ n, 1 ≤ n → u.elems n ∈ cycloClosureOne p n}`           (CyclotomicUnits.lean:226)
- `unitsTower1 p`  := `{u | ∀ n, 1 ≤ n → u.elems n ∈ localUnitsOne  p n}`            (LocalUnits.lean:479)
- `cycloClosureOne p n` := `cycloClosure p n ⊓ localUnitsOne p n`                    (CyclotomicUnits.lean:218–219)

So at each level the membership target is literally an `⊓` whose **second** factor is `localUnitsOne p n`
— and the proof is exactly "take `.2` of `Subgroup.mem_inf` at each level".

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A one-line glue lemma — the trivial inclusion half of a milestone, threading the elementary
lattice fact `a ⊓ b ≤ b` through a pointwise inverse-limit definition. Not a named theorem, not a new
structure, not itself a `## Main results` entry (it is *infrastructure for* the milestone
`cyclo_mem_unitsTower1`, which is the headline). It is a sibling of `unitsTower1Plus_le_unitsTower1`
(LocalUnits.lean:492), `cycloUnits_le_globalUnits` (`:= inf_le_right`, CyclotomicUnits.lean:201),
`globalUnits_le_localUnits`, `cycloTower1Plus_le_cycloTower1`, `cycloTower1Plus_le_unitsTower1Plus`,
`unitsTower1Plus_le_unitsTower1` — an entire family of project-internal tower-inclusion plumbing lemmas.

(Note: literature width was run EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Body line count: 1 substantive line (`fun _ hu n hn => (Subgroup.mem_inf.1 (hu n hn)).2`)
One-liner verdict: **n/a — kind is `lemma`, not `def`** (the defeq/diamond/API exemption table is for
`def`/`abbrev`/`structure`; a lemma introduces no definitional equality or typeclass-search path).
Noted only: the *proof term* is one line, which is itself a strong signal that the statement is a thin
composition (carried into Phase 6/7).

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

The lemma has two separable "concepts": (i) the **number-theoretic content** — cyclotomic units sitting
inside the principal local units in the cyclotomic tower (classical Iwasawa theory; the RJW paper is the
immediate source); and (ii) the **structural mechanism** actually being proved — the meet/greatest-lower-
bound fact `a ⊓ b ≤ b` lifted through an inverse-limit-of-subgroups. Both were searched.

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "cyclotomic units contained in principal local units inverse limit Iwasawa theory"                     | yes  | `C_∞ ⊆ U_∞`; cyclotomic/circular units sit inside (principal) local units, studied via the projective limit with respect to norm maps | Hida lecture notes, Encyclopedia of Mathematics, nLab "Iwasawa theory", Kurihara/Coleman literature; this is textbook Iwasawa theory (Washington Ch. 7–8, Lang *Cyclotomic Fields*) |
|  2 | WebSearch (general / structural) | "meet semilattice infimum less than or equal to second factor a ⊓ b ≤ b lattice theory"                | yes  | `a ⊓ b ≤ a` and `a ⊓ b ≤ b` — the meet is the greatest *lower* bound, hence below both factors | Wikipedia "Join and meet"; J.B. Nation *Notes on Lattice Theory*; this is the defining property of a meet-semilattice — fully standard |
|  3 | WebSearch (named-after / aliases)| "inverse limit subgroups monotone inclusion towers projective limit order preserving"                  | yes  | intersections of subgroups form an inverse system; level-wise inclusions are order-preserving and pass to the projective limit | Osserman *Inverse limits and profinite groups*; W&M *Direct/Inverse limits and profinite groups*; Wikipedia "Inverse limit"; standard category/group theory |
|  4 | ChatGPT MCP                      | (intended: "standard form + generality + historical evolution of 'cyclotomic units ⊆ principal local units' and of 'meet ≤ factor in a subgroup lattice'") | n/a  | —                                | ChatGPT MCP server not configured in this environment (ToolSearch returns no such tool). Recorded n/a; compensated by extra WebSearch breadth (rows 1–3) + nLab (row 6) + direct mathlib source reading (Phase 5). |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/`                | n/a  | (no references dir)              | Neither `.mathlib-quality/references/` nor a gitignored `refs/` store exists for this project; the RJW arXiv:2309.15692 PDF is not available locally. Recorded n/a. |
|  6 | nLab                             | meet semilattice / greatest lower bound / subgroup lattice / Iwasawa theory                            | yes  | nLab "lattice": meet = greatest lower bound, below both factors; nLab "Iwasawa theory": the norm-compatible inverse limit of unit groups is the central object | nLab "lattice", nLab "Iwasawa theory" both confirm; nothing categorical-novel is being asserted by this lemma |
|  7 | nCatLab (if categorical)         | (covered by nLab row 6)                                                                                 | n/a  | not a higher-categorical concept | The lemma is a 1-categorical/order-theoretic inclusion; no ∞-categorical content. |
|  8 | Stacks Project (if alg geom)     | —                                                                                                      | n/a  | not an algebraic-geometry concept | This is `p`-adic / Iwasawa number theory + lattice theory; Stacks has no bearing. |
|  9 | MathOverflow / Math.StackExchange| "a ⊓ b ≤ b semilattice" / "cyclotomic units principal units inverse limit"                             | yes  | confirms `a∧b ≤ b` is the elementary meet property; confirms the NT inclusion is standard background, never stated as a quotable named lemma | The structural fact is "too trivial to have a name"; the NT inclusion is ambient background in every Iwasawa-theory text |
| 10 | recent arXiv (last 5 years)      | RJW arXiv:2309.15692 (the project's own source) + arXiv:2310.03543, math/0512015                       | yes  | RJW §11.3 (TeX 3060–3112): defines `𝒞_{∞,1}` as the inverse limit of `𝒞_{n,1} = 𝒞_n ∩ 𝒰_{n,1}`; the inclusion `𝒞_{∞,1} ⊆ 𝒰_{∞,1}` is immediate from the definition and used without comment | The source treats this inclusion as definitional bookkeeping, exactly as the Lean lemma does |

The protocol passes: WebSearch ran 3 distinct queries at different generality levels (specific NT form,
the most-general structural `a⊓b≤b` form, and the inverse-limit/aliases form); ChatGPT MCP is recorded
n/a with reason (not installed); local references recorded n/a with reason; nLab checked; nCatLab /
Stacks / MathOverflow / arXiv each checked or n/a-with-reason.

### Literature summary (Phase 3)

Concept identified as: a project-specific packaging of two standard ingredients — (NT) "the cyclotomic
units lie in the principal local units of the cyclotomic tower" (classical Iwasawa theory; RJW
arXiv:2309.15692 §11.3 is the immediate source) and (structure) "the meet `a ⊓ b` lies below its second
factor `b`, applied level-by-level in an inverse limit of subgroups".

Sources agree on the standard form: yes. The NT inclusion is ambient background in Washington / Lang /
Hida / RJW. The structural fact `a ⊓ b ≤ b` is the defining property of a meet-semilattice (Wikipedia,
Nation, nLab) and in mathlib is exactly `inf_le_right`.

Most general standard form: the *structural* skeleton is `inf_le_right : a ⊓ b ≤ b` in any
`SemilatticeInf`. Everything else here (`NormCompatUnits`, `cycloTower1`, `unitsTower1`,
`cycloClosureOne`, `localUnitsOne`) is bespoke RJW-tower scaffolding with no literature-standard or
mathlib counterpart.

Generality dimensions where the literature varies:
  - The NT objects (`𝒞`, `𝒰` towers) — RJW realises them concretely inside `ℂ_p`; other treatments use
    abstract local fields. Either way they are not mathlib objects.
  - The structural fact — already maximally general in mathlib as `inf_le_right` over `SemilatticeInf`.

Disagreement with the literature: none. The Lean statement matches the (definitional) inclusion the
source states, and the proof matches the elementary lattice fact the literature gives for it.

---

### Generality analysis — `cycloTower1_le_unitsTower1` (Phase 4)

Literature-standard form (from Phase 3): structurally `inf_le_right : a ⊓ b ≤ b` over any
`SemilatticeInf`; semantically the RJW definitional inclusion `𝒞_{∞,1} ⊆ 𝒰_{∞,1}`.

| # | Parameter / hypothesis            | Current Lean form                         | Literature-standard form                 | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|-------------------------------------------|------------------------------------------|---------------------|----------------------------------|
| 1 | `cycloTower1 p` (LHS subgroup)    | bespoke inverse-limit subgroup of `NormCompatUnits p` | no mathlib/literature-standard analogue (project object) | NO | It is glued out of project-only defs (`cycloClosureOne`, `cycloClosure`, `localUnitsOne`, …) that exist nowhere in mathlib; the statement is intrinsically about these objects. |
| 2 | `unitsTower1 p` (RHS subgroup)    | bespoke inverse-limit subgroup of `NormCompatUnits p` | no analogue (project object)             | NO | Same — `unitsTower1` / `localUnitsOne` / `NormCompatUnits` are RJW-specific. |
| 3 | the underlying lattice step       | `(Subgroup.mem_inf.1 (hu n hn)).2`        | `inf_le_right` over `SemilatticeInf`     | (already maximal)   | The abstract kernel is already the most general possible meet projection; mathlib's `inf_le_right` *is* the general form. No further generalisation of the *fact* is meaningful. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (for the objects it is about). There are zero weakening
opportunities: the lemma is a statement *about* two specific project subgroups, and the only abstract
content (`a ⊓ b ≤ b`) is already at mathlib's maximal generality (`inf_le_right`). Nothing can be
weakened without either (a) being a statement about different (non-existent-in-mathlib) objects, or (b)
collapsing to `inf_le_right`, which already exists.

Number of weakening opportunities found: 0
Proposed restatement: none (MAXIMALLY GENERAL).
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                  | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|---------------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                      | no       | —                      | The hypotheses are already just the `p`/`Fact p.Prime` section vars; nothing to typeclass-ify. |
|  2 | sequences/metric → filters/topological?                                                                  | no       | —                      | The tower is indexed over `ℕ` with an `n ≥ 1` predicate; this is the inverse-system index, not a metric limit. Already the right idiom. |
|  3 | construct an object → universal-property class?                                                          | no       | —                      | This is an inclusion lemma, not a construction. |
|  4 | set-with-closure-predicate → bundled substructure?                                                       | no       | —                      | Both sides are already bundled `Subgroup`s; the proof already uses `Subgroup.mem_inf`. Idiomatic. |
|  5 | vector-space/metric/field-specific → weaker typeclass?                                                   | no       | —                      | No algebraic-structure hypothesis to weaken; the abstract core already lives over `SemilatticeInf`. |
|  6 | 1-categorical → higher-categorical?                                                                      | no       | —                      | Order-theoretic inclusion; no categorification target. |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive/ordered structure?                                          | no       | —                      | The `ℕ`-index is the inverse-system's directed index; abstracting it would mean re-engineering `NormCompatUnits`, which is the project's chosen model, not a mathlib idiom gap. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**.
One-line reason: the lemma is already stated idiomatically (bundled `Subgroup`s, `Subgroup.mem_inf`,
section typeclasses); its only generalisable kernel is already mathlib's `inf_le_right`. There is no
Bourbaki-2.0 reformulation to make — the objects themselves are project-bespoke and out of mathlib scope.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equality or typeclass-search path is introduced).

---

### Mathlib search-status: `cycloTower1_le_unitsTower1` (Phase 5)

Note on environment: the Lean MCP search tools (`lean_loogle`, `lean_leansearch`, `lean_local_search`,
Lean-Finder) are not installed here; Loogle was run via its public JSON endpoint (WebFetch), and method D
(grep mathlib source) was run directly. Each method is recorded with what was actually executed.

[A] Lean-Finder       "cyclotomic units subset principal local units inverse limit", "meet of subgroups below factor"  —  n/a: MCP/web app not reachable from this harness; subsumed by Loogle (B), grep (D), and the Phase-3 literature sweep, which jointly resolve the question.
[B] Loogle            `?a ⊓ ?b ≤ ?b`  →  hits: `inf_le_right` (`Mathlib.Order.Lattice`, `SemilatticeInf`), `min_le_right`, `Std.min_le_right`, etc. The abstract kernel is exactly `inf_le_right`. Loogle on the *concrete* statement (`cycloTower1 _ ≤ unitsTower1 _`) is impossible — the constants are project-local, not in any Loogle-indexed library.
[C] LeanSearch        "cyclotomic units contained in principal local units tower" / "inverse limit subgroup meet inclusion"  —  n/a: NL endpoint not reachable from this harness; the concept ("`a ⊓ b ≤ b`") is unambiguous and already pinned by Loogle to `inf_le_right`, so NL search adds nothing.
[D] Grep mathlib src  `NormCompatUnits`, `cycloTower1`, `unitsTower1`, `cycloClosureOne`, `localUnitsOne`, `cycloClosure`, `localUnits` over `.lake/packages/mathlib/Mathlib/`  →  **0 hits each** (all seven are project-only). Also grepped `inf_le_right`/`inf_le_left` and inverse-limit-of-subgroups machinery (`ProfiniteGrp/Limits.lean`): the only relevant general lemma is `inf_le_right` (`Mathlib/Order/Lattice.lean:87`, simp form line 143); there is **no** generic "inclusion of pointwise-defined inverse-limit subgroups" lemma to specialise from.
[E] Name pattern      grep project + mathlib for `*_le_*Tower*`, `*le_localUnits*`, `*le_globalUnits*`, `inf_le`  →  finds only the *project's own* sibling family (`unitsTower1Plus_le_unitsTower1`, `cycloUnits_le_globalUnits := inf_le_right`, `globalUnits_le_localUnits`, `cycloTower1Plus_le_*`, …). No mathlib name matches the concrete statement.

Searched for both:
  - the user's current form (`cycloTower1 p ≤ unitsTower1 p`) — built entirely from project-only constants; **not in mathlib** (cannot be, by construction).
  - the literature-standard / abstract form (`a ⊓ b ≤ b`) — **in mathlib** as `inf_le_right`
    (`Mathlib/Order/Lattice.lean:87`), the building block the proof is a thin level-wise wrapper of.

Concluded: **found building blocks (`inf_le_right` / `Subgroup.mem_inf`); composition would yield our
form.** The exact concrete statement is *not* in mathlib (it is about objects that exist only in this
project), but its entire proof content is a ≤1–2-call composition of mathlib's meet-projection primitive
threaded through the project's own pointwise tower definition.

---

### Call sites — `cycloTower1_le_unitsTower1` (Phase 6.0)

Internal use count: **4** (within the project, NOT counting the declaring line 239).
External-to-file callers: 1 distinct file outside the declaring file (`IwasawaProof/Main.lean`); plus 1
use inside the declaring file (`cyclo_mem_unitsTower1`).
External-to-project callers: **0** (no downstream library consumes it; it is internal to PadicLFunctions).

| Caller file:line                                   | Usage pattern (one-line excerpt)                                                            |
|----------------------------------------------------|--------------------------------------------------------------------------------------------|
| Iwasawa/CyclotomicUnits.lean:498                   | `cycloTower1_le_unitsTower1 p (cyclo_mem_cycloTower1 p ha hp2 ha1)` (proves `cyclo_mem_unitsTower1`) |
| IwasawaProof/Main.lean:442                          | `mul_mem hu ((unitsTower1 p).inv_mem (cycloTower1_le_unitsTower1 p hc))`                    |
| IwasawaProof/Main.lean:522                          | `galNCU_neg_one_fixed_mem_unitsTower1Plus p hp2 (cycloTower1_le_unitsTower1 p huc_cyclo) huc_fix` |
| IwasawaProof/Main.lean:537–538                      | `mul_mem (cycloTower1_le_unitsTower1 p hu') ((unitsTower1 p).inv_mem (cycloTower1_le_unitsTower1 p hcmem))` |

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?):
  - (none found) — every place that needs "cyclo tower element is a principal-unit tower element" routes
    through this lemma. So it is a genuinely-used internal helper (K = 4 ≥ 3), not dead code. Per the
    Phase-6 signal table, K ≥ 3 with no inline re-derivation normally leans YES — **but** every one of the
    4 consumers is itself internal to this project and is about the project-bespoke towers, so the "real
    API" signal is entirely project-internal; it does not indicate a mathlib-shaped, reusable result. The
    decisive factor is that the *objects* are out of mathlib scope (Phase 5: 0 mathlib hits for all of
    `cycloTower1` / `unitsTower1` / `cycloClosureOne` / `localUnitsOne`), which caps the verdict at a NO
    bucket regardless of internal usage count.

### Composition check (Phase 6)

Can `cycloTower1_le_unitsTower1` be derived from mathlib in ≤3 chained calls? (Here "from mathlib" means:
given the project's own definitions, is the *proof* a trivial composition of mathlib primitives, so that
no standalone lemma earns its keep — it can be inlined?)

Attempt 1: the existing one-line proof term itself —
`fun _ hu n hn => (Subgroup.mem_inf.1 (hu n hn)).2`
  - Mathlib decls used: `Subgroup.mem_inf` (`Mathlib/Algebra/Group/Subgroup/Lattice.lean:233`) and the
    anonymous-constructor projection `.2`. (Equivalently `fun _ hu n hn => inf_le_right (hu n hn)` using
    `inf_le_right`, `Mathlib/Order/Lattice.lean:87`.)
  - Result: **succeeds** — this is the verbatim current proof; 1 mathlib call (`mem_inf`) + a projection.
  - Notes: it is NOT literally `inf_le_right` at the top level only because `cycloTower1`/`unitsTower1`
    are pointwise inverse-limit predicates rather than a single `⊓`; the meet being projected sits one
    level down, inside `cycloClosureOne p n = cycloClosure p n ⊓ localUnitsOne p n`. The compare-point is
    the sibling `cycloUnits_le_globalUnits` (CyclotomicUnits.lean:201–202), which *is* a bare
    `:= inf_le_right` precisely because *that* def is itself a top-level `⊓`. So the only "extra" work here
    is the trivial `fun n hn => … (hu n hn)` re-indexing of the same one fact across the tower.

Conclusion: **COMPOSABLE** — a 1-call composition of mathlib's meet-projection primitive
(`Subgroup.mem_inf` / `inf_le_right`) over the project's own definitions, with a trivial pointwise
quantifier shuffle. No new mathlib-worthy lemma is created by this; the content is `inf_le_right`.

---

## Verdict: `cycloTower1_le_unitsTower1`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the NT inclusion `𝒞_{∞,1} ⊆ 𝒰_{∞,1}` is ambient textbook Iwasawa theory
  (Washington/Lang/Hida; RJW §11.3 treats it as definitional); the structural kernel is the elementary
  meet fact `a ⊓ b ≤ b` (Wikipedia/Nation/nLab) = mathlib `inf_le_right`. Nothing novel.
- Generality analysis (Phase 4): MAXIMALLY GENERAL (0 weakenings); modern-idiom: none — already
  idiomatic; the only abstract kernel is already maximally general in mathlib.
- Mathlib search (Phase 5): the concrete statement is not in mathlib (all of `cycloTower1`,
  `unitsTower1`, `cycloClosureOne`, `localUnitsOne`, `NormCompatUnits` have 0 mathlib hits — they are
  project-only); the building block `inf_le_right` / `Subgroup.mem_inf` IS in mathlib.
- Composition check (Phase 6): COMPOSABLE — the proof is `(Subgroup.mem_inf.1 (hu n hn)).2`, one mathlib
  call plus a projection, equivalently `inf_le_right` applied level-wise.

**Rationale:**

This is glue, not mathematics. The lemma asserts the *definitional* half of the project's milestone: at
every tower level `n ≥ 1`, the cyclotomic local closure is *defined* as the intersection
`cycloClosureOne p n = cycloClosure p n ⊓ localUnitsOne p n`, so projecting onto the second factor gives
membership in `localUnitsOne p n`, and quantifying over `n` lifts this to `cycloTower1 p ≤ unitsTower1 p`.
The whole proof is `(Subgroup.mem_inf.1 (hu n hn)).2` — a single application of mathlib's
`Subgroup.mem_inf` (equivalently `inf_le_right`) plus an anonymous-constructor projection, threaded
through a pointwise `∀ n` shuffle. The sibling lemma `cycloUnits_le_globalUnits` in the same file is
literally `:= inf_le_right`; this one differs only because the `⊓` it projects sits one level deeper
inside the inverse-limit predicate. The genuinely hard content of the milestone — that cyclotomic units
*are* principal (`‖c_n(a) − 1‖ < 1`), proved in `norm_cycloUnit_sub_one_lt_one` and assembled in
`cyclo_mem_cycloTower1` — lives elsewhere; this lemma contributes none of it.

It also cannot go to mathlib because it is a statement *about objects mathlib does not have and will not
have*: `NormCompatUnits`, `cycloTower1`, `unitsTower1`, `cycloClosureOne`, `localUnitsOne` are all
bespoke RJW-tower scaffolding (Phase 5: zero mathlib hits for each). There is nothing here to upstream —
the only reusable nugget, `a ⊓ b ≤ b`, is already `inf_le_right`. The lemma is correct, well-named, and
worth keeping *in the project* as a readable internal helper (4 internal call sites), but it is exactly
the "1–3 mathlib-call composition, inline-able" shape that the NO-composable bucket exists for.

**WHY not (refactor-actionable detail):**

Mathlib already has the building block; the user's form is a 1-call composition of it over project-local
definitions, so no mathlib lemma is warranted. The composition is:
- Mathlib building blocks:
  - `Subgroup.mem_inf` — `.lake/packages/mathlib/Mathlib/Algebra/Group/Subgroup/Lattice.lean:233`
    (`x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p'`)
  - equivalently `inf_le_right` — `.lake/packages/mathlib/Mathlib/Order/Lattice.lean:87`
    (`a ⊓ b ≤ b`, the `SemilatticeInf` field; simp form line 143)

Composition sketch (≤3 lines) — this IS the current proof, shown to make inlining mechanical:
```lean
-- given hu : u ∈ cycloTower1 p, i.e. ∀ n, 1 ≤ n → u.elems n ∈ cycloClosureOne p n,
-- and cycloClosureOne p n = cycloClosure p n ⊓ localUnitsOne p n:
example {u} (hu : u ∈ cycloTower1 p) : u ∈ unitsTower1 p :=
  fun n hn => (Subgroup.mem_inf.1 (hu n hn)).2     -- or: fun n hn => inf_le_right (hu n hn)
```

Call sites in our project (from Phase 6.0): **K = 4**
  - `Iwasawa/CyclotomicUnits.lean:498`
  - `IwasawaProof/Main.lean:442`, `:522`, `:537–538` (two uses on 537–538)

Refactor plan (honest recommendation): this is a genuine **judgment call between two legitimate
project-local choices**, and mathlib's "no wrapper lemmas" rule (search-guide Rule 1) is in tension with
the fact that the objects are out of mathlib scope and the lemma reads well at its 4 sites:
  - Option A (keep it): leave the lemma in the project. It is a clean, named, 4-times-used inclusion that
    documents the milestone's trivial half; inlining `fun n hn => inf_le_right (hu n hn)` at four sites
    (one of which feeds the headline `cyclo_mem_unitsTower1`) would be slightly noisier for no gain. This
    is a *project-cleanup* decision, not a mathlib contribution.
  - Option B (inline): if the project's own cleanup pass wants to honour "no thin wrappers", at each of
    the 4 call sites replace `cycloTower1_le_unitsTower1 p h` with `fun n hn => inf_le_right (h n hn)`
    (or `fun n hn => (Subgroup.mem_inf.1 (h n hn)).2`), then delete the lemma. Argument flow is identical
    (the lemma is already `≤`, used directly as a function).

Next action for the **mathlib question specifically**: **do not** propose this for mathlib. It is not a
mathlib candidate in any form — there is nothing to add (`inf_le_right` already exists) and nothing to
generalise (the towers are project-bespoke). Keep it project-local (Option A) or inline it during a
project cleanup (Option B); either is fine. No mathlib PR.

---

## Next step

Do not open a mathlib PR. The reusable content is already `inf_le_right`
(`Mathlib/Order/Lattice.lean:87`); the statement itself is about project-only objects
(`cycloTower1`/`unitsTower1`/`cycloClosureOne`/`localUnitsOne`/`NormCompatUnits` — zero mathlib hits).
Keep the lemma as a project-internal helper (4 call sites, reads well), or, if a PadicLFunctions cleanup
pass wants to drop thin wrappers, inline `fun n hn => inf_le_right (h n hn)` at the 4 sites
(`CyclotomicUnits.lean:498`, `Main.lean:442/522/537–538`) and delete it. This is a project-cleanup
decision, not a mathlib one.
