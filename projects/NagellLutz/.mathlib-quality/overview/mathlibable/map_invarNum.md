# /mathlibable report — `map_invarNum`

> Mode A, single declaration. AINTLIB `/overview` Step-9 mathlibable assessment of the
> NagellLutz project (Nagell–Lutz theorem; elliptic curves; division polynomials; elliptic
> divisibility sequences; Stange elliptic nets). Source paper being formalised:
> arXiv **2604.05280** "On Elliptic Sequences over Commutative Rings" (Junyan Xu).

---

### Baseline (Phase 0)

- lake build:               not run (local build is stale per task brief; reasoned from source +
                            the pinned mathlib checkout at `.lake/packages/mathlib`). The decl is a
                            single-`simp only` over a one-line `def`, so elaboration is not in doubt.
- decl `map_invarNum`:      ✓ resolved at
                            `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1171`.
- kind:                     `lemma`.
- has sorry:                no.
- module docstring summary: "Elliptic divisibility sequences" — defines EDS, builds normalised
                            EDSs (`normEDS`) from initial terms, and (new vs. upstream) a Stange-
                            elliptic-net apparatus (`addMulSub`/`rel₄`/`net`, the invariant layer
                            `invarNum`/`invarDenom`/`invar`) to prove `IsEllSequence (normEDS …)`.

**Qualified-name verification (the brief asked to VERIFY).** The parse `map_invarNum` is
**correct, and it is NOT `EllSequence.map_invarNum`.** Namespace trace: `namespace EllSequence`
opens at L90 (closes L597) and re-opens at L1079, **closing at L1112** (`end EllSequence`). The
next region is `section Map` (L1116) … `end Map` (L1201) — a plain `section`, **not** a namespace.
The target sits at L1171, inside `section Map`, *outside* any `namespace`. Contrast L1140/L1152,
where the author wrote `lemma EllSequence.map_compl'` / `lemma EllSequence.map_compl` *explicitly*
to land those in the namespace, and deliberately did **not** do so for `map_addMulSub`, `map_rel₄`,
`map_net`, `map_invarNum`, `map_invarDenom`.
**True fully-qualified name: `map_invarNum` (root namespace).**

---

### Statement (Phase 1)

`map_invarNum` is a **naturality / base-change lemma**: a ring homomorphism commutes with the
elliptic-sequence invariant numerator `invarNum`.

The object (`EllSequence.invarNum`, def at L140):
```lean
/-- The numerator of an invariant of an elliptic sequence, such that for each `s`,
`invarNum s n / invarDenom s n` is a constant independent of `n`. -/
def invarNum (s n : ℤ) : R :=
  (W (n + 2 * s) * W (n - s) ^ 2 + W (n + s) ^ 2 * W (n - 2 * s)) * W s ^ 2
    + W n ^ 3 * W (2 * s) ^ 2
```
i.e. `invarNum W s n = (W(n+2s)·W(n−s)² + W(n+s)²·W(n−2s))·W(s)² + W(n)³·W(2s)²`. Together with
`invarDenom W s n = W(n+s)·W(n)·W(n−s)` (L145) it packages the EDS *invariant*: for an elliptic
`W`, the ratio `invarNum s n / invarDenom s n` is independent of `n`.

The lemma (L1171):
```lean
lemma map_invarNum (s m : ℤ) : f (invarNum W s m) = invarNum (f ∘ W) s m := by
  simp only [invarNum, map_add, map_mul, map_pow, Function.comp]
```

Mathematical content: `invarNum` is built entirely from `+`, `*`, `^` of the sequence values
`W(·)`. A ring hom `f` distributes through each (`map_add`, `map_mul`, `map_pow`), and
post-composing the sequence gives `f ∘ W`. Hence `f(invarNum_W s m) = invarNum_{f∘W} s m`. Utterly
routine — the value is purely *bookkeeping* (the invariant is preserved by base change).

Variables / typeclasses (file-level `variable` block, L85–86):
- `{R : Type u} {S : Type v} [CommRing R] [CommRing S]` — source/target commutative rings.
- `(W : ℤ → R)` — an **arbitrary** integer-indexed sequence (no EDS hypothesis is needed; this is
  purely algebraic distribution).
- `{F} [FunLike F R S] [RingHomClass F R S] (f : F)` — an **unbundled** ring homomorphism.

Hypotheses (Lean side): none beyond the typeclasses; `s m : ℤ` are free.
Conclusion (Lean): `f (invarNum W s m) = invarNum (f ∘ W) s m`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**.
Reason: a helper naturality lemma over a one-screen internal `def`; not a named theorem, not a new
structure, not a `## Main results` goal. One member of the `map_*` glue family (`map_addMulSub`,
`map_rel₄`, `map_net`, `map_invarNum`, `map_invarDenom`). (Lit width is exhaustive regardless — the
EDS invariant *is* a real literature concept; see Phase 3.)

### One-line check (Phase 2b)

Kind is `lemma` (not `def`/`abbrev`/`structure`) → the one-liner-`def` exemption table does **not
apply**. Recorded `n/a`. For context: the lemma body is a single `simp only`; the *parent*
`invarNum` it is about is a multi-line `def` (separately assessed in `invarNum.md`, verdict
BORDERLINE). This lemma's fate is tied to that parent (Phase 7).

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | EDS invariant numerator/denominator `W(n+2s)W(n−s)^2`                                           | partial | general EDS recursion is standard; this exact split not surfaced verbatim | Wikipedia/arXiv hits on the recursion; the split is the paper's `s`-parametrisation |
|  2 | WebSearch (naturality form)      | "ring homomorphism commutes with EDS naturality"                                                | yes (object) | surfaces the **source paper** | arXiv **2604.05280** "On Elliptic Sequences over Commutative Rings" (J. Xu) — the work this file formalises |
|  3 | WebSearch (named-after / aliases) | "elliptic sequence" invariant ratio independent of `n`, Ward                                    | **YES** | **Swart's translation invariant** | `(h_{n+2}h_{n−1}² + h_{n+1}²h_{n−2} + A·h_n³)/(h_{n+1}h_n h_{n−1})` = `invarNum/invarDenom` at `s=1` |
|  4 | ChatGPT MCP                       | self-contained Q: standard form + is the map-lemma anything but routine glue?                   | **DOWN** | — | Codex MCP unavailable (Codex exec failed, as the brief warned); compensated by the heavy WebSearch sweep + source reasoning |
|  5 | Local references                  | `projects/NagellLutz/.mathlib-quality/references/`                                              | n/a  | (no references dir) | recorded n/a; the source paper is arXiv 2604.05280 (found via #2) |
|  6 | nLab                              | EDS / functoriality of a polynomial expression under ring homs                                  | partial | "polynomial laws"/naturality is generic | nLab has no EDS page; confirms "ring hom commutes with a polynomial law" is unremarkable folklore |
|  7 | nCatLab (if categorical)          | —                                                                                              | n/a  | not categorical | a polynomial identity of ring elements; nothing 1-/∞-categorical |
|  8 | Stacks Project (if alg geom)      | EDS / elliptic-sequence invariants                                                              | n/a  | not in Stacks | Stacks does not cover EDS / EDS-invariant recurrences |
|  9 | MathOverflow / MSE                | EDS invariant ratio constancy; functoriality                                                    | partial | ratio constancy discussed | the base-change statement is treated as obvious, never a citable lemma |
| 10 | recent arXiv (≤5 yrs)             | source paper + "invariant translation Swart"                                                    | **YES** | confirms Swart invariant in the commutative-ring setting | arXiv 2604.05280 proves translation invariance via the net/Somos-4 relation — the paper formalised here |

Protocol status: WebSearch ran ≥3 queries at distinct generality levels ✓. ChatGPT MCP attempted,
**down** (documented). Local refs checked (absent → n/a). nLab/nCatLab/Stacks/MO/arXiv each checked
or n/a-with-reason ✓.

### Literature summary (Phase 3)

Concept identified as: **Swart's translation invariant of an elliptic sequence** — `invarNum` is
its numerator, `invarDenom` its denominator. Attributed to Swart (PhD thesis, under van der
Poorten); appears in the EDS / Somos-4 literature, and in the commutative-ring generality used here
in the source paper arXiv **2604.05280** (Junyan Xu). The `s = 1` form
`(W(n+2)W(n−1)² + W(n+1)²W(n−2) + b²W(n)³)/(W(n+1)W(n)W(n−1))` matches `invarNum/invarDenom`
exactly — cf. the project's own `invarNum_normEDS` (L972–973).

So the **object** `invarNum/invarDenom` is a genuine, named, literature-standard concept that
mathlib lacks. **But the `map_invarNum` lemma is not a named literature statement**: that a ring
hom commutes with a fixed `+/*/^` polynomial in the values of `W` is generic folklore (nLab
"polynomial laws", #6) that every source assumes silently. The literature therefore bears on
whether `invarNum` belongs in mathlib, and only *derivatively* on `map_invarNum`.

Most general standard form: of the **object**, `invarNum/invarDenom` over an arbitrary `CommRing`
with general shift `s` (the literature usually fixes `s = 1`; the `s`-parametrised numerator is the
paper's generalisation). Of the **lemma**, none — the relevant "standard" is mathlib's own
`map_<construction>` naturality convention.
Disagreement with the literature: none.

---

### Generality analysis — `map_invarNum` (Phase 4)

Literature-standard form (from Phase 3): n/a for the *lemma* (no named map-lemma). Benchmark =
mathlib's own `map_normEDS` / `map_preNormEDS` / `map_complEDS` family in
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:510–545`.

| # | Parameter / hypothesis | Current Lean form                                         | Benchmark (mathlib `map_*`)        | Weaker form exists? | Reason |
|---|------------------------|-----------------------------------------------------------|------------------------------------|---------------------|--------|
| 1 | ring hom `f`           | `[FunLike F R S] [RingHomClass F R S] (f : F)` (unbundled) | `(f : R →+* S)` (bundled)           | already MORE general | the unbundled `RingHomClass` form is *strictly more general* than mathlib's bundled `→+*` — covers any `F` with the class |
| 2 | `R`, `S`               | `[CommRing R] [CommRing S]`                               | `[CommRing R] [CommRing S]`         | borderline (def-level) | `invarNum` uses only `+,*,^` (no subtraction), so it could live over `CommSemiring`/`CommMonoid`+`AddCommMonoid`; but that is a property of the **def**, not this lemma |
| 3 | sequence `W`           | arbitrary `W : ℤ → R`                                     | (mathlib lemmas target a specific construction, not a free `W`) | NO — already maximal | `W` is fully arbitrary |
| 4 | indices `s m`          | free `ℤ`                                                  | free `ℤ`                            | NO                  | already maximal (and already `s : ℤ`, the paper's generalisation of the classical `s=1`) |

#### Generality verdict (Phase 4b)

The current form is **MAXIMALLY GENERAL** (indeed *more* general than the mathlib benchmark, via
the unbundled `RingHomClass` hom and the fully-free `W`). Meaningful weakening opportunities at the
lemma level: 0. The only theoretical weakening (`CommRing`→`CommSemiring`) is a **def-level**
property of `invarNum`, not actionable on `map_invarNum`. Proposed restatement: none. Cost: n/a.

#### Modern-idiom check — Bourbaki 2.0 (Phase 4c)

| #  | Question                                          | Applies? | Reformulation | Downstream |
|----|---------------------------------------------------|----------|---------------|------------|
|  1 | "let f be a hom" → typeclass/instance?            | already done | — | the decl already uses unbundled `RingHomClass`, the modern idiom |
|  2 | sequences/metric → filters/nets/topology?         | no | — | finite ring-element identity; no topology (here "net" is Stange's, not a topological net) |
|  3 | construct → universal-property class?             | no | — | nothing constructed |
|  4 | set+closure-pred → bundled substructure?          | no | — | no substructure |
|  5 | vector-space/field-specific → modules/(semi)ring? | def-level only | (def) `invarNum` over `CommSemiring`/`CommMonoid`+`AddCommMonoid` | would let `map_invarNum` use a weaker hom — but that travels with the **def**, not this lemma |
|  6 | 1-categorical → higher/∞-categorical?             | no | — | not categorical |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary monoid/group?    | no | — | the `ℤ` index is intrinsic to EDS (`W : ℤ → R`) |

**Modern-idiom verdict (Phase 4c):** modern idiom **available = no** (the lemma is already in the
modern unbundled form, and uses the same `f ∘ W` naturality idiom as mathlib's
`EllipticCurve.Jacobian.Point.map_neg`/`map_add`). One caveat in the *opposite* direction: the
sibling upstream `map_*` EDS simp-lemmas use the **bundled `f : R →+* S`** with `@[simp]`. So if
upstreamed, the contribution would likely be *re-bundled* to match `map_normEDS` et al. and tagged
`@[simp]` — a cosmetic alignment, not a mathematical change.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or typeclass-search paths
introduced).

---

### Mathlib search-status: `map_invarNum` (Phase 5)

Five-method search. (lean_loogle / lean_leansearch MCP indices were not exposed as tools in this
environment; substituted the **authoritative local mathlib source** at the pinned commit
`.lake/packages/mathlib/`, plus name-pattern reasoning.)

```
[A] Lean-Finder       n/a — index not reachable here; covered by [B]/[C]/[D]/[E]
[B] Loogle            `_ (invarNum _ _ _) = invarNum _ _ _` shape       no hits (invarNum absent from mathlib)
[C] LeanSearch        "ring hom commutes invariant elliptic sequence"   no hits (mathlib EDS theory has no invariant layer)
[D] Grep mathlib src  `invarNum` / `invarDenom` over Mathlib/           ZERO HITS anywhere in mathlib
                      `addMulSub`/`rel₄`/`net` in NT EDS file           ZERO HITS (the whole net+invariant apparatus is absent)
[E] Name pattern      `map_normEDS|map_preNormEDS|map_complEDS`          HIT — the sibling family exists
                      (Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:510–545, all @[simp], bundled hom)
```

Searched for **both** forms:
- user's form (`map_invarNum` about a free `W` with `f ∘ W`): **not in mathlib**.
- the sibling/general form (mathlib's `map_<EDS-construction>`): the *family* exists, but **no
  member is about `invarNum`** — because **`invarNum` itself is not in mathlib**
  (verified by [D]: `grep -rn invarNum .lake/packages/mathlib/Mathlib/` → 0 files). Mathlib's EDS
  `map_*` lemmas are all **coefficient-shaped** (`f (normEDS b c d n) = normEDS (f b) (f c) (f d) n`),
  structurally unlike `map_invarNum`'s composition-shaped `f ∘ W`.

Decisive context: upstream `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` has the base
predicate `IsEllSequence` (and `isEllSequence_id`, `IsEllSequence.smul`) but **none** of the
project's net/invariant apparatus. The `EllSequence` invariant machinery (`addMulSub`, `rel₄`,
`net`, `invarNum`, `invarDenom`, `invar_of_net`, `IsEllSequence.invar`, …) is a **new development**,
present in this repo only.

Concluded: **"not in mathlib"** — all source/name methods exhausted, *and* the parent `invarNum`
definition is absent, so no member of the existing `map_*` family covers it.

---

### Call sites — `map_invarNum` (Phase 6.0)

Internal use count (this project, excluding the declaring line): **1.**
External-to-file callers: 0 (the one use is inside the declaring file).

| Caller file:line                                         | Usage pattern (one-line excerpt)                                                |
|----------------------------------------------------------|---------------------------------------------------------------------------------|
| EllipticDivisibilitySequence.lean:1496 (`invar₂_normEDS`)| `simp only [map_mul, map_invarNum, map_invarDenom, map_add, map_pow, aeval_X] …` |

So `map_invarNum` is a **link in the universal-EDS argument**: `invar₂_normEDS` (proof L1485–1496)
lifts the invariant identity `invarNum (normEDS …) 1 m · c = invarDenom (normEDS …) 1 m · (d + b⁴)`
from the universal `MvPolynomial Param ℤ`-valued EDS down to an arbitrary `CommRing` via
`aeval`/base change. `map_invarNum` is exactly the step "push `aeval` through `invarNum`" in that
descent — part of the invariant/Nagell–Lutz development the project is building.

Duplication across the consolidation monorepo (the project context flagged this): the **identical**
lemma appears in
- `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:143`
- (target) `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1171`
forks of the same `EllSequence` development. No consumer re-derives the fact inline; each routes
through this lemma within its own fork.

Call-sites signal: **K = 1 internal use, single descent step, no external consumers** → on the
call-sites table this is the "possibly the wrong abstraction / private API surface" pattern. But the
more important signal is *what it is about*: a non-mathlib definition (`invarNum`).

### Composition check (Phase 6a)

Can `map_invarNum` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: unfold + `map_add`/`map_mul`/`map_pow`.
  - The statement mentions `invarNum` on **both sides**, and `invarNum` is **not a mathlib symbol**,
    so one cannot *state* — let alone prove — this lemma using only mathlib decls. Once `invarNum`
    is introduced *in the project*, the body is the one-line `simp only [invarNum, map_add, map_mul,
    map_pow, Function.comp]` — three mathlib primitives + the project def. As a *project* fact it is
    a trivial ≤3-primitive `simp` composition; as a *mathlib* composition it fails, because the
    objects are project-local.
  - Result: **trivially composable given the project's `invarNum`; NOT composable from mathlib
    alone** (the building blocks on both sides are project-local).

Conclusion: **NOT-COMPOSABLE *from mathlib*.** It is trivially provable *given the project's
`invarNum`*, but that is the point: the lemma is meaningless without the project def, so it is not
an "inline a mathlib composition at the call site and delete" situation — you cannot replace its
call site with mathlib calls, because the very objects involved (`invarNum`/`invarDenom`) are not in
mathlib.

---

### Glue-lemma inheritance (Phase 7)

The skill's glue-lemma rule: a naturality lemma whose *entire reason to exist* is a project-local
parent `def` should **inherit the parent's verdict** rather than be assessed standalone.

- Parent `invarNum` (the `def`, L140) was assessed in `invarNum.md` → **BORDERLINE-needs-human**
  (mathlib lacks it — it is Swart's translation invariant, absent from mathlib's EDS theory; cannot
  cheaply compose it; whether/how/at what grain to upstream the invariant layer is maintainer-taste).
- The directly-analogous sibling one rung down, `map_addMulSub` (`map_addMulSub.md`), also landed
  **BORDERLINE-needs-human** for the identical structural reason (its parent `addMulSub` is not in
  mathlib).
- Contrast `map_normEDS` (`map_normEDS.md`) → **NO-mathlib-has-it**: that one is NO *only because*
  its parent `normEDS` **is** in mathlib and `map_normEDS` **is literally already** upstream
  (L530). `map_invarNum` differs on exactly that hinge — `invarNum` is **not** upstream — so it is
  **not** a NO-mathlib-has-it.

`map_invarNum` therefore inherits the BORDERLINE verdict of its parent. It is genuinely true,
maximally general, and rides a pattern mathlib already endorses (the `@[simp] map_*` EDS family),
but it is not a standalone contribution: it ships (or not) with the invariant apparatus, and the
packaging/grain decision is human/maintainer territory.

---

## Verdict: `map_invarNum`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature search (Phase 3): the **object** `invarNum/invarDenom` = **Swart's translation
  invariant** (named, in the EDS literature; commutative-ring generalisation in arXiv 2604.05280,
  the paper being formalised). The **naturality lemma is not a named literature statement** — it is
  folklore "ring hom commutes with a polynomial law" bookkeeping. No external standard to match the
  lemma to.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** — unbundled `RingHomClass` hom (strictly
  more general than the upstream bundled `→+*`), arbitrary `W`, free `ℤ` indices. The only
  adjustment if upstreamed is cosmetic re-bundling to `f : R →+* S` + `@[simp]` to match the sibling
  family.
- Mathlib search (Phase 5): **not in mathlib**, and — decisively — the **parent `invarNum` def is
  also absent** (zero `invarNum` hits across the whole `Mathlib/` tree; mathlib's EDS file has only
  the base `IsEllSequence` and a coefficient-shaped `map_*` family, never the invariant layer).
- Composition check (Phase 6a): **NOT-COMPOSABLE from mathlib** (the objects on both sides are
  project-local; trivial *given* `invarNum`, impossible to state with mathlib symbols alone).
- Glue-lemma inheritance (Phase 7): inherits the parent `invarNum`'s **BORDERLINE** verdict;
  matches the analogous `map_addMulSub` (BORDERLINE) and is distinguished from `map_normEDS` (NO)
  precisely because `invarNum` is not upstream.

**Rationale.**
`map_invarNum` is true, maximally general, and belongs to a pattern mathlib *already endorses* —
upstream `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` carries the exact sibling family
`map_preNormEDS' / map_preNormEDS / map_complEDS₂ / map_normEDS / map_complEDS' / map_complEDS`,
all `@[simp]`. So "a ring hom commutes with the EDS building blocks" is unambiguously
mathlib-welcome *as a pattern*; that pulls toward YES.

But the bucket cannot be a clean YES, and is not a NO, because of one structural fact:
**`invarNum` itself — Swart's translation invariant — is not in mathlib.** `map_invarNum` is a glue
lemma whose only purpose is the project-local `invarNum` def and the universal-EDS descent built on
it (its sole call site is `invar₂_normEDS`, the `aeval` base-change step). Per the glue-lemma rule
it inherits its parent's verdict — and the parent `invarNum` is itself **BORDERLINE** (mathlib lacks
the whole EDS-invariant layer; whether to upstream it, in what grain, with `invarNum` public vs. an
internal detail, bundled-vs-unbundled hom, are taste/policy calls). The natural unit of contribution
is the **EDS-invariant apparatus** (`invarNum`/`invarDenom`/`invar_of_net`/`IsEllSequence.invar` and
the `map_*` glue) shipped in one coordinated PR — ideally by an author already maintaining the
upstream EDS file — not this one glue lemma plucked out. Cost is **not** the reason for BORDERLINE
(the lemma is a one-liner); the genuine human judgment is the *packaging/grain* question, which is
exactly what BORDERLINE is for.

**Refactor-/upstreaming-actionable detail.**
This lemma rides with its parent definition. Decision tree for a human:

1. **Is the project planning to upstream the EDS-invariant apparatus** (`invarNum`/`invarDenom`/
   `invar_of_net`/`IsEllSequence.invar`, resting on the `addMulSub`/`rel₄`/`net` layer — i.e.
   Swart's translation invariant over a commutative ring, the heart of arXiv 2604.05280)?
   - If **yes** → `map_invarNum` ships **as part of that PR**, alongside `map_invarDenom`,
     `map_addMulSub`, `map_rel₄`, `map_net` (re-bundled to `f : R →+* S` and tagged `@[simp]` to
     match `map_normEDS` et al.). It is NOT a separate contribution; it may even be left
     internal/unadvertised if `invarNum` is treated as a building block.
   - If **no** → it stays a project-internal helper; nothing to upstream now, and the standalone
     verdict collapses to "not a contribution" (effectively NO-composable-from-mathlib: inline the
     one-line `simp [invarNum, map_add, map_mul, map_pow]` at its single call site, L1496, and
     delete).
2. **Monorepo dedup (orthogonal to mathlib, an AINTLIB `/cleanup` job):** the identical lemma is
   duplicated in `HasseWeil/.../EllipticDivisibilitySequence.lean:143` and the NagellLutz target.
   Whatever the mathlib decision, these forks of the `EllSequence` development should be
   consolidated to one shared copy within AINTLIB.

**Numbered questions (≤5):**
1. Does the project intend to upstream the new EDS-invariant apparatus (Swart's translation
   invariant `invarNum`/`invarDenom`/`invar_of_net`/`IsEllSequence.invar`, with the underlying
   `addMulSub`/`rel₄`/`net`) to mathlib? (If no, `map_invarNum` is not a standalone mathlib
   candidate — inline at L1496 and delete.)
2. If yes, should `invarNum` be **public** mathlib API (making `map_invarNum` a public `@[simp]`
   lemma like `map_normEDS`), or an internal/`private` implementation detail (making `map_invarNum`
   internal too)?
3. Should the upstreamed form be **re-bundled** to `f : R →+* S` and tagged `@[simp]` to match the
   existing `map_normEDS / map_preNormEDS / map_complEDS` family (recommended for consistency)?
4. Should `invarNum`/`invarDenom` first be **generalised at the def level** from `CommRing` to
   `CommSemiring` (they use only `+,*,^`)? This is a def-level `/generalise` question that determines
   the final hypotheses of the shipped naturality lemma.
5. Are the monorepo copies (HasseWeil aux + NagellLutz target) meant to be deduplicated into one
   shared AINTLIB module first (an AINTLIB `/cleanup`/`/generalise` task, independent of mathlib)?

**Next action:** user (ideally coordinating with the upstream EDS-file author) answers Q1–Q5; the
verdict then collapses to **NO-composable-from-mathlib / "not a standalone contribution"** if the
apparatus is *not* upstreamed, or **YES-add-as-is *as part of the apparatus PR*** (re-bundled,
`@[simp]`) if it *is*. Drive the decision off the parent `def` `invarNum` (`/mathlibable invarNum`,
already BORDERLINE), since this glue lemma inherits that verdict and should travel in the same PR as
`map_invarDenom` / `map_addMulSub` / `map_rel₄` / `map_net`, not alone.

---

## Next step

Answer the numbered questions above (Q1 is the hinge: is Swart's translation-invariant apparatus
being upstreamed?). Because `map_invarNum` is a glue lemma over the project-local `invarNum`, assess
the **parent definition** `invarNum` first (`/mathlibable invarNum` — verdict already BORDERLINE);
this lemma inherits that verdict and should travel in the same PR as the rest of the `map_*`
invariant glue, not alone. Independently, file an AINTLIB `/cleanup` dedup for the duplicated copies
of the `EllSequence` development.

---

### Sources

- [Elliptic divisibility sequence — Wikipedia](https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence)
- [J. Xu, *On Elliptic Sequences over Commutative Rings*, arXiv:2604.05280](https://arxiv.org/pdf/2604.05280) — the source paper formalised here; proves Swart's translation invariance over a commutative ring
- [K. Stange, *Elliptic nets and elliptic curves*, arXiv:0710.1316](https://arxiv.org/pdf/0710.1316)
- [*The ECDLP and equivalent hard problems for EDS*, arXiv:0803.0728](https://arxiv.org/pdf/0803.0728)
- [Mathlib.NumberTheory.EllipticDivisibilitySequence (mathlib4 docs)](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EllipticDivisibilitySequence.html)
- Local pinned mathlib source: `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
  (base predicate `IsEllSequence` present; `invarNum`/`invarDenom`/`addMulSub`/`rel₄`/`net` absent;
  coefficient-shaped `@[simp] map_*` family at L510–545, bundled `f : R →+* S`)
- Sibling reports (same `/overview` run): `invarNum.md` (parent def → BORDERLINE),
  `map_addMulSub.md` (analogous glue → BORDERLINE), `map_normEDS.md` (NO-mathlib-has-it, the
  contrasting hinge)
