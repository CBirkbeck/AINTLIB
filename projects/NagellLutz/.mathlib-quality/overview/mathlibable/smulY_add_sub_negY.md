# /mathlibable report — `WeierstrassCurve.Universal.Affine.smulY_add_sub_negY`

> Step-9 mathlibable assessment, NagellLutz project (Nagell–Lutz; elliptic curves; division
> polynomials; elliptic divisibility sequences). Reasoned from source (local Lean build stale).

## Baseline (Phase 0)
- lake build:               not run (prompt: local build stale; reasoned from source per instructions)
- decl `WeierstrassCurve.Universal.Affine.smulY_add_sub_negY`:
                            ✓ resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:324`
- qualified name:           VERIFIED — namespaces nest `WeierstrassCurve` (L76) → `Universal` (L86)
                            → `Affine` (L157); decl at L324 is a public `lemma`.
- kind:                     lemma (theorem-like; not a `def`/`class`/`instance`)
- has sorry:                no
- module docstring summary: Expresses `n • P` in Jacobian/affine coords via division polynomials on
                            a Weierstrass curve; proves `WeierstrassCurve.zsmul_eq_smulEval`. The
                            docstring explicitly names `smulY_add_sub_negY` (L65, L70) as one of the
                            "fancy identities of division polynomials and elliptic divisibility
                            sequences" that drive the strong-induction step, and notes its proof
                            "requires 2 to be invertible".

## Statement (Phase 1)

`smulY_add_sub_negY` is an **algebraic interpolation identity for the "doubled `Y`-coordinate"**
(`ψ₂(x,y) := y − negY(x,y) = 2y + a₁x + a₃`) of a sum of integer multiples of the distinguished
point `(X,Y)` on the universal Weierstrass curve.

Working in `Universal.Field` (the fraction field of `ℤ[A₁,A₂,A₃,A₄,A₆,X,Y]/⟨Weierstrass poly⟩`),
with `smulX n = φₙ/ψₙ²` and `smulY n = ωₙ/ψₙ³` the affine coordinates of `n • (X,Y)`, the lemma
states: for nonzero `m, n, n+m, n−m`,

```
ψ₂(smulX(n+m), smulY(n+m))
  = [ ψ₂(smulX m, smulY m)·(smulX n − smulX(n+m))
      − ψ₂(smulX n, smulY n)·(smulX m − smulX(n+m)) ] / (smulX m − smulX n).
```

Mathematically: the value of the affine function `ψ₂ = 2Y + a₁X + a₃` at the point `(n+m)•P` is the
linear interpolation, in the `X`-coordinate, of its values at `n•P` and `m•P`. The proof rewrites
every `ψ₂(…) − negY` and every `smulX − smulX` difference into ratios of `ψᵤ` (the universal `ψ`
family) via `smulY_sub_negY`/`smulX_sub_smulX`, clears denominators with a field-algebra aux lemma
(`smulY_add_sub_negY_aux`, proved by `field_simp`), and finishes with the **elliptic-net relation**
`EllSequence.net ψᵤ (·) n m (·) = 0` (`net_ψᵤ`, via `net_add_sub_iff`) plus `linear_combination …
ring_nf`.

Variables / typeclasses (Lean side):
- `{m n : ℤ}` — the two integer multiples (implicit, from the `Affine` section's `variable`).
- Ambient: the fixed `Universal.Field` and its distinguished `pointedCurve` — **not** parameters;
  the whole development is over this one universal object.

Hypotheses:
- `hm : m ≠ 0`, `hn : n ≠ 0`, `add_ne : n + m ≠ 0`, `sub_ne : n − m ≠ 0` — keep every `ψᵤ` in a
  denominator nonzero (`ψᵤ k ≠ 0 ↔ k ≠ 0`) so the divisions are valid.

Conclusion (math): the `ψ₂`-interpolation identity above.
Conclusion (Lean): an equation in `Universal.Field` (under a `let ψ₂ x y := y − negY x y` binder).

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: an internal helper lemma (an equation in `Universal.Field`), explicitly described in the
file docstring as one of the induction-driving "identities", not a `## Main results` entry and not
named after a person/place. (Literature width run EXHAUSTIVE regardless.)

## One-line check (Phase 2b)

Kind is `lemma`, not a `def`/`abbrev`/`structure` — one-line check **n/a**.

## Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found                                   | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|--------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | EDS / division-polynomial addition formula, `Y`-coordinate, `negY`, universal Weierstrass curve         | no   | general EDS addition recurrences only; no `ψ₂`-of-sum interpolation identity | Wikipedia EDS; arXiv 2102.07573; eprint 2008/444 — recurrences for `ψ`, not this glue form |
|  2 | WebSearch (general form)         | Stange elliptic nets "net" relation, `ψ`/`ω` formula, three-term, sum-of-points `Y`-coordinate          | no   | elliptic-net recurrence `W(p+q)W(p−q)W(r)² = …` (Ward/Stange) | the *net* relation IS in the literature; the project's `ψ₂`-interpolation packaging of it is not |
|  3 | WebSearch (named-after / aliases)| homogeneous division polynomials Weierstrass; division polynomials for arbitrary isogenies (Stange 2025)| no   | `φ,ψ,ω` definitions + recurrences | arXiv 1303.4327, eprint 2025/521 — define the polynomials; no such named coordinate lemma |
|  4 | ChatGPT MCP                      | "Is this `ψ₂`-of-sum identity a named theorem vs. a glue lemma; usual generality; abstract supersession?"| n/a  | — | **Codex backend errored** (prompt warned MCP may be down); WebSearch used as the mandated fallback |
|  5 | Local references                 | `.mathlib-quality/references/` for division polynomial / EDS notes                                       | n/a  | (no references dir present for this project)           | recorded n/a |
|  6 | nLab                             | "elliptic divisibility sequence" / "division polynomial"                                                 | no   | nLab has no dedicated EDS/division-polynomial coordinate-identity page | concept is classical NT, not nLab-categorical |
|  7 | nCatLab (if categorical)         | —                                                                                                       | n/a  | —                                                      | not a categorical concept |
|  8 | Stacks Project (if alg geom)     | division polynomial / elliptic divisibility sequence                                                     | n/a  | —                                                      | Stacks has no elliptic-curve division-polynomial chapter |
|  9 | MathOverflow / Math.StackExchange| EDS addition / `ψ₂` sum-of-points identity generality                                                    | no   | scattered EDS recurrence Q&A; nothing matching this specific identity | — |
| 10 | recent arXiv (last 5 years)      | division polynomials arbitrary isogenies (Stange 2503.15428 / eprint 2025/521)                           | no   | modern `φ,ψ,ω` + nets framework | confirms the *building blocks* are standard; this packaged identity is not a stated result |

The protocol passed: WebSearch ran 3 distinct queries at different generality levels (specific
form / general "net" form / named-after & modern-isogeny); ChatGPT MCP attempted and recorded
n/a-with-reason (backend down); local refs / nLab / nCatLab / Stacks / MathOverflow / arXiv each
checked or n/a-with-reason.

### Literature summary (Phase 3)

Concept identified as: an internal **`ψ₂ = 2Y + a₁X + a₃` linear-interpolation identity** for the
doubled `Y`-coordinate of `(n+m)•P`, derived from the **elliptic-net relation** `net(ψ) = 0`
(Ward's EDS recurrence / Stange's elliptic nets) specialised to the universal curve.
Sources agree on the standard form: **no** — the literature states the *net / EDS addition
recurrence* (for `ψ`) and the standard `φ/ψ², ω/ψ³` coordinate formulas, but **does not** state this
particular `ψ₂`-of-a-sum interpolation identity as a named result. It is the Lean proof's bespoke
repackaging of `net(ψᵤ) = 0` into the exact shape the induction step consumes.
Most general standard form: the elliptic-net / EDS three-term recurrence over an arbitrary
commutative ring (already in mathlib as `IsEllSequence` / `normEDS`); this lemma is a *downstream
coordinate consequence*, not the recurrence itself.
Generality dimensions where the literature varies: base ring (field vs. arbitrary CommRing via the
universal curve) — but the project deliberately works over the **universal** object precisely to
get the most general (`char`-free, all-coefficients) statement, then specialises.
Disagreement with the literature: none — it is a faithful, if narrowly-packaged, consequence of the
standard net relation.

## Generality analysis — `WeierstrassCurve.Universal.Affine.smulY_add_sub_negY`

Literature-standard form (from Phase 3): the elliptic-net relation `net(ψ) = 0` over an arbitrary
commutative ring; the coordinate `ψ₂`-interpolation is a specialisation.

| # | Parameter / hypothesis        | Current Lean form                          | Literature-standard form        | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------|--------------------------------------------|---------------------------------|---------------------|----------------------------------|
| 1 | ambient field                 | the fixed `Universal.Field` (Frac of `ℤ[Aᵢ,X,Y]/⟨P⟩`) | EDS recurrence over any CommRing | NO (by design)      | working over the **universal** field already yields the *most general* coefficient-free statement; any concrete curve over any field is a ring-hom image (`ringEval`). Generalising further is meaningless — this *is* the universal case. |
| 2 | `hm,hn,add_ne,sub_ne : · ≠ 0` | four nonvanishing hyps                      | needed wherever `ψ` sits in a denominator | NO                  | each guards a `ψᵤ k ≠ 0` for a denominator; the statement is a ratio identity, so the hyps are intrinsic, not slack. |
| 3 | the identity's *shape*        | `ψ₂`-interpolation over `smulX`/`smulY`     | `net(ψ) = 0`                    | n/a                 | the shape is dictated by the consumer (`addX_eq_addX_negY_sub` / `addY_sub_negY_addY` induction); it is not a knob to widen. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (it is *the* universal-curve case; concrete curves follow
by `ringEval`/`polyEval` specialisation — the project's whole design point).
Number of weakening opportunities found: **0**.
Cost of restatement: n/a (nothing to restate).

### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Proposed reformulation | Mathlib downstream |
|----|--------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | "let X be a foo" preamble → typeclass/instance?                          | no       | — | already typeclass-driven (`CommRing`, `Field`, `WeierstrassCurve`) |
|  2 | sequences/metric → filters/topological?                                  | no       | — | purely algebraic identity; no analysis |
|  3 | construction → universal-property class?                                 | partial  | the *parent* `Universal` framework is itself the universal-property packaging; this leaf lemma rides on it | n/a at leaf level |
|  4 | set-with-closure-predicate → bundled substructure?                       | no       | — | no substructure |
|  5 | vector-space/field-specific → weaken typeclass to module/ring?           | no       | — | already at the universal `CommRing`/its Frac field; cannot weaken (see 4a row 1) |
|  6 | 1-categorical → higher-categorical?                                      | no       | — | not categorical |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary monoid/group?                           | no       | — | indices are genuinely `ℤ` (the `ℤ`-action on the curve); not a generalisable index |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. The lemma is an algebraic equation in a fixed universal field; there
is no filter/typeclass/categorical reformulation that improves it. Its "modernity" is entirely
inherited from the parent `Universal` framework, which it does not itself define.

## Diamond / defeq risk — n/a

Declaration kind is `lemma` — Phase 4.5 skipped (no definitional equalities / instance-search paths
introduced).

## Mathlib search-status: `WeierstrassCurve.Universal.Affine.smulY_add_sub_negY`

[A] Lean-Finder       (index unavailable here)                              n/a — mathlib index tool not reachable in env
[B] Loogle            (index unavailable here)                              n/a — could not run; reasoned via source grep instead
[C] LeanSearch        (index unavailable here)                              n/a — could not run
[D] Grep mathlib src  `smulY_add_sub_negY`, `smulX`/`smulY` defs, `add_sub_negY`,
                      `EllSequence.net`, `net_add_sub_iff`, `namespace Universal`,
                      `WeierstrassCurve.Universal`                          NO HITS in `.lake/packages/mathlib/`
[E] Name pattern      `smulX`/`smulY`/`smulY_add_sub_negY` repo-wide        hits ONLY in the two project forks (see below)

Searched for both the user's current form and the literature-standard form. Findings:
- **`smulX` / `smulY` / `smulY_add_sub_negY` do NOT exist in the mathlib tree.** Repo-wide they
  appear only in **two project copies**: `projects/NagellLutz/LutzNagell/ZSMul.lean` (this file) and
  `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:395` — **byte-identical** (verified
  by `diff`); the `Universal` track is forked into both projects.
- **`WeierstrassCurve.Universal` (the universal curve, `Universal.Ring`, `Universal.Field`) is absent
  from mathlib.** (`grep` for `namespace Universal` / `WeierstrassCurve.Universal` in
  `.lake/packages/mathlib/Mathlib/` finds only unrelated `UniversallyOpen` / `UniversalEnveloping`.)
- **`EllSequence.net` and `net_add_sub_iff` (the proof's mathematical backbone) are project-local**,
  defined in each project's own `EllipticDivisibilitySequence.lean` — **not** in
  `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (which has `IsEllSequence`, `normEDS`,
  `complEDS`, but no `net`).
- Mathlib *does* have the curve-side affine helpers the induction consumes —
  `WeierstrassCurve.Affine.addX_eq_addX_negY_sub` and `…addY_sub_negY_addY`
  (`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean:359,381`) — and the EDS scaffolding
  `IsEllSequence`/`normEDS` (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`). But these are
  *ingredients*, not this lemma.

Concluded: **not in mathlib** (grep over the mathlib tree exhausted for both the user's form and the
literature-standard "net" form; index tools unavailable but the source grep is dispositive — the
entire `smulX`/`smulY`/`Universal.Field` vocabulary the statement is phrased in does not exist in
mathlib, so the statement is not even expressible there yet).

## Call sites — `WeierstrassCurve.Universal.Affine.smulY_add_sub_negY`

Internal use count: **1** (within NagellLutz, excluding the declaring file's own region): used at
`ZSMul.lean:371` inside `zsmul_point_eq_smulX_smulY` —
`convert smulY_add_sub_negY (n := n2) one_ne_zero (by omega) (by omega) (by omega) using 1` — i.e. it
is the `Y`-coordinate half of the induction step proving `n • P = (smulX n, smulY n)`.
External-to-file callers: 0 in NagellLutz. (A second, independent copy exists in HasseWeil and is
used analogously at `DivisionPolynomial.lean:443` — a duplicate of the whole track, not a consumer.)

| Caller file:line       | Usage pattern (one-line excerpt)                                              |
|------------------------|-------------------------------------------------------------------------------|
| ZSMul.lean:371         | `convert smulY_add_sub_negY (n := n2) one_ne_zero (by omega) (by omega) (by omega) using 1` |

Inline-derivation grep (re-derived without using the lemma elsewhere?): (none) — the only other
occurrence is the verbatim fork in HasseWeil, which has its own copy of the lemma.

Signal: single internal consumer, tightly coupled to `smulX`/`smulY`; classic glue lemma. Combined
with "the vocabulary isn't in mathlib", this firmly excludes the NO-mathlib-has-it / NO-composable
buckets (you cannot inline a mathlib composition for a statement mathlib cannot express).

## Composition check (Phase 6)

Can `smulY_add_sub_negY` be derived from mathlib in ≤3 chained calls?

Attempt 1: phrase the statement using only mathlib decls and compose.
  - **Blocked at the statement level.** The conclusion is an equation among `ψ₂(smulX·, smulY·)`
    terms in `Universal.Field`. Mathlib has neither `smulX`/`smulY`, nor `Universal.Field`, nor
    `EllSequence.net`/`net_add_sub_iff`. There is no mathlib expression to compose toward.
  - Result: fails.
Attempt 2: ignore the universal packaging and try the underlying `net(ψ) = 0` ⇒ identity over a
generic field, using mathlib's `IsEllSequence`/`normEDS`.
  - Mathlib's EDS API stops at `IsEllSequence`/`normEDS`/`complEDS`; it has no `net` four-argument
    relation and no `net_add_sub_iff`, and no `φ/ψ², ω/ψ³` coordinate functions. Recovering this
    identity would mean **first porting** `net` + `net_add_sub_iff` + the `smulX`/`smulY` layer —
    i.e. building the missing API, not composing existing primitives.
  - Result: fails (a multi-lemma development, not a ≤3-call composition).

Conclusion: **NOT-COMPOSABLE** — the prerequisite vocabulary and the `net` lemma are absent from
mathlib; this is not a 1–3-call inline.

## Verdict: `WeierstrassCurve.Universal.Affine.smulY_add_sub_negY`

**Category:** BORDERLINE-needs-human

**Evidence:**
- Literature search (Phase 3): the *net / EDS addition recurrence* is standard (Ward, Stange), but
  this specific `ψ₂`-of-a-sum interpolation packaging is **not a named/citable theorem** — it is the
  Lean induction's bespoke glue (the file docstring itself lists it as an induction-driving identity).
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** (the universal-curve case; 0 weakenings; no
  modern-idiom improvement at the leaf — modernity is inherited from the parent framework).
- Mathlib search (Phase 5): **not in mathlib**; moreover `smulX`/`smulY`/`Universal.Field` and
  `EllSequence.net`/`net_add_sub_iff` are all **absent** from mathlib — the statement is not yet
  *expressible* there. Forked identically into NagellLutz + HasseWeil.
- Composition check (Phase 6): **NOT-COMPOSABLE** (no mathlib vocabulary to compose toward).

**Rationale (1–2 paragraphs):**

This is not a NO bucket: mathlib neither has the result nor the primitives to express it
(`smulX`/`smulY`, `Universal.Field`, and the `EllSequence.net` four-place relation with
`net_add_sub_iff` are all project-local), so neither NO-mathlib-has-it nor NO-composable-from-mathlib
can fire. Nor is it a clean YES-add-as-is on its own: it is a **single-consumer glue lemma** (one
call site, `ZSMul.lean:371`) phrased entirely in terms of the unlanded `Universal` framework, whose
mathematical content (`net(ψ) = 0`) the literature carries only as the *net recurrence*, not as this
`ψ₂`-interpolation identity. It is meaningless to upstream `smulY_add_sub_negY` in isolation: it
would drag in `smulX`/`smulY`, the universal curve/ring/field construction, `EllSequence.net`, and
`net_add_sub_iff` — a substantial development, all authored by **Junyan Xu** (the mathlib author of
the existing division-polynomial / EDS files), which strongly suggests this whole `ZSMul.lean` →
`Universal` stack is an **in-flight upstreaming effort** rather than a project-private artifact. The
right question is therefore a policy/sequencing one for a human, not a self-resolving bucket: it
hinges on the upstreaming plan for the parent framework and on de-duplicating the NagellLutz/HasseWeil
forks first. Hence BORDERLINE.

If forced into a single bucket, the honest reading is **"YES, but only as part of the whole
`Universal` + EDS-`net` upstreaming"** — i.e. it travels with `smulX`, `smulY`, `smulX_add`,
`smulX_sub_sub_smulX_add`, `EllSequence.net`, `net_add_sub_iff`, and the universal-curve machinery,
as one coordinated contribution led by their author. The skill must not silently pick between
"YES-as-part-of-a-bundle" and "leave as project glue"; that is the human call below.

Numbered questions (≤5):
  1. Is the `WeierstrassCurve.Universal` framework (`Universal.Ring`/`Universal.Field`, `smulX`,
     `smulY`, `zsmul_point_eq_smulX_smulY`, `zsmul_eq_smulEval`) **already on a mathlib upstreaming
     track** (e.g. an open/planned PR by Junyan Xu)? If yes, this lemma simply rides along and no
     separate action is needed.
  2. Should `EllSequence.net` + `net_add_sub_iff` (currently project-local, the proof's backbone) be
     upstreamed into `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` **first**, as the
     natural home for the net relation, independent of the universal-curve layer?
  3. NagellLutz and HasseWeil carry **byte-identical** copies of this whole `smulX`/`smulY` track —
     should that be de-duplicated into a shared `Common/` (or upstreamed) before any mathlibing, so
     there is a single source of truth?
  4. Within an upstreamed `Universal` framework, is `smulY_add_sub_negY` wanted as a **named public
     lemma**, or should it be `private`/inlined into the `zsmul_point_eq_smulX_smulY` proof (its sole
     consumer), with only the headline `n • P` formula exposed?
  5. Is there appetite to first state the underlying content as a **field-level** lemma about
     `normEDS`/`IsEllSequence` coordinates (reusable beyond the universal curve), with the universal
     case as a corollary — or is the universal-only form the intended endpoint?

---

## Next step

User answers the questions above (chiefly Q1: is the `Universal` framework already being upstreamed
by its author?). If yes → no separate action; this lemma travels with that PR series. If no → file a
coordinated upstreaming plan for the `Universal` + EDS-`net` stack (de-duplicating the
NagellLutz/HasseWeil forks first), then re-run `/mathlibable` on the framework's headline results
rather than on this single glue lemma. Do **not** attempt to ship `smulY_add_sub_negY` standalone —
mathlib cannot yet express it.
