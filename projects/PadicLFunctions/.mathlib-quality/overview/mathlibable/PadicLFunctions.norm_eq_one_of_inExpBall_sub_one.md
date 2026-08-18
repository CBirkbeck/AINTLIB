# `/mathlibable` report — `PadicLFunctions.norm_eq_one_of_inExpBall_sub_one`

**Final verdict: `NO-composable-from-mathlib`.** The statement unfolds the
project-local `InExpBall` predicate and is a ≤3-call composition of mathlib's
ultrametric isosceles lemma `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`
together with `norm_one` + `max_eq_right` (the `‖y-1‖ < 1` premise itself coming
from the sibling project lemma `norm_lt_one_of_inExpBall`, which is in turn a
mathlib composition). It is the textbook "principal-unit norm" fact
`‖x‖ < 1 ⟹ ‖1 + x‖ = 1` — the `b = 1` specialisation of the **Krull sharpening**
of the strong triangle inequality — repackaged for the project's `InExpBall`
encoding. Mathlib ships every ingredient; it has no p-adic exp/log machinery for
the `InExpBall`-stated form to attach to. It should stay as project-local API,
derived inline from mathlib where needed — not proposed to mathlib on its own.

---

### Baseline (Phase 0)

- lake build:               build **not re-run** (stale/slow per task instruction); **reasoned from source** — the declaration and all dependencies read directly from `projects/PadicLFunctions/PadicLFunctions/ExtLog.lean` and `PadicExp.lean`, and the candidate mathlib lemmas read verbatim from `.lake/packages/mathlib/` (pinned rev `887d94632e78`, toolchain `v4.32.0-rc1`).
- decl `PadicLFunctions.norm_eq_one_of_inExpBall_sub_one`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ExtLog.lean:186`
- kind:                      theorem
- has sorry:                 no (file `ExtLog.lean` has 0 `sorry`/`admit`; the theorem body is a 4-line tactic proof)
- module docstring summary:  the extended (Iwasawa-branch) `p`-adic logarithm `extLog`, extending `padicLog` to the rational-valuation domain (RJW §6, decomposition cluster W6a; Washington §5.1).

---

### Statement (Phase 1)

`PadicLFunctions.norm_eq_one_of_inExpBall_sub_one` is **a theorem** stating the following:

> If a scalar `y` in an ultrametric normed field `L` lies in the *translated*
> exponential ball `1 + B` — encoded by the project predicate `InExpBall p (y − 1)`,
> namely `‖y − 1‖^(p−1) < p⁻¹`, which in particular forces `‖y − 1‖ < 1` — then
> `‖y‖ = 1`.

Mathematically: in a non-archimedean field, an element of the form `y = 1 + t`
with `‖t‖ < 1` is a **principal unit**, and principal units have norm exactly `1`.
This is the canonical consequence of the strong (ultrametric) triangle inequality:
since `‖t‖ < 1 = ‖1‖`, the two summands `t` and `1` have *different* norms, so the
"isosceles" sharpening gives `‖t + 1‖ = max(‖t‖, ‖1‖) = 1`. The hypothesis is
phrased through the project's exp-ball encoding (`‖y−1‖^(p−1) < p⁻¹`), which is
strictly stronger than `‖y−1‖ < 1`, but only `‖y−1‖ < 1` is actually used.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the residue prime. Used only via the sibling lemma `norm_lt_one_of_inExpBall` (which needs `p ≥ 2` to extract `‖y−1‖ < 1` from `InExpBall`); the equality `‖y‖ = 1` itself does not use `p` directly.
- `{L : Type*} [NormedField L] [IsUltrametricDist L]` — the ultrametric normed field carrying `y`. `IsUltrametricDist L` is the load-bearing instance (it supplies the isosceles lemma). The instances `[NormedAlgebra ℚ_[p] L]` and `[CompleteSpace L]` are explicitly `omit`-ted for this theorem.

Hypotheses (Lean side):
- `{y : L}` — the element under test.
- `(hy : InExpBall p (y - 1))` — i.e. `‖y − 1‖^(p−1) < (p : ℝ)⁻¹` (definitional unfolding of `InExpBall`); used only to obtain `‖y − 1‖ < 1`.

Conclusion (math): `‖y‖ = 1`.

Conclusion (Lean): `‖y‖ = 1`.

`InExpBall` is defined (in `PadicExp.lean:65`) as:
```lean
def InExpBall (p : ℕ) {L : Type*} [NormedField L] (x : L) : Prop :=
  ‖x‖ ^ (p - 1) < (p : ℝ)⁻¹
```
The current proof:
```lean
theorem norm_eq_one_of_inExpBall_sub_one {y : L} (hy : InExpBall p (y - 1)) :
    ‖y‖ = 1 := by
  have hlt := norm_lt_one_of_inExpBall p hy                       -- ‖y - 1‖ < 1
  have hne : ‖y - 1‖ ≠ ‖(1 : L)‖ := by rw [norm_one]; exact ne_of_lt hlt
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne   -- ‖(y-1)+1‖ = max ‖y-1‖ ‖1‖
  rwa [show y - 1 + 1 = y by ring, norm_one, max_eq_right hlt.le] at this
```
i.e. get `‖y−1‖ < 1` (sibling lemma), note `‖y−1‖ ≠ ‖1‖`, apply the ultrametric
isosceles lemma to `t = y−1`, `1`, then simplify `max ‖y−1‖ 1 = 1` via `max_eq_right`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper lemma — the elementary "principal units have norm 1" fact, stated
through the project's translated-exp-ball encoding. Not a new structure, not a named
theorem, not a `## Main results` entry (the file's main results are the `extLog`
construction and `extLogDomain_of_integral_norm_one`; this is one of its sub-lemmas,
labelled in-source as part of decomposition cluster W6a).

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded for the
report's framing only and did not gate which channels Phase 3 ran.)

### One-line check (Phase 2b)

n/a — kind is `theorem`, not `def`/`abbrev`/`structure`. (No one-liner exemption
analysis applies. The body is a 4-line tactic proof, but the one-line check only
governs definitions.)

---

### PHASE 3 — Literature search (EXHAUSTIVE protocol)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "ultrametric absolute value if \|x\| < 1 then \|1 + x\| = 1 non-archimedean norm" | **yes** | `\|x\| < 1 ⟹ \|1 + x\| = 1`, stated as a *consequence* of the ultrametric inequality + `\|1\| = 1` | Confirmed across multiple sources: Morin *BMST Intro to p-adic numbers* notes, Browning *Local Fields* (Bouyer notes), Kedlaya 18.787 *absolute-values*, Quick *p-adic absolute values* (UChicago REU 2020). Universally a textbook corollary, not a named standalone result. |
| 2 | WebSearch (general form) | "non-archimedean norm strong triangle inequality \|a + b\| = max(\|a\|,\|b\|) when \|a\| ≠ \|b\| isosceles" | **yes** | "If `\|λ\| ≠ \|μ\|` then `\|λ ± μ\| = max{\|λ\|, \|μ\|}`"; "every triangle in a non-Archimedean metric space is isosceles" | This is the maximally-general parent fact (the **Krull sharpening** / **isosceles triangle property**). The target lemma is its `μ = 1`, `\|λ\| < \|μ\|` specialisation. Sources: IAS *A Geometry in which all Triangles are Isosceles* (Resonance), Durham non-Archimedean Jørgensen notes, nLab `triangle+inequality`. |
| 3 | WebSearch (named-after / aliases — principal units) | "p-adic units norm one 1 + p Z_p principal units \|u\| = 1 valuation ring Washington cyclotomic fields" | **yes (context)** | elements `1 + t`, `‖t‖ < 1` are **principal units** (the group `1 + 𝔪`); all have norm 1; norm-one ⇔ unit of the valuation ring | Confirms the *name* of the objects: principal units / 1-units. Sources: arXiv 1907.06437 (p-adic log on principal units), arXiv math/0512015 (Iwasawa), Erickson *Cyclotomic Fields*, Washington (cited in-source, §5.1). The fact "principal units have norm 1" is folklore inside this theory. |
| 4 | ChatGPT MCP | (intended: "standard form of `‖1 + x‖ = 1` for `‖x‖ < 1` in a non-arch field; is it named; historical evolution from Krull's sharpening?") | n/a | — | **ChatGPT MCP is not configured in this environment** (no `chatgpt`/`openai` MCP tool surfaced via tool search). Substituted by the three WebSearch generality levels (#1–#3) + the verbatim Wikipedia read (#9), which already pin the standard form precisely. Recorded n/a-with-reason rather than skipped. |
| 5 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/` | n/a | (no references dir present in worktree) | Neither `.mathlib-quality/references/` nor `refs/` exists here. The module docstring already cites the math sources verbatim — **Washington, _Introduction to Cyclotomic Fields_, §5.1** (docstring on this very theorem) and RJW Thm 6.1(ii). In those texts "‖y‖ = 1 for `y` a 1-unit" is used silently. |
| 6 | nLab | `non-archimedean+field` (disambiguation), then `ultrametric+space` | partial | ultrametric page states the strengthened triangle inequality `max(d(x,y),d(y,z)) ≥ d(x,z)` | nLab `non-archimedean+field` is a disambiguation page (no math). nLab `ultrametric+space` states the strong inequality but **does not** spell out the equality/isosceles case. No named standalone result for our fact. |
| 7 | nCatLab (categorical) | — | n/a | — | Not a categorical concept; it is a one-line metric/valuation identity. No higher-categorical content. |
| 8 | Stacks Project | — | n/a | — | Not an algebraic-geometry concept; Stacks has no p-adic-exp/principal-unit-norm material framed this way. |
| 9 | Wikipedia / MathOverflow / MSE | "Ultrametric space" (Wikipedia), fetched verbatim | **yes (decisive)** | **Krull sharpening, quoted verbatim:** "‖x+y‖ ≤ max{‖x‖,‖y‖} **with equality if ‖x‖ ≠ ‖y‖**"; plus the isosceles property "at least one of `d(x,y)=d(y,z)` or `d(x,z)=d(y,z)` or `d(x,y)=d(z,x)` holds" | en.wikipedia.org/wiki/Ultrametric_space. This is the exact parent statement; the page even gives the proof of the equality-when-norms-differ case. The target lemma is the `y := 1` instance. |
| 10 | recent arXiv (last 5y) | "p-adic L-function Iwasawa branch logarithm exponential ball" / "p-adic logarithm principal units" | yes (context only) | — | Confirms the *ambient* RJW/Iwasawa-branch context (`log_p p = 0`, p-adic L-function work) but **no source states "1-units have norm 1" as a result** — it is universally an immediate step. arXiv 1907.06437 / math/0512015 use principal units freely. |

The protocol passed: WebSearch ran 3 distinct generality levels (the specific
`‖1+x‖=1` form #1, the general Krull/isosceles `‖a+b‖=max` form #2, the named-object
"principal units" aliasing #3); ChatGPT MCP recorded n/a-with-reason (tool absent)
and was compensated by an extra verbatim source read; local references recorded
n/a-with-reason (dir absent, in-source Washington §5.1 citation covers it); nLab
checked (strong inequality present, equality case not isolated); nCatLab / Stacks
recorded n/a-with-reason; Wikipedia gave the decisive verbatim parent statement; arXiv
checked for context.

### Literature summary (Phase 3)

Concept identified as: **"principal units (1-units) have norm 1"** — equivalently the
`b = 1`, `‖a‖ < ‖b‖` case of the **Krull sharpening** of the strong triangle
inequality (`‖a + b‖ = max(‖a‖, ‖b‖)` when `‖a‖ ≠ ‖b‖`), a.k.a. the **isosceles
triangle property** of ultrametric spaces.

Sources agree on the standard form: **yes.** Wikipedia states the Krull sharpening
verbatim; Morin/Browning/Kedlaya/Quick all state `‖x‖ < 1 ⟹ ‖1 + x‖ = 1` as an
immediate corollary; the cyclotomic-fields literature (Washington, Erickson, Iwasawa)
calls the `1 + 𝔪` elements *principal units* and uses their norm-one property freely.

Most general standard form: in **any** non-archimedean normed group/field,
`‖a‖ ≠ ‖b‖ ⟹ ‖a + b‖ = max(‖a‖, ‖b‖)`. Specialising `b = 1` (so `‖b‖ = 1`) and
`‖a‖ < 1` gives `‖a + 1‖ = 1`. The fact needs only ultrametricity + `‖1‖ = 1`; it is
agnostic to completeness, to the `ℚ_p`-algebra structure, and to `p` (the prime enters
only through the project's `InExpBall` premise being stronger than `‖y−1‖ < 1`).

Generality dimensions where the literature varies:
- Ambient object: `ℚ_p` / `ℂ_p` / a complete ultrametric extension `L` (classical texts) → mathlib phrases the parent fact at the level of an **ultrametric normed (additive) group** (`IsUltrametricDist`), strictly more general. The project's `[NormedField L] [IsUltrametricDist L]` is already at/near that level.
- Premise on the small part: `‖t‖ < 1` (literature) vs. the project's stronger `‖t‖^(p−1) < p⁻¹` (the `InExpBall` encoding). Only `‖t‖ < 1` is used, so the project premise is over-strong here — but that is forced by the calling context (the same `hy` is reused for log/exp facts), not a defect of this lemma.

Disagreement with the literature: **none.** The Lean form is a faithful, slightly
over-hypothesised (it asks for `InExpBall`, more than `‖y−1‖ < 1`) encoding of the
standard "1-units have norm 1" fact.

If-empty caveat: Phase 3 did **not** come back empty — it positively identified the
concept, found the exact parent statement verbatim (Wikipedia Krull sharpening), and
confirmed every source treats `‖1 + x‖ = 1` as an immediate corollary, never a named
standalone result. That is a strong signal toward a NO bucket.

---

### PHASE 4 — Generality analysis — `PadicLFunctions.norm_eq_one_of_inExpBall_sub_one`

Literature-standard form (from Phase 3): in an ultrametric normed group,
`‖a‖ ≠ ‖b‖ ⟹ ‖a + b‖ = max(‖a‖, ‖b‖)` (Krull sharpening / isosceles). The "1-unit"
corollary `‖t‖ < 1 ⟹ ‖1 + t‖ = 1` is the immediate `b = 1` specialisation.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `[NormedField L]` | normed field | ultrametric normed **(additive) group** — `‖1‖ = 1` is the only ring-flavoured fact used, and even that only to compute `‖1‖` | yes | The proof uses no multiplication and no field inverses — it is purely about `‖(y−1) + 1‖`. The parent mathlib lemma lives at `IsUltrametricDist` over a `SeminormedAddGroup`/`SeminormedAddCommGroup`. `NormedField` is far stronger than the equality needs. |
| 2 | `[IsUltrametricDist L]` | ultrametric | ultrametric (essential) | NO | The isosceles equality is *exactly* the ultrametric hypothesis; cannot be weakened. This is the load-bearing instance. |
| 3 | `[Fact p.Prime]` + `(hy : InExpBall p (y − 1))` = `‖y − 1‖^(p−1) < p⁻¹` | prime `p`, `(p−1)`-power premise | only need `‖y − 1‖ < 1` | yes (substantially) | Primality and the `(p−1)`-power/`p⁻¹`-bound encoding are far stronger than used; the proof extracts `‖y − 1‖ < 1` via `norm_lt_one_of_inExpBall` and discards the rest. The *literature-standard* premise is simply `‖y − 1‖ < 1`. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (it is the `NormedField`,
`InExpBall`-premised specialisation of the abstract ultrametric isosceles equality).

Number of weakening opportunities found: 2 substantive (`NormedField` → ultrametric
normed additive group with `‖1‖ = 1`; `InExpBall p (y−1)` premise → the literal
`‖y − 1‖ < 1`), plus the prime hypothesis being unused for the equality.

Proposed restatement: the *maximally general* statement —
`{x y : G} [SeminormedAddCommGroup G] [IsUltrametricDist G] (h : ‖x‖ ≠ ‖y‖) :
‖x + y‖ = max ‖x‖ ‖y‖` — **is already in mathlib** as
`IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm` (see Phase 5). So "restate the
project lemma more generally" is *not* the move: the general parent is an **existing**
mathlib lemma, and the target is a one-step specialisation of it. This pushes the
verdict toward **NO-composable-from-mathlib**, not toward YES-but-generalise-first.

Cost of restatement: n/a — the general form needs no work because mathlib already
ships it; the only "missing" object is the project-local `InExpBall`-stated wrapper,
which mathlib should not have.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preambles → typeclasses/instances? | no | — | Hypotheses are already type-class/instance form; nothing to bundle. |
| 2 | sequences/metric → filters/nets/topology? | no | — | A single norm equality; no limit/convergence content to filter-ise. |
| 3 | construct an object → universal-property class? | no | — | No object is constructed; it is a proposition. |
| 4 | set-with-closure-predicate → bundled substructure? | no (mildly relevant) | one *could* phrase via the open subgroup `IsUltrametricDist.ball_openSubgroup` / `closedBall_openSubgroup` (1-units = the unit ball as an open subgroup) | but that reframes, it doesn't generalise the equality; the equality itself is `norm_add_eq_max_of_norm_ne_norm`, already present. |
| 5 | field/metric-specific → weaken typeclass to module/semiring/group? | **yes** | the proof is an additive-group fact: `SeminormedAddCommGroup G` + `IsUltrametricDist G` (the parent `norm_add_eq_max_of_norm_ne_norm`) | but the weakened form **already exists in mathlib** — "use mathlib", not "contribute a modernisation". |
| 6 | 1-categorical → higher/∞-categorical? | no | — | No categorical content. |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive/ordered structure? | yes (the `(p−1)` exponent / `p⁻¹` bound, both inside the `InExpBall` premise) | replace the premise by the literal `‖y − 1‖ < 1` | this just *un-specialises the premise*; it does not yield a new mathlib lemma — the resulting statement is the `b=1` case of the existing `norm_add_eq_max_of_norm_ne_norm`. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no (as a contribution).** Rows 5 and 7 (and 4) identify a
strictly more general / more idiomatic form — but that form is **already shipped by
mathlib** as `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm` (the additive
`to_additive` of `norm_mul_eq_max_of_norm_ne_norm`). There is no modernisation for
*us* to contribute; the modern form is what we should *call*. One-line reason: the
abstraction target is an existing mathlib lemma, so "modernise and contribute"
collapses to "use mathlib" — a NO bucket, not YES-but-generalise-first.

---

### PHASE 4.5 — Diamond / defeq risk

n/a — declaration kind is `theorem`. (No definitional equalities or typeclass-search
paths are introduced; risk assessment is skipped per the skill's scope rule.)

---

### Mathlib search-status: `PadicLFunctions.norm_eq_one_of_inExpBall_sub_one`

[A] Lean-Finder — n/a: Lean-Finder MCP/web endpoint not available in this environment. Substituted by [D] grep over the pinned mathlib source (authoritative for rev `887d94632e78`, v4.32.0-rc1).
[B] Loogle — intended pattern queries `‖?x + ?y‖ = max ‖?x‖ ‖?y‖` and `name:norm_add_eq_max`; Loogle's web JSON endpoint does not accept these query shapes reliably through WebFetch in this environment. Fell back to [D].
[C] LeanSearch — n/a: `leansearch.net/api` not reachable as a usable API endpoint from this environment. Fell back to [D]/[E].
[D] Grep mathlib src — **HITS** (`grep -rn` over `.lake/packages/mathlib/Mathlib/`):
  - `IsUltrametricDist.norm_mul_eq_max_of_norm_ne_norm {x y : S} (h : ‖x‖ ≠ ‖y‖) : ‖x * y‖ = max ‖x‖ ‖y‖` — `Mathlib/Analysis/Normed/Group/Ultra.lean:96`, carrying `@[to_additive /-- All triangles are isosceles in an ultrametric normed additive group. -/]`. **The `to_additive`-generated `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm` is exactly the parent fact**, and is precisely the lemma the existing proof calls (`IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne`).
  - Supporting `norm_one` (for `‖1‖ = 1`) and `max_eq_right : a ≤ b → max a b = b` (`Mathlib/Order/`) — both standard, used by the existing proof.
  - Near-misses that are **not** what we want: `norm_add_eq_max` (`Mathlib/Topology/ContinuousMap/Compact.lean:359`, `…/Bounded/Normed.lean:311`, `…/CStarAlgebra/GelfandDuality.lean`) all require `f * g = 0` (orthogonality), a different hypothesis; `norm_add_one_le_max_norm_one` (`Mathlib/Analysis/Normed/Ring/Ultra.lean:50`) is the *inequality* `‖x + 1‖ ≤ max ‖x‖ 1`, not the equality.
[E] Name pattern — grep `norm_eq_one*`, `*eq_one_of_norm*`, `*expBall*`, `principal*unit*`, `padicExp`, `padicLog` across mathlib:
  - **No lemma of the form "`‖x‖ < 1 → ‖1 + x‖ = 1`" or "`‖y − 1‖ < 1 → ‖y‖ = 1`" exists in mathlib** — the equality `eq_one` conclusion is nowhere stated as a standalone lemma; only the `_eq_max_of_norm_ne_norm` parent and the `_le_max` inequalities exist.
  - The `norm_eq_one` hits in mathlib are about `ℤ_[p]` units (`PadicInt.norm_units`, `PadicInt.isUnit_iff : IsUnit z ↔ ‖z‖ = 1`, `PadicInt.norm_eq_one_iff_*` coprimality) — **a different statement** (characterising units of `ℤ_[p]` by norm one, not deriving norm one from `‖y−1‖ < 1` in a general ultrametric `L`).
  - Crucially, **mathlib contains NO `padicExp`, NO `padicLog`, NO `InExpBall`, and no p-adic exponential/logarithm/exp-ball machinery whatsoever** (the entire `PadicExp.lean`/`ExtLog.lean` development is novel-to-mathlib).

Searched for both:
  - the user's current form (`InExpBall p (y − 1) → ‖y‖ = 1`): **not in mathlib** — `InExpBall` is a project-local `def`, so no mathlib lemma can be about it.
  - the literature-standard / abstract form (`‖x‖ ≠ ‖y‖ → ‖x + y‖ = max ‖x‖ ‖y‖`): **found in mathlib** as `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm` (the parent; our statement is its `b = 1`, `‖a‖ < 1` specialisation).

Concluded: **found the building blocks** — mathlib has `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm` (the isosceles equality) + `norm_one` + `max_eq_right`; composition yields our form (the `‖y−1‖ < 1` premise coming from the sibling project lemma `norm_lt_one_of_inExpBall`, itself a mathlib composition). The *exact* form is absent from mathlib only because it mentions the project-local `InExpBall` and because no source bothers to package the `‖1+x‖=1` corollary as its own lemma. There is no p-adic-exp content in mathlib for the user's form to coincide with.

---

### Call sites — `PadicLFunctions.norm_eq_one_of_inExpBall_sub_one`

Internal use count: **0** (within the project, NOT counting the declaring file `ExtLog.lean`).
External-to-file callers: **0 distinct files.**

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| ExtLog.lean:308 (declaring file) | `have hny : ‖y‖ = 1 := norm_eq_one_of_inExpBall_sub_one p hy` — inside `extLog_witness_smul_eq` |
| ExtLog.lean:309 (declaring file) | `have hny' : ‖y'‖ = 1 := norm_eq_one_of_inExpBall_sub_one p hy'` — inside `extLog_witness_smul_eq` |

Both uses are **inside the declaring file** (`ExtLog.lean`), within the single lemma
`extLog_witness_smul_eq` (well-definedness of `extLog`), where they establish `‖y‖ = 1`
and `‖y'‖ = 1` for two witness elements so the `p`-valuations can be matched. Repo-wide
grep (`grep -rn "norm_eq_one_of_inExpBall_sub_one" projects/ --include="*.lean"`) finds
no occurrence outside `ExtLog.lean`. So the Phase-6.0 "internal use count" (which
excludes the declaring file) is **0**, and external-to-file callers is **0**.

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?):
  - Elsewhere in the project, norm-one facts for ultrametric units are obtained by *other* routes: `extLog_witness_smul_eq` later uses `norm_natCast_p` for `‖p‖`; `ResidueZeta.lean` and `ValuesAtOne.lean` compute `‖z‖ = 1` for angle-units / roots of unity from `IsPrimitiveRoot`/integrality facts (a different hypothesis chain, not `‖z−1‖ < 1`). No site re-derives the bare `‖y−1‖ < 1 ⟹ ‖y‖ = 1` implication by hand. The two in-file uses are the only consumers.

**Composability signal (per the call-sites table):** K = 0 *project-internal* uses
(the only two consumers are in the declaring file, in one lemma). This is the
K=0/within-file convenience-wrapper pattern — exactly the case that leans toward
NO-composable-from-mathlib: it has no external consumers that would argue for shipping
it, and it is a ≤3-call mathlib composition on the project-local predicate.

---

### Composition check (Phase 6)

Can `norm_eq_one_of_inExpBall_sub_one` be derived from mathlib in ≤3 chained calls?

Attempt 1 (the existing proof, given `‖y − 1‖ < 1`):
```lean
example {y : L} (hlt : ‖y - 1‖ < 1) : ‖y‖ = 1 := by
  have hne : ‖y - 1‖ ≠ ‖(1 : L)‖ := by rw [norm_one]; exact ne_of_lt hlt
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne   -- ‖(y-1)+1‖ = max ‖y-1‖ ‖1‖
  rwa [show y - 1 + 1 = y by ring, norm_one, max_eq_right hlt.le] at this
```
  - Mathlib decls used: `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm` (the isosceles equality), `norm_one`, `max_eq_right` (+ a `ring` rewrite `y − 1 + 1 = y`).
  - Result: **succeeds.** The single substantive mathlib call is the isosceles lemma; `norm_one` + `max_eq_right` are the trivial `max ‖y−1‖ 1 = 1` simplification. This matches the Phase-6 composable patterns ("one function call" + a `rw`/`max` simplification), **not** the "multiple `have`s with non-trivial reasoning between" non-composable pattern.

Attempt 2 (fold in the `‖y − 1‖ < 1` extraction, so the whole thing is mathlib + the project def):
  - The premise `‖y − 1‖ < 1` is supplied by the sibling lemma `norm_lt_one_of_inExpBall p hy`, which is *itself* a ≤3-call mathlib composition (`pow_lt_one_iff_of_nonneg` + `inv_le_one_of_one_le₀` + `norm_nonneg`; see the sibling report `PadicLFunctions.norm_lt_one_of_inExpBall.md`, verdict `NO-composable-from-mathlib`). Inlined, the full derivation from `InExpBall p (y−1)` to `‖y‖ = 1` is still a small composition of existing mathlib lemmas around the project-local `InExpBall` unfold — no new mathematical idea, no automation chain.
  - Result: **succeeds** (modulo the `InExpBall` premise being project-local).

Conclusion: **COMPOSABLE** (the core equality is a 1-substantive-call composition of
`IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm` with a trivial `max` simplification;
the `‖y−1‖ < 1` premise is a further mathlib composition). It is not a proof in disguise.

---

## Verdict: `PadicLFunctions.norm_eq_one_of_inExpBall_sub_one`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the concept is "principal units (1-units) have norm 1", the `b = 1` specialisation of the **Krull sharpening** `‖a + b‖ = max(‖a‖,‖b‖)` for `‖a‖ ≠ ‖b‖` (quoted verbatim from Wikipedia "Ultrametric space"; corroborated by Morin/Browning/Kedlaya/Quick and the cyclotomic-fields principal-unit literature). Treated everywhere as an immediate corollary, never a named standalone lemma.
- Generality analysis (Phase 4): STRICTLY NARROWER than the abstract ultrametric isosceles equality — but that general form is an **existing** mathlib lemma (`IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`), so this is "use mathlib", not "generalise-and-contribute". Modern-idiom check confirms no modernisation for us to add.
- Mathlib search (Phase 5): found the building blocks — `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm` (`Mathlib/Analysis/Normed/Group/Ultra.lean:96`, via `to_additive`) + `norm_one` + `max_eq_right`. Mathlib has **no** `eq_one`-conclusion lemma of this shape and **no** p-adic exp/log machinery, so the user's `InExpBall`-stated form cannot exist there.
- Composition check (Phase 6): COMPOSABLE — one substantive mathlib call (the isosceles equality) plus a trivial `max ‖y−1‖ 1 = 1` simplification; the `‖y−1‖ < 1` premise is itself a further mathlib composition.

**Rationale:**

The statement is the classical "1-units have norm 1" fact: in an ultrametric field,
`y = 1 + t` with `‖t‖ < 1` satisfies `‖y‖ = 1`. Its mathematical content is *exactly*
the `b = 1` case of mathlib's `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`
(`‖a‖ ≠ ‖b‖ ⟹ ‖a + b‖ = max ‖a‖ ‖b‖`, the "all triangles are isosceles" sharpening,
which the existing proof literally calls): take `a = y − 1`, `b = 1`; since
`‖y − 1‖ < 1 = ‖1‖` the norms differ, so `‖(y−1) + 1‖ = max(‖y−1‖, 1) = 1`. Mathlib
already ships the isosceles equality and the trivial `max` simplification, so the lemma
adds no new mathematical content and is a ≤3-call composition. It therefore does not
belong in mathlib **as a standalone lemma** — and it could not be added "as is" in any
case, because its statement mentions the *project-local* predicate `InExpBall`, which
mathlib does not have (mathlib has no `padicExp`/`padicLog`/exp-ball machinery at all,
and no `eq_one`-form of the 1-unit fact). The literature reinforces this: Wikipedia and
the standard p-adic texts state the Krull/isosceles parent and treat `‖1 + x‖ = 1` as an
immediate corollary, never elevating it to a named result — a textbook signal that this
is wrapper-grade, not contribution-grade.

This is, however, a *reasonable project-local convenience lemma*: it names the
"1-unit ⟹ norm one" step that `extLog`'s well-definedness proof (`extLog_witness_smul_eq`)
relies on to match `p`-valuations of two witnesses. The verdict is about
mathlib-worthiness, not about whether to keep it in the project — it should **stay in
the project**, deriving `‖y − 1‖ < 1` from `InExpBall` and calling
`IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`; it just should not be proposed to
mathlib on its own. (If one wanted a *mathlib-shaped* contribution at all, the only
candidate would be a general `‖x‖ < 1 → ‖1 + x‖ = 1` corollary stated over
`[SeminormedAddCommGroup G] [IsUltrametricDist G]` with `‖1‖ = 1` — but that is a one-line
specialisation of an existing lemma and, per Phase 3, the community has consistently
declined to name it; proposing it would be a borderline micro-lemma at best, and is *not*
what this `InExpBall`-premised project lemma is.)

**WHY not (refactor-actionable detail):**

Mathlib has the building blocks; the user's form is a ≤3-call composition wrapping a
project-local definition.

Mathlib building blocks:
- `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm` — `.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Ultra.lean:96` (the `to_additive` of `norm_mul_eq_max_of_norm_ne_norm`) — `{x y : G} (h : ‖x‖ ≠ ‖y‖) : ‖x + y‖ = max ‖x‖ ‖y‖`.
- `norm_one` — supplies `‖(1 : L)‖ = 1`.
- `max_eq_right` — `.lake/packages/mathlib/Mathlib/Order/...` — `(h : a ≤ b) : max a b = b`, simplifies `max ‖y − 1‖ 1 = 1`.
- (premise) `norm_lt_one_of_inExpBall` — project lemma at `ExtLog.lean:38`, itself `NO-composable-from-mathlib` (= `pow_lt_one_iff_of_nonneg` + `inv_le_one_of_one_le₀` + `norm_nonneg`), supplies `‖y − 1‖ < 1`.

Composition sketch (≤3 lines, given `‖y − 1‖ < 1`):
```lean
example {y : L} (hlt : ‖y - 1‖ < 1) : ‖y‖ = 1 := by
  have hne : ‖y - 1‖ ≠ ‖(1 : L)‖ := by rw [norm_one]; exact ne_of_lt hlt
  have h := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
  rwa [show y - 1 + 1 = y by ring, norm_one, max_eq_right hlt.le] at h
```

Call sites in our project (from Phase 6.0): **0 outside the declaring file** (2 uses,
both inside `ExtLog.lean`, in the single lemma `extLog_witness_smul_eq`: lines 308, 309).

Refactor plan: **mathlib-worthiness only — no project deletion recommended.** Because
mathlib has no `InExpBall` and the two consumers are tightly local (one lemma, same
file), the pragmatic action is to **keep `norm_eq_one_of_inExpBall_sub_one` as
project-local API** and *not* open a mathlib PR for it. If a maintainer nonetheless
wants to remove the named wrapper, the mechanical refactor is: at each of the 2 in-file
sites (`ExtLog.lean:308`, `ExtLog.lean:309`) inline the composition above — replace
`norm_eq_one_of_inExpBall_sub_one p hy` (resp. `… p hy'`) with the term
`by have hlt := norm_lt_one_of_inExpBall p hy; <the 3-line block above>`. Verify the
`InExpBall` argument unfolds (it does — the def is semireducible and the existing proof
already feeds `hy` straight into `norm_lt_one_of_inExpBall`). **Recommendation: do NOT
inline** — the named lemma improves local readability and documents the "1-unit" step;
the only "cost" is one extra declaration. The actionable conclusion is simply *"not a
mathlib contribution."*

Next action: **do not propose `norm_eq_one_of_inExpBall_sub_one` to mathlib.** Keep it
project-local. (No `/generalise` or mathlib-PR follow-up is warranted: the general fact
already exists in mathlib as `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`, and the
literature has consistently declined to name the `‖1 + x‖ = 1` corollary on its own.)

---

## Next step

Do not propose `norm_eq_one_of_inExpBall_sub_one` to mathlib — it is the classical
"principal units have norm 1" fact, a ≤3-call composition of
`IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm` + `norm_one` + `max_eq_right`
(with `‖y − 1‖ < 1` from the sibling `norm_lt_one_of_inExpBall`), wrapping the
project-local `InExpBall` predicate, and mathlib has no p-adic-exp machinery nor any
`eq_one`-form of this fact for it to attach to. Keep it as project-local convenience API
(its 2 consumers are both inside `ExtLog.lean`, in `extLog_witness_smul_eq`); if ever
desired, inline the 3-line composition at those two sites. No `/generalise` follow-up is
needed because mathlib already ships the general isosceles equality.
