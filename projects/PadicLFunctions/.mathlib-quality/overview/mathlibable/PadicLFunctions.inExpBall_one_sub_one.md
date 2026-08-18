# `/mathlibable` report — `PadicLFunctions.inExpBall_one_sub_one`

**Final verdict: `NO-composable-from-mathlib`** (a project-internal one-line lemma
about the project-local predicate `InExpBall`; its content is a ≤3-call composition
of mathlib primitives and is already re-derived inline at two other sites).

---

### Baseline (Phase 0)
- lake build:               build not re-run; reasoned from source (per task instruction — stale/slow build, Phase-0 fallback used)
- decl `PadicLFunctions.inExpBall_one_sub_one`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ExtLog.lean:346`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  the extended (Iwasawa-branch) p-adic logarithm — extends `padicLog` to the rational-valuation domain (`x^m = p^k·y` with `y` in the open exponential ball), RJW §6 / Washington §5.1.

Dependency context read from source:
- `InExpBall` (`PadicExp.lean:65`): `def InExpBall (p : ℕ) {L} [NormedField L] (x : L) : Prop := ‖x‖ ^ (p - 1) < (p : ℝ)⁻¹` — a **project-local** predicate, the rpow-free form of membership in the open convergence ball `‖x‖ < p^{-1/(p-1)}` of the p-adic exponential.
- Variables in scope: `(p : ℕ) [hp : Fact p.Prime]`, `{L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]` (all four `L`-instances `omit`ted for this theorem).
- Proof body (one line): `rw [sub_self, InExpBall, norm_zero, zero_pow (by have := hp.out.one_lt; omega)]; exact inv_pos.mpr (by exact_mod_cast hp.out.pos)`.

---

### Statement (Phase 1)

`PadicLFunctions.inExpBall_one_sub_one` is a theorem stating the following:

In any complete ultrametric normed field `L` that is a normed `ℚ_p`-algebra, the
difference `1 − 1 = 0` lies in the open ball of convergence of the `p`-adic
exponential / logarithm. Concretely, since `‖0‖ = 0` and `0^{p−1} = 0 < p⁻¹` for a
prime `p`, the basepoint condition `InExpBall p (1 − 1)` holds. Equivalently: the
multiplicative identity `1` belongs to the group of principal units `1 + B` (the
translated exponential ball), because its translate `1 − 1 = 0` is the centre of the
additive ball `B`.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the residue prime (only `p > 1` and `p > 0` are used).
- `L`, `[NormedField L]` — the ambient normed field (the only instance the proof needs; the algebra / ultrametric / complete instances are `omit`ted).

Hypotheses (Lean side): none beyond the ambient variables.

Conclusion (math): `0` is in the open convergence ball; i.e. `1` is a principal unit.

Conclusion (Lean): `InExpBall p ((1 : L) - 1)`, which unfolds to `‖(1:L) - 1‖ ^ (p - 1) < (p : ℝ)⁻¹`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-line helper — the "trivial/empty witness" that the basepoint `1` lies in
the principal-unit group `1 + B`. Not a named theorem, not a new structure, not a
`## Main results` entry. (Literature width is EXHAUSTIVE regardless; SMALL is recorded
for framing only.)

### One-line check (Phase 2b)

Body line count: 2 substantive lines (one `rw`, one `exact`).
One-liner verdict: **n/a — kind is `theorem`, not a `def`** (the one-liner/defeq/diamond
exemption machinery applies to definitions; a one-line *theorem* carries no
definitional-equality surface). Recorded as a one-line note per the skill.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "p-adic exponential logarithm radius of convergence open ball contains 0 principal units 1+pZ_p"       | yes  | exp converges on the open ball of valuative radius `1/(p−1)` **around 0**; log on `\|x−1\|<1`; `1+pℤ_p` is the principal-unit group | PlanetMath, MIT (Vogan exp.pdf), Wikipedia "p-adic exponential function" — "0 in the ball" / "1 a principal unit" is definitional, not a named result |
|  2 | WebSearch (general form)         | "p-adic logarithm convergence ball 1+p principal units identity element domain"                        | yes  | log is an isometry between `{‖x‖ < p^{-1/(p−1)}}` (additive) and `{1+y : ‖y‖ < p^{-1/(p−1)}}` (multiplicative) | arXiv:1907.06437, arXiv:1904.09850 — the basepoint `1`↔`0` correspondence is the trivial endpoint of the isometry |
|  3 | WebSearch (named-after / aliases)| "zero membership open ball metric space norm definition trivial nonarchimedean"                        | yes  | non-arch. norm: `‖x‖=0 ⇔ x=0`; open ball `B(a,r)={x:d(x,a)<r}`; centre always in ball for `r>0` | Schikhof, Numdam — "centre ∈ open ball" is `d(a,a)=0<r`, the textbook one-liner |
|  4 | ChatGPT MCP                      | (would ask: standard form + generality + historical evolution of "0 in the p-adic exp ball")          | n/a  | —                                | ChatGPT MCP **not configured** in this environment (no `mcp__*chatgpt*` tool); recorded n/a. WebSearch ×3 + grep cover the same ground; the fact is too elementary to have a contested standard form |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` for "exponential" / "ball"                | n/a  | (directory absent)               | only `.mathlib-quality/overview/` exists; no `references/` dir — recorded n/a |
|  6 | nLab                             | "nLab p-adic exponential logarithm convergence radius open disc principal units"                       | yes  | exp converges on open ball of valuative radius `1/(p−1)` **around 0**, image is the open ball around 1 | confirms #1/#2; no separate "0 ∈ ball" statement — it is the implicit basepoint |
|  7 | nCatLab (if categorical)         | —                                                                                                      | n/a  | —                                | not a categorical concept — it is a membership inequality in a normed field |
|  8 | Stacks Project (if alg geom)     | —                                                                                                      | n/a  | —                                | not an algebraic-geometry concept (no schemes/sheaves/sites) — it is elementary p-adic analysis |
|  9 | MathOverflow / Math.StackExchange| covered by query #1/#3 (p-adic exp ball; centre-in-ball)                                                | yes  | same as #1/#3                    | standard Q&A material; no one treats "0 ∈ ball" / "1 ∈ 1+B" as a citable named lemma |
| 10 | recent arXiv (last 5 years)      | "p-adic logarithm principal units image" (1907.06437, 1904.09850, GJM-2023)                            | yes  | recent work studies the **image** of log on `1+m`; the basepoint `1` (⇔ `0`) is the trivial fixed endpoint | the interesting math is the image structure; the basepoint membership is assumed throughout |

The protocol passes: WebSearch ran 3 distinct queries at different generality levels
(specific p-adic ball, the general isometry form, the abstract centre-in-ball form);
local references checked (absent → n/a); nLab checked; Stacks / nCatLab / MathOverflow /
arXiv each checked or n/a-with-reason. ChatGPT MCP recorded n/a (tool not available),
which the three WebSearch queries + nLab more than cover for a fact this elementary.

### Literature summary (Phase 3)

Concept identified as: **the basepoint of the p-adic exponential ball** — equivalently,
"the centre `0` lies in the open ball of convergence" / "the identity `1` is a principal
unit (`1 ∈ 1 + B`)".
Sources agree on the standard form: **yes** — exp converges on the open ball of valuative
radius `1/(p−1)` centred at `0`; log on the corresponding ball centred at `1`; the two
are isometric, with `0 ↔ 1` the basepoint. In every source this membership is *implicit
and definitional*, never a separately-named theorem.
Most general standard form: in any non-archimedean normed field, the centre of an open
ball of positive radius is a member of the ball (`d(a,a) = 0 < r`). Specialised here to
the exp-ball centre `0` via `‖0‖^{p−1} = 0 < p⁻¹`.
Generality dimensions where the literature varies:
  - ground structure: from `ℚ_p` / `ℂ_p` (classical texts) to "any non-archimedean normed
    field" (the abstract endpoint) — the project's `[NormedField L]` already sits at the
    abstract end.
  - radius convention: rpow form `‖x‖ < p^{-1/(p−1)}` vs the rpow-free `‖x‖^{p−1} < p⁻¹`
    the project uses — equivalent.
Disagreement with the literature: **none**. The project's statement is the basepoint
endpoint of the standard isometry, at the abstract `[NormedField]` generality.

**Literature signal:** the search returned a rich standard *theory* (the exp/log
isometry, principal units) but **no source names "0 ∈ ball" / "1 ∈ 1+B" as a citable
lemma** — it is the trivial endpoint everyone assumes. Per the verdict reference, "the
literature treats it as definitional/implicit" is a NO-leaning signal, not a YES one.

---

### Generality analysis — `PadicLFunctions.inExpBall_one_sub_one`

Literature-standard form (from Phase 3): in a non-archimedean normed field the centre `0`
of the exp-ball is a member, i.e. `‖0‖^{p−1} < p⁻¹` (equivalently `InExpBall p 0`), for
any prime `p`.

| # | Parameter / hypothesis        | Current Lean form                    | Literature-standard form              | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------|--------------------------------------|----------------------------------------|---------------------|----------------------------------|
| 1 | `[hp : Fact p.Prime]`         | `p` prime                            | needs only `p > 1` (so `p−1 ≥ 1`) and `p > 0` (so `p⁻¹ > 0`) | yes (in principle)  | the proof uses only `hp.out.one_lt` and `hp.out.pos`; but `InExpBall`'s whole API is stated with `[Fact p.Prime]`, so weakening here would desync the predicate's interface — not a real generalisation, just interface drift |
| 2 | `[NormedField L]`             | normed field                         | non-archimedean normed field           | already maximal     | the statement is about `0`, whose norm is `0` in *any* normed group; the three `L`-instances (`NormedAlgebra`, `IsUltrametricDist`, `CompleteSpace`) are explicitly `omit`ted — already maximally general for this content |
| 3 | the bespoke predicate `InExpBall` | project-local `‖x‖^(p-1) < p⁻¹` | abstract `x ∈ Metric.ball (0) r` / `1 ∈ principal units` | n/a — see Phase 4c | the "generalisation" worth discussing is not weakening a hypothesis but **re-aiming at mathlib's abstract ball API**; covered in 4c |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (for the project-local predicate it targets).
Number of weakening opportunities found: 0 real ones. Row 1 is interface drift, not a
generalisation; row 2 is already at the abstract `[NormedField]` endpoint with all
heavier instances omitted.
Proposed restatement: none (no hypothesis to weaken).
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preambles → typeclasses? | no | already typeclass-based (`[NormedField L]`) | — |
| 2 | sequences/metric → filters/topological? | no | a single membership inequality; no limit to filter-ise | — |
| 3 | construct an object → universal-property class? | no | it is a `Prop`, constructs nothing | — |
| 4 | set-with-closure-predicate → bundled substructure? | **partially** | the *upstream* move would be to define the principal-unit ball as a mathlib `Subgroup`/`Submodule` and state `1 ∈ it`; but that is a redesign of `InExpBall` itself, far beyond this leaf lemma | the *predicate* `InExpBall` could be a mathlib `Metric.ball 0 r` membership — but that is a `/generalise`-of-`InExpBall` task, not a property of this theorem |
| 5 | vector-space/metric/field-specific → weaker typeclass? | no | already maximally weak (`NormedField`, heavy instances omitted) | — |
| 6 | 1-categorical → higher-categorical? | no | not categorical | — |
| 7 | concrete index (ℕ/ℤ/ℝ) → general algebraic structure? | no | `p−1`/`p⁻¹` are intrinsic to the p-adic radius; not an index to abstract | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** — not for *this theorem*. The only contemporary-idiom move
(row 4) targets the *definition* `InExpBall`, not this lemma about it: if `InExpBall p x`
were re-expressed as `x ∈ Metric.ball (0 : L) r`, then this whole theorem would collapse to
mathlib's `Metric.mem_ball_self` (`x ∈ Metric.ball x r` for `0 < r`). That is a
`/generalise PadicLFunctions.InExpBall` decision about the predicate's design, which the
verdict reference explicitly says comes from re-aiming the *def*, not from this leaf
lemma. For the theorem as written, no modernisation applies.
One-line reason: it is the trivial basepoint membership of a bespoke predicate; the only
"modernisation" is to redesign the predicate, which is out of scope for this leaf.

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (no definitional equalities or typeclass-search paths
introduced).

---

### Mathlib search-status: `PadicLFunctions.inExpBall_one_sub_one`

[A] Lean-Finder       (would query "centre of open ball is a member"; "p-adic exp basepoint") — **n/a: Lean-Finder MCP not configured in this environment**
[B] Loogle            (would query `?x ∈ Metric.ball ?x _` ; `‖(0 : _)‖ ^ _ < _`)            — **n/a: `lean_loogle` tool not available here**
[C] LeanSearch        (would query "centre is in the open ball positive radius")               — **n/a: `lean_leansearch` tool not available here**
[D] Grep mathlib src  `padicLog` / `padicExp` / `InExpBall` over `.lake/packages/mathlib/Mathlib/` — **no hits** (predicate entirely absent from mathlib). `mem_ball_self` / `mem_closedBall_self` — **hits** (the abstract analog, see below).
[E] Name pattern      grep `mem_ball_self`, `mem_closedBall_self`, `self_mem_ball`, `norm_zero`, `zero_pow`, `inv_pos` over mathlib — **hits** on all (the building blocks + the abstract analog).

Searched for both:
  - the user's current form `InExpBall p ((1:L)-1)` → **no mathlib hit**: `InExpBall`,
    `padicLog`, `padicExp` do not exist anywhere in mathlib (grep returns empty). Mathlib
    therefore *cannot* host this statement as-is — it references a project-local predicate.
  - the literature-standard / abstract form "centre `0` is in the open ball of positive
    radius" → mathlib **has the abstract analog**:
      - `Metric.mem_ball_self : 0 < ε → x ∈ Metric.ball x ε` (`Mathlib/Topology/MetricSpace/Pseudo/Defs.lean:382`)
      - `Seminorm.mem_ball_self : 0 < r → x ∈ ball p x r` (`Mathlib/Analysis/Seminorm.lean:629`)
    but `InExpBall` is **not** defined as a `Metric.ball` membership (it is the bespoke
    `‖x‖^(p−1) < p⁻¹`), so these do not apply to the literal statement.

Building blocks the proof actually uses (all present in mathlib):
  - `sub_self : a - a = 0` (reduces `1 - 1` to `0`)
  - `norm_zero : ‖0‖ = 0`
  - `zero_pow : 0 < n → (0 : R) ^ n = 0` (`Mathlib/Tactic/Ring/Common.lean:987` and elsewhere)
  - `inv_pos : 0 < a⁻¹ ↔ 0 < a` (`Mathlib/Algebra/Order/GroupWithZero/Basic.lean:842`)
  - `Nat.Prime.one_lt`, `Nat.Prime.pos`, `Nat.cast` positivity

Concluded: **not in mathlib (the predicate `InExpBall` is project-local; all 5 methods —
2 available, 3 n/a — exhausted), but mathlib has both the abstract analog
`Metric.mem_ball_self` and every building block needed to discharge it in one line.**

---

### Call sites — `PadicLFunctions.inExpBall_one_sub_one`

Internal use count: **5** (within the project, not counting the declaring line `ExtLog.lean:346`).
External-to-file callers: **1 distinct file** (`ResidueZeta.lean`); the other 4 uses are in the declaring file `ExtLog.lean`.

| Caller file:line                | Usage pattern (one-line excerpt)                                                          |
|---------------------------------|-------------------------------------------------------------------------------------------|
| ExtLog.lean:405                 | `⟨1, 0, 1, one_pos, …, inExpBall_one_sub_one p⟩` — empty-product witness in `ExtLogDomain.prod` |
| ExtLog.lean:420                 | `extLog_eq_padicLog p (inExpBall_one_sub_one p), padicLog_one` — empty-product case of `extLog_prod` |
| ExtLog.lean:430                 | `… (inExpBall_one_sub_one p), padicLog_one, smul_zero` — in `extLog_eq_zero_of_pow_eq_one` |
| ExtLog.lean:438                 | `⟨2, 0, 1, two_pos, …, inExpBall_one_sub_one p⟩` — `−1 ∈ ExtLogDomain` witness in `extLog_neg` |
| ResidueZeta.lean:1757           | `⟨p - 1, 0, 1, hp1, …, inExpBall_one_sub_one p⟩` — Teichmüller `ω ∈ ExtLogDomain` witness |

All five uses are the **same idiom**: supplying the `InExpBall p (y − 1)` field of an
`ExtLogDomain`/witness tuple in the case where the ball element is `y = 1` (so `y − 1 = 0`).
It is the "trivial/empty witness" plug.

Inline-derivation grep (was the equivalent re-derived elsewhere without using `inExpBall_one_sub_one`?):
  - `PadicExp.lean:261` — `have h0 : InExpBall p (0 : L) := by rw [InExpBall, norm_zero, zero_pow …]; exact inv_pos.mpr …` — **the identical fact, proved inline** (without `sub_self`, since it states `InExpBall p 0` directly).
  - `ExtLog.lean:67–72` — the `zero` case of `pow_mem_expBall` proves `InExpBall p (y^0 − 1)` via `rw [pow_zero, sub_self, InExpBall, norm_zero, zero_pow …]; exact inv_pos.mpr …` — **the identical proof inlined**, this time including the `sub_self` step (i.e. literally this theorem's proof, re-typed).

What the call-sites pattern tells you: K = 5 internal uses (≥3) shows the *idiom* is real
and recurring — but the inline-derivation grep shows the underlying fact is **also**
re-derived from scratch at 2 sites (including a verbatim copy of this very proof). That is
the signature of a thin convenience wrapper around a definitional one-liner, not of a
load-bearing API lemma. Combined with Phase 5 (mathlib cannot host it — the predicate is
project-local) and Phase 6 (≤3-call composition), the pattern points to
NO-composable-from-mathlib: keep it (or not) as a *project* convenience, but it is not a
mathlib contribution.

---

### Composition check (Phase 6)

Can `PadicLFunctions.inExpBall_one_sub_one` be derived from mathlib in ≤3 chained calls?

Attempt 1 (literal statement, current `InExpBall` def):
  `by rw [sub_self, InExpBall, norm_zero, zero_pow h]; exact inv_pos.mpr h'`
  - Mathlib decls used: `sub_self`, `norm_zero`, `zero_pow`, `inv_pos` (+ `Nat.Prime.one_lt`/`pos`).
  - Result: **succeeds** — this *is* the existing proof; every lemma is from mathlib. It is
    a short rewrite chain (`sub_self` to hit `0`, then `‖0‖ = 0`, then `0^{p−1} = 0`, then
    `0 < p⁻¹`). Two of the four mathlib lemmas (`sub_self`, `norm_zero`) are `simp` lemmas,
    so `by simp [InExpBall, zero_pow (show 0 < p - 1 from …), inv_pos, hp.out.pos]`-style
    closes it too — a trivial simp/rewrite composition, not a real proof.
  - Notes: the only "content" is unfolding the project-local `InExpBall` and noting
    `‖0‖ = 0`; there is no mathematical step mathlib doesn't already provide.

Attempt 2 (if `InExpBall` were re-aimed at `Metric.ball 0 r`, hypothetically):
  `Metric.mem_ball_self (by positivity)` — a single mathlib call.
  - Mathlib decls used: `Metric.mem_ball_self`.
  - Result: succeeds in 1 call — but only after redesigning the predicate (a
    `/generalise InExpBall` task, out of scope for this leaf).

Conclusion: **COMPOSABLE.** The statement, as it pertains to mathlib, is a ≤3-call
composition of `sub_self` / `norm_zero` / `zero_pow` / `inv_pos`. Per the Phase-6
heuristics table, "a trivial simp/rewrite composition" is borderline-to-composable and
does **not** justify a *mathlib* lemma. It is already inlined verbatim at two project sites,
which empirically confirms the composition is what people write when they don't reach for
the wrapper.

---

## Verdict: `PadicLFunctions.inExpBall_one_sub_one`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the p-adic exp/log isometry and principal units are
  standard, but "0 ∈ ball" / "1 ∈ 1+B" is the *implicit basepoint* — no source names it as
  a citable lemma. NO-leaning signal.
- Generality analysis (Phase 4): MAXIMALLY GENERAL for the project-local predicate; no real
  weakening; Phase 4c finds no modern-idiom move for *this* lemma (the only one targets the
  *definition* `InExpBall`).
- Mathlib search (Phase 5): `InExpBall`/`padicLog`/`padicExp` are **absent from mathlib**, so
  it cannot be hosted as-is; mathlib has the abstract analog `Metric.mem_ball_self` and every
  building block (`sub_self`, `norm_zero`, `zero_pow`, `inv_pos`).
- Composition check (Phase 6): **COMPOSABLE** — the existing proof *is* a ≤3-call mathlib
  rewrite, already re-derived inline at `PadicExp.lean:261` and `ExtLog.lean:67–72`.

**Rationale:**

This theorem is the "trivial basepoint" fact that the centre `0` of the p-adic exponential
ball is a member — equivalently, that the identity `1` is a principal unit (`1 ∈ 1+B`). It
cannot be a mathlib contribution for a structural reason that the mathlib search settles
outright: it is a statement *about the project-local predicate* `PadicLFunctions.InExpBall`,
which does not exist anywhere in mathlib (mathlib has no `padicLog`/`padicExp`/`InExpBall`
API at all). There is nothing for mathlib to host without first upstreaming the entire
predicate — and even then, the natural upstream form of `InExpBall` is `x ∈ Metric.ball 0 r`,
at which point this lemma collapses to the existing `Metric.mem_ball_self` and disappears.

Within the project the content is a ≤3-call composition of mathlib primitives — `sub_self`
to reduce `1 − 1` to `0`, then `norm_zero`, `zero_pow`, `inv_pos`. The proof reference
heuristics class a trivial simp/rewrite chain like this as composable, not as a justified
lemma, and the call-site evidence corroborates it empirically: the *same fact* is already
typed out inline at two sites — including a verbatim copy of this very proof in the `zero`
case of `pow_mem_expBall` (`ExtLog.lean:67–72`) and a direct `InExpBall p 0` derivation in
`PadicExp.lean:261`. A lemma whose proof people re-type rather than reach for is a thin
wrapper, not an API anchor. The verdict is therefore NO-composable-from-mathlib: there is no
new *mathlib* lemma here.

**WHY not (refactor-actionable detail):**
Mathlib has the building blocks; the user's form is a 1–3 mathlib-call composition. It is
not a mathlib contribution because (a) it references a project-local predicate mathlib does
not have, and (b) its proof is a trivial rewrite chain over mathlib lemmas, already inlined
verbatim elsewhere in the project.

Mathlib building blocks:
  - `sub_self`  (`Mathlib/Algebra/Group/Basic.lean`) — `a - a = 0`
  - `norm_zero` (`Mathlib/Analysis/Normed/Group/Basic.lean`) — `‖0‖ = 0`
  - `zero_pow`  (`Mathlib/Algebra/GroupWithZero/Basic.lean`, also `Mathlib/Tactic/Ring/Common.lean:987`) — `0 < n → (0:R)^n = 0`
  - `inv_pos`   (`Mathlib/Algebra/Order/GroupWithZero/Basic.lean:842`) — `0 < a⁻¹ ↔ 0 < a`
  - (abstract analog, if `InExpBall` is ever re-aimed at `Metric.ball`: `Metric.mem_ball_self`, `Mathlib/Topology/MetricSpace/Pseudo/Defs.lean:382`)

Composition sketch (≤3 lines — this is the existing proof, all mathlib calls):
```lean
example : InExpBall p ((1 : L) - 1) := by
  rw [sub_self, InExpBall, norm_zero, zero_pow (by have := hp.out.one_lt; omega)]
  exact inv_pos.mpr (by exact_mod_cast hp.out.pos)
```

Call sites in our project (from Phase 6.0): **K = 5** (ExtLog.lean:405, 420, 430, 438;
ResidueZeta.lean:1757), plus 2 inline re-derivations of the same fact (PadicExp.lean:261;
ExtLog.lean:67–72).

Refactor plan (project-scoped — this is NOT a mathlib action):
  - **Recommended: keep the lemma as a project-internal convenience.** Because it is used at
    5 sites with a uniform idiom (the empty/trivial `InExpBall p (1 − 1)` witness), it does
    pull modest local weight. The NO verdict means only that **it is not a mathlib
    contribution** — do not open a mathlib PR for it.
  - If a cleaner-API pass is desired, the *real* refactor is upstream of this lemma: run
    `/generalise PadicLFunctions.InExpBall` to consider re-expressing the predicate as
    `x ∈ Metric.ball (0 : L) r`. If that lands, this theorem becomes `Metric.mem_ball_self
    (by positivity)` and the 2 inline re-derivations (PadicExp.lean:261, ExtLog.lean:67–72)
    can be unified to it as well — eliminating the duplication the call-site grep exposed.
  - Either way, at the 5 call sites no change is needed: they already use the lemma by name;
    if it is ever inlined, replace `inExpBall_one_sub_one p` with the 2-line composition
    above (note `sub_self` reduces `1 − 1` to `0`; the `zero_pow` side-goal needs `0 < p − 1`
    from `hp.out.one_lt`).

Next action: **do not PR to mathlib.** Optionally run `/generalise
PadicLFunctions.InExpBall` to re-aim the *predicate* at mathlib's `Metric.ball` API, which
would let this lemma and its two inline twins all collapse to `Metric.mem_ball_self`.

---

## Next step

Do not open a mathlib PR for `PadicLFunctions.inExpBall_one_sub_one` — it is a
project-internal one-line lemma about the project-local predicate `InExpBall`, and its
content is a ≤3-call composition of mathlib primitives (`sub_self`, `norm_zero`,
`zero_pow`, `inv_pos`) already re-derived inline at two project sites. Keep it as a local
convenience if desired. The only upstream-flavoured move is `/generalise
PadicLFunctions.InExpBall` (re-aim the predicate at `Metric.ball 0 r`), after which this
lemma collapses to mathlib's existing `Metric.mem_ball_self`.
