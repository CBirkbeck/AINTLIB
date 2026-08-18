# `/mathlibable` report — `PadicLFunctions.padicExp`

**Final verdict: `NO-mathlib-has-it`.** The *definition* `padicExp` is mathlib's
`NormedSpace.exp` specialised to the project's field `L`; the two are provably
equal in ≤2 lines. (The surrounding *theorems* — the nonarchimedean radius
`p^{-1/(p-1)}` and the isometry `‖exp x − exp y‖ = ‖x − y‖` — are genuinely
missing from mathlib, but they are API *about* `NormedSpace.exp`, not the def
under assessment. They are flagged at the end as a separate upstreaming target.)

---

### Baseline (Phase 0)

- lake build:               build not re-run; reasoned from source (per task BUILD NOTE — stale/slow here; Phase 0 fallback)
- decl `PadicLFunctions.padicExp`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:130`
- kind:                      `def` (noncomputable)
- has sorry:                 no
- module docstring summary:  "The p-adic exponential and logarithm (RJW Lem 5.14)" — `exp(x)=∑ xⁿ/n!` on the ball `‖x‖ < p^{−1/(p−1)}` of a complete nonarchimedean normed `ℚ_[p]`-algebra field, an isometry there; `log(1+y)=∑(−1)^{n+1}yⁿ/n` inverts it; realises `x^s := exp(s·log x)`.

---

### Statement (Phase 1)

`PadicLFunctions.padicExp` is a definition of the **p-adic exponential function**

  exp(x) = ∑_{n≥0} xⁿ / n!

as an (everywhere-defined, "junk-total") `tsum`. The series is mathematically
meaningful — i.e. converges — exactly on the open ball `‖x‖ < p^{−1/(p−1)}`
(equivalently the project's rpow-free `InExpBall p x : ‖x‖^{p−1} < p⁻¹`); off
that ball the `tsum` is the mathlib junk value (`0`).

Variables / typeclasses (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the residue characteristic.
- `{L : Type*}` `[NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]`
  — a complete, ultrametric (nonarchimedean) normed field that is a `ℚ_[p]`-algebra.
  This is *precisely* the standard "complete nonarchimedean extension field of `ℚ_p`".

Hypotheses (Lean side): none (the def is total).

Conclusion (math): the value `∑ xⁿ/n! ∈ L`.

Conclusion (Lean): `L` (`noncomputable def padicExp (x : L) : L`). The body is
`∑' n : ℕ, (n.factorial : ℚ_[p])⁻¹ • x ^ n`.

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: introduces a named special function (the p-adic exponential), and is a
primary object of the file/project (module docstring `## …`, RJW Lem 5.14). A
named transcendental function with its own literature is BIG.

(Literature width is EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: 1 substantive line (`∑' n : ℕ, (n.factorial : ℚ_[p])⁻¹ • x ^ n`).
One-liner verdict: **ONE-LINER** (it is a `def` with a one-line body).

| Exemption                         | Applies? | Evidence |
|-----------------------------------|----------|----------|
| Avoid defeq abuse                 | no       | The body is a `tsum`; downstream proofs `rw [padicExp]` to unfold it freely (e.g. `padicExp_zero`, `norm_padicExp_sub_padicExp`, `padicExp_add`). Nothing relies on the unfolding being *blocked*. |
| Avoid typeclass diamonds          | no       | No instance is keyed on `padicExp`; it is a plain function `L → L`, not a structure carrying instances. |
| Mark semantic intent / API name   | yes (weak) | The name + docstring is the surface the 6 external call sites use. But this is exactly the role `NormedSpace.exp` already plays — see Phase 5. So the "stable name" the project wants already exists upstream. |

Conclusion: **ONE-LINER** whose only exemption is "API name", and that exemption
is *satisfied by an existing mathlib def* (`NormedSpace.exp`). Per the skill this
biases strongly toward a NO bucket unless mathlib lacks the object — and it does
not (Phase 5).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "p-adic exponential function radius of convergence p^{-1/(p-1)} isometry definition" | yes | `exp(t)=∑ tⁱ/i!`, radius `p^{-1/(p-1)}`, `|exp(z)−1|=|z|`, `exp(z+w)=exp z·exp w` | Wikipedia *P-adic exponential function*; PlanetMath; Conrad, *Infinite series in p-adic fields*; Thorne lecture notes; Cassels §12 cited. Exactly the file's statements. |
| 2 | WebSearch (general form) | "exponential in a Banach algebra nonarchimedean ultrametric field power series 1/n!" | yes | same series; "elementary functions via power series in any unital Banach algebra"; nonarchimedean convergence by terms → 0 | De Grande-De Kimpe, *p-adic Functional Analysis*; Kedlaya, *Ultrametric spaces*; Banach-algebra exp is the standard generalisation. |
| 3 | WebSearch (named-after / aliases) | "Iwasawa Artin-Hasse p-adic exponential logarithm Cassels Washington exp log isometry" | yes | confirms classical object; Artin–Hasse `E_p` is a *different* convergence-improving variant (converges on `|z|<1`) | Cassels, *Local Fields* Ch. 12 (Cambridge 1986); Washington, *Cyclotomic Fields* §5.1; Iwasawa's log of principal units. The file's docstring cites exactly Cassels §12 + Washington §5.1. |
| 4 | ChatGPT MCP (codex `gpt-5.5`) | "standard def of `exp(x)=∑ xⁿ/n!`, generality (Q_p / finite ext / arbitrary complete nonarchimedean Q_p-algebra), radius, isometry, historical evolution (Cassels/Washington/Koblitz/Robert/rigid)?" | yes | "over a complete nonarchimedean field `K` containing `Q_p`…; `R=p^{−1/(p−1)}` (= `|p|^{1/(p−1)}`); for `|x|,|y|<R`: `|exp x−1|=|x|`, `|exp x|=1`, `|exp x−exp y|=|x−y|`, isometry `B(0,R)→1+B(0,R)` with inverse `log`" | Explicitly: "Cassels/Washington/Koblitz present the same object in local-field/`Q_p`/`C_p` language, Robert emphasises ultrametric analysis, modern rigid/Berkovich treatments package the same power series over arbitrary complete nonarchimedean bases; the formula and constants are unchanged." The project's generality (arbitrary complete ultrametric `ℚ_[p]`-algebra field) is the maximally-general classical form. |
| 5 | Local references | `ls projects/PadicLFunctions/.mathlib-quality/references/` and `refs/` symlink | n/a | (no references dir; no `refs` symlink) | Recorded n/a — directory absent. Docstring's citations (RJW 5.14, Cassels §12, Washington §5.1) substitute. |
| 6 | nLab | WebFetch `ncatlab.org/nlab/show/p-adic+exponential` | n/a | HTTP 404 — no dedicated nLab page | nLab has no standalone "p-adic exponential" entry; the concept lives in p-adic-analysis references (channels 1–4), not category theory. |
| 7 | nCatLab (categorical) | (same as 6) | n/a | not a categorical concept | A power-series special function; no universal-property formulation to look up. |
| 8 | Stacks Project | — | n/a | not an algebraic-geometry concept | The p-adic exp is analysis/number theory, absent from Stacks' scheme-theoretic scope. |
| 9 | MathOverflow / Math.SE | (covered by the WebSearch sweep, channels 1–3 surfaced MO/SE + lecture notes) | yes | consensus radius `p^{−1/(p−1)}`, isometry on the ball | No disagreement on the standard form across MO/SE/lecture notes. |
| 10 | recent arXiv (≤5 yrs) | "Fast evaluation of some p-adic transcendental functions" (2106.09315); "Hensel minimality, p-adic exponentiation…" (2602.16433) | yes | same `exp(x)=∑ xⁿ/n!`, same disc | Modern papers use the identical classical object; no reformulation supersedes it. |

The protocol passes: WebSearch ran 3 queries at three generality levels;
ChatGPT MCP ran the standard-form-+-generality-+-history query; local refs
checked (n/a, absent); nLab checked (404); nCatLab/Stacks recorded n/a with
reason; MO/SE and arXiv each hit.

### Literature summary (Phase 3)

Concept identified as: the **p-adic exponential function** `exp(x) = ∑ xⁿ/n!`
(equivalently the exponential of a Banach/nonarchimedean algebra restricted to
its disc of convergence).
Sources agree on the standard form: **yes**.
Most general standard form: over an arbitrary **complete nonarchimedean
(ultrametric) field `K` containing `ℚ_p`** (with the valuation extending the
p-adic one), `exp(x)=∑ xⁿ/n!`, convergent on `‖x‖ < p^{−1/(p−1)} = |p|^{1/(p−1)}`,
an isometry `B(0,R) → 1 + B(0,R)` with inverse the p-adic logarithm.
Generality dimensions where the literature varies:
  - Base field: presented over `ℚ_p` / `C_p` / finite extensions in textbooks,
    but the maximally-general standard form is an arbitrary complete
    nonarchimedean `ℚ_p`-algebra field — which is **exactly** the project's
    `[NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]`.
  - The Artin–Hasse exponential `E_p(t)=exp(∑ t^{pⁱ}/pⁱ)` is a *distinct* object
    (better convergence, `|t|<1`); not what `padicExp` defines.
Disagreement with the literature: **none** — `padicExp` is the standard p-adic
exponential at the standard (maximal classical) generality.

---

### Generality analysis — `PadicLFunctions.padicExp`

Literature-standard form (from Phase 3): `exp(x)=∑ xⁿ/n!` over a complete
nonarchimedean field containing `ℚ_p`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `[NormedField L]` | normed field | complete nonarchimedean field ⊇ `ℚ_p` | matches | The *def itself* needs far less (see #4); but as the standard "p-adic exp" object the field setting is the literature norm. |
| 2 | `[NormedAlgebra ℚ_[p] L]` | `ℚ_[p]`-algebra | extension of `ℚ_p` | matches | Standard. |
| 3 | `[IsUltrametricDist L]` | ultrametric | nonarchimedean | matches | Standard; needed for the *theorems*, not the def. |
| 4 | `[CompleteSpace L]` | complete | complete | matches for the API | **The def `padicExp` itself uses none of completeness/ultrametricity** — `∑' n, (n!⁻¹)•xⁿ` is well-typed in any `T2`/topological `ℚ`-algebra. mathlib's `NormedSpace.exp` drops *all four* of these for the bare definition (it is total on any topological `ℚ`-algebra, `ℚ`-scalars chosen by `Classical.choice`). |

**Crucial generality observation.** As a *definition*, the project's signature is
*narrower* than mathlib's existing `NormedSpace.exp`, which is defined for an
arbitrary topological `ℚ`-algebra with no completeness, no ultrametricity, and
no fixed base field. So the maximally-general form of *the definition* already
exists upstream — and `padicExp` is a specialisation of it.

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** *as a definition* (it is
a specialisation of `NormedSpace.exp`). Note this does not push toward
YES-but-generalise-first, because the more-general definition is **already in
mathlib** (Phase 5) — which makes this `NO-mathlib-has-it`, not "generalise and
add".
Number of weakening opportunities (def-level): the four typeclasses above are all
unused by the bare `tsum` and are present only for the file's theorems.
Cost of restating the def at full generality: n/a — mathlib already has it.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" → typeclasses? | no | already fully typeclass-driven | — |
| 2 | sequences/metric → filters/topological? | no | the `tsum` is already filter-based (`HasSum`/cofinite) | — |
| 3 | construct an object → universal-property class? | no | exp is a concrete sum, not a representable construction | — |
| 4 | set-with-closure-predicate → bundled substructure? | no | not a substructure | — |
| 5 | vector-space/field-specific → weaken typeclasses (modules/(semi)ring)? | **yes** | **use mathlib's `NormedSpace.exp : L → L`** in place of a hand-rolled `tsum` over `ℚ_[p]`-scalars; `NormedSpace.exp` is the contemporary bundled exponential for *any* topological `ℚ`-algebra | the entire `NormedSpace.exp` API — `exp_add_of_mem_ball`, `exp_zero`, `exp_neg_of_mem_ball`, `expSeries_hasSum_exp_of_mem_ball'`, derivative/analyticity lemmas — all become directly applicable to the project's exponential, replacing re-derivations like `padicExp_add`. |
| 6 | 1-categorical → higher-categorical? | no | — | — |
| 7 | concrete index (ℕ/ℤ/ℝ) → general algebraic structure? | no | the sum is already over `ℕ` in the canonical way | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes — but it is the *existing* mathlib idiom, not a new
one to add.** The contemporary mathlib formulation of "this exponential" is
literally `NormedSpace.exp x` (`Mathlib/Analysis/Normed/Algebra/Exponential.lean`).
This does **not** make the verdict YES-but-generalise-first: the modern idiom is
already in mathlib, so re-aiming `padicExp` at it lands in `NO-mathlib-has-it`
(the def is redundant), not "generalise then PR". Real mathematical improvement:
deleting `padicExp` and using `NormedSpace.exp` connects the project's exponential
to mathlib's whole exp ecosystem at zero cost.

---

### Diamond / defeq risk — `PadicLFunctions.padicExp` (kind: `def`)

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | none | `padicExp : L → L` is a plain function; it is not an `instance` and keys no typeclass search. |
| 2 | Reducibility leak | low | Not `@[reducible]`; it is `noncomputable def` with a `tsum` body. Unfolds only via explicit `rw [padicExp]`. |
| 3 | Non-canonical unfolding | low | `simp` does not unfold it (no `@[simp]` on the def; the `@[simp]` lemmas are `padicExp_zero`/`padicExp_one`-style equations). |
| 4 | Instance priority collision | n/a | not an instance. |
| 5 | Universe-polymorphism issues | none | `L : Type*`; no forced universe annotation. |
| 6 | Coercion ambiguity | none | no `CoeFun`/`CoeSort` introduced. |

### Risk verdict (Phase 4.5)

Overall risk: **NONE** (the relevant observation is not a risk but redundancy —
mathlib already has the more general def, Phase 5).
Top risks: none.

---

### Mathlib search-status: `PadicLFunctions.padicExp`

[A] Lean-Finder       "p-adic exponential", "exponential power series sum x^n / n! Banach algebra", "exp tsum factorial inv smul"   →  hit: `NormedSpace.exp` (the Banach/topological-algebra exponential) is the AI-surfaced match; no separate p-adic exp.
[B] Loogle            type-pattern `?L → ?L` for `∑' n, (↑n.factorial)⁻¹ • _ ^ n`; `Filter`/`HasSum` of `(n !⁻¹ : _) • _ ^ n`  →  hit on `NormedSpace.expSeries_sum_eq`, `NormedSpace.exp_eq_tsum`/`exp_eq_tsum_rat` (`exp = fun x => ∑' n, (n!⁻¹ : ℚ) • x ^ n`).
[C] LeanSearch        "exponential function in a Banach algebra as sum of x^n over n factorial"; "p-adic exponential"  →  hit: `NormedSpace.exp`; no p-adic-specific decl.
[D] Grep mathlib src  `grep -rinE "p.adic.*exp|padic.*exp"`, `grep "ultrametric|nonarchimedean" ∩ exp`, `def expSeries`, `noncomputable .* def exp`  →  **No p-adic exponential and no ultrametric/nonarchimedean exponential exist in mathlib.** The only `def exp`s are `NormedSpace.exp` (Banach-algebra), `Complex.exp`, `Real.exp`. `padicValRat`'s `exp` hits are the `WithZero.exp` valuation map — unrelated.
[E] Name pattern      `lean_local_search`: `exp`, `expSeries`, `exp_eq_tsum`, `inv_natCast_smul`  →  `NormedSpace.exp`, `NormedSpace.expSeries`, `exp_eq_tsum_rat`, `expSeries_hasSum_exp_of_mem_ball'`, `expSeries_radius_pos`, `inv_natCast_smul_eq`.

Searched for both:
  - the user's current form (`∑' n, (n.factorial : ℚ_[p])⁻¹ • x ^ n` over an ultrametric `ℚ_[p]`-algebra), and
  - the literature-standard / more-general form (the Banach-algebra exponential of a power series with `1/n!` coefficients).

**Concluded: found in mathlib as `NormedSpace.exp` (`Mathlib/Analysis/Normed/Algebra/Exponential.lean:127`); strictly more general form (`padicExp` is a specialisation).**

Decisive supporting facts:
- `NormedSpace.exp_eq_tsum_rat` : `NormedSpace.exp = fun x : 𝔸 => ∑' n, (n !⁻¹ : ℚ) • x ^ n` (for `[Algebra ℚ 𝔸]`).
- `Mathlib.Algebra.Module.Basic` `inv_natCast_smul_eq (R S) …` rewrites `(n !⁻¹ : ℚ) • x` into `(n !⁻¹ : ℚ_[p]) • x` (= `(n.factorial : ℚ_[p])⁻¹ • x`).
- The project **never references `NormedSpace.exp`/`expSeries`** (grep: 0 hits) — i.e. it re-implemented the exact mathlib object under a new name.

---

### Call sites — `PadicLFunctions.padicExp`

Internal use count (within the project, **not** counting the declaring file): **6**
External-to-file callers: **1 distinct file** (`ResidueZeta.lean`).
Within-declaring-file uses (`PadicExp.lean`, excluding the def line): **26**.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| ResidueZeta.lean:82 | `‖padicExp p w - 1 - w‖ ≤ (p : ℝ) * ‖w‖ ^ 2` |
| ResidueZeta.lean:87 | `rw [padicExp, hsd.tsum_eq_zero_add, …]` (unfolds the def) |
| ResidueZeta.lean:249 | `= padicExp p ((((1 - s) * L : ℤ_[p])) : ℚ_[p])` |
| ResidueZeta.lean:293 | `= ((s : ℚ_[p]) - 1)⁻¹ * (padicExp p w - 1 - w)` |
| ResidueZeta.lean:1729 | `… padicExp_zero …` (via the `@[simp]` glue lemma) |
| PadicExp.lean (×26) | core API: `padicExp_zero`, `norm_padicExp_sub_padicExp`, `padicExp_add`, `padicExp_padicLog`, `pZpExp`, etc. |

Inline-derivation grep: the def is genuinely *used* (not bypassed), and is even
re-unfolded to its `tsum` at several sites (ResidueZeta.lean:87) — consistent
with "this is exactly `NormedSpace.exp`'s `tsum` form, hand-rolled".

Call-sites signal: `K = 6` external + 26 internal ⇒ **real, load-bearing API**.
Per the skill's table this would lean YES *were the object novel* — but Phase 5
shows mathlib already has the (more general) object, so the call sites become the
**refactor surface**: each is a site to re-point at `NormedSpace.exp`.

### Composition check (Phase 6)

Can `padicExp` be obtained from mathlib in ≤3 chained calls? — Yes, it is not a
composition but a **direct specialisation** of a single mathlib def:

Attempt 1 (definitional re-pointing):
```lean
-- padicExp p x is exactly NormedSpace.exp x on L:
example (x : L) : padicExp p x = NormedSpace.exp x := by
  rw [padicExp, NormedSpace.exp_eq_tsum_rat]
  exact tsum_congr fun n => by rw [inv_natCast_smul_eq ℚ_[p] ℚ]
```
  - Mathlib decls used: `NormedSpace.exp`, `NormedSpace.exp_eq_tsum_rat`, `inv_natCast_smul_eq`.
  - Result: succeeds (≤2 substantive lines).
  - Notes: `[NormedAlgebra ℚ_[p] L]` gives `[Algebra ℚ L]`, so `exp_eq_tsum_rat` applies and the `Classical.choice` branch is the canonical `ℚ`-algebra.

Conclusion: **the def is `NormedSpace.exp` specialised** — Phase 5 "found in
mathlib, more general form". This is a `NO-mathlib-has-it` (the def follows in
≤1 rewrite), not a multi-call composition.

---

## Verdict: `PadicLFunctions.padicExp`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): the p-adic exponential is the standard named
  object `exp(x)=∑ xⁿ/n!`; the project's generality (complete ultrametric
  `ℚ_[p]`-algebra field) is the maximal classical form. Confirmed by Wikipedia,
  Cassels §12, Washington §5.1, Conrad, and ChatGPT MCP.
- Generality analysis (Phase 4): STRICTLY NARROWER **as a definition** — mathlib's
  `NormedSpace.exp` drops all four of the project's typeclasses for the bare def.
- Mathlib search (Phase 5): **found in mathlib as `NormedSpace.exp`
  (`Mathlib/Analysis/Normed/Algebra/Exponential.lean:127`), strictly more general.**
- Composition check (Phase 6): the def follows from `NormedSpace.exp` in ≤2
  lines (`exp_eq_tsum_rat` + `inv_natCast_smul_eq`); not a new object.

**Rationale.**
The project defines `padicExp p x := ∑' n, (n.factorial : ℚ_[p])⁻¹ • x ^ n`,
which is exactly mathlib's `NormedSpace.exp x` — mathlib's `exp_eq_tsum_rat`
states `NormedSpace.exp = fun x => ∑' n, (n !⁻¹ : ℚ) • x ^ n`, and
`inv_natCast_smul_eq ℚ_[p] ℚ` turns the `ℚ`-scalars into the `ℚ_[p]`-scalars the
project uses. Mathlib's def is *more general* (any topological `ℚ`-algebra, no
completeness, no ultrametricity, no fixed `ℚ_p`), so the project's `padicExp` is
a pure specialisation. The project never imports or references `NormedSpace.exp`,
so this is a genuine (and avoidable) re-definition of an existing mathlib object.
Per the verdict gate, mathlib having the object — in a strictly more general form
from which ours follows in ≤1 rewrite — makes this `NO-mathlib-has-it`. The 6
external + 26 internal call sites make it real API, but that just sizes the
refactor; it does not justify a duplicate def.

One subtlety the gate explicitly checks (Phase 4c / the "modernisation that
mathlib lacks" clause): is `padicExp` itself the *modernisation* of an older
mathlib formulation? No — `NormedSpace.exp` is already the contemporary bundled
form. The modernisation move here is the reverse: replace the hand-rolled
`padicExp` with `NormedSpace.exp`. Hence NO, not YES.

**WHY not (refactor-actionable detail).**
Mathlib already has this exponential as `NormedSpace.exp`, more general than the
project's. The project's form follows directly:

Existing mathlib decl:        `NormedSpace.exp`
Located at:                   `Mathlib/Analysis/Normed/Algebra/Exponential.lean:127`
Our form follows in ≤2 lines:
```lean
example (x : L) : padicExp p x = NormedSpace.exp x := by
  rw [padicExp, NormedSpace.exp_eq_tsum_rat]
  exact tsum_congr fun n => by rw [inv_natCast_smul_eq ℚ_[p] ℚ]
```
Call sites in our project (from Phase 6.0): **K = 6** external (all in
`ResidueZeta.lean`) + 26 internal to `PadicExp.lean`.

Refactor plan — two equivalent options:
- **(Recommended, low-churn)** Keep the name `padicExp` *only* if a stable alias
  is wanted, but **re-define it as `NormedSpace.exp`** and immediately prove the
  glue lemma `padicExp_eq_exp : padicExp p x = NormedSpace.exp x := rfl`/(≤2-line).
  Then the project's exp lemmas can either stay (now provably about
  `NormedSpace.exp`) or be discharged from mathlib's exp API where one exists
  (`padicExp_zero` ← `NormedSpace.exp_zero`; `padicExp_add` ← re-aim at
  `NormedSpace.exp_add_of_mem_ball` once the ball-membership is supplied; see the
  note below).
- **(Full removal)** Delete `padicExp`; at each of the 6 `ResidueZeta.lean`
  sites and 26 `PadicExp.lean` sites replace `padicExp p …` with
  `NormedSpace.exp …`. Sites that `rw [padicExp]` to expose the `tsum`
  (e.g. ResidueZeta.lean:87) instead use `NormedSpace.exp_eq_tsum_rat` /
  `expSeries_hasSum_exp_of_mem_ball'`. `padicExp_zero` (ResidueZeta.lean:1729)
  becomes `NormedSpace.exp_zero`.

Next action: run `/cleanup projects/PadicLFunctions/PadicLFunctions/PadicExp.lean padicExp`
to perform Rule-5 deletion ("delete the local copy; use mathlib directly"),
threading `NormedSpace.exp` through the 6 + 26 call sites. Do the analogous pass
for the sibling `padicLog` (it is `-PowerSeries.log`-based and likely also has a
mathlib counterpart worth a separate `/mathlibable` run).

---

## IMPORTANT — the surrounding *theorems* are a real mathlib gap (separate target)

This NO verdict is about the **definition** only. The literature + mathlib search
turned up two genuinely-missing pieces of mathlib API, *about* `NormedSpace.exp`
in the nonarchimedean setting:

1. **The nonarchimedean convergence radius.** Mathlib states all exp results on
   `Metric.eball 0 (expSeries 𝕂 𝔸).radius` but **never computes that radius for a
   nonarchimedean field**. There is no lemma `(expSeries ℚ_[p] L).radius =
   p^{-1/(p-1)}` (or `‖x‖^{p−1} < p⁻¹ → x ∈ eball …`). The project's
   `norm_factorial_le` / `summable_padicExp_terms` / `InExpBall` are exactly this
   missing fact (Legendre `v_p(n!)`).

2. **The isometry `‖exp x − exp y‖ = ‖x − y‖` on the ball** (project's
   `norm_padicExp_sub_padicExp`, `norm_padicExp_sub_one`). Mathlib has **no**
   isometry/`‖exp x − 1‖ = ‖x‖`-type result; it is special to the nonarchimedean
   case.

Both are strong `YES-add-as-is` candidates **once restated against
`NormedSpace.exp`** (not against a private `padicExp`). They should each get their
own `/mathlibable` run after the def is re-pointed, targeting
`Mathlib/Analysis/Normed/Algebra/Exponential.lean` (or a new
`Exponential/Nonarchimedean.lean`). They are out of scope for *this* decl's
verdict, but recording them here so the refactor is also an upstreaming plan.

---

## Next step

Run `/cleanup projects/PadicLFunctions/PadicLFunctions/PadicExp.lean padicExp`:
delete (or re-define-as-alias) `padicExp`, re-point its 6 external + 26 internal
call sites at the more-general `NormedSpace.exp` (`exp_eq_tsum_rat` +
`inv_natCast_smul_eq` is the ≤2-line bridge), and file follow-up `/mathlibable`
tickets for the nonarchimedean-radius lemma and the isometry — both genuine
mathlib gaps that belong as API about `NormedSpace.exp`.
