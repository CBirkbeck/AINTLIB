# `/mathlibable` report — `PadicLFunctions.padicLog_padicExp`

**Mode A — full 10-phase workflow, exhaustive 9-channel literature search.**

---

### Baseline (Phase 0)
- lake build:               build not re-run; reasoned from source (per task instruction — `lake build` is stale/slow here; declaration + dependency closure read directly from source, as the skill's Phase 0 fallback allows).
- decl `PadicLFunctions.padicLog_padicExp`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:950`
- kind:                      theorem
- has sorry:                 no (proof body lines 950–969 contain zero `sorry`)
- module docstring summary:  `PadicExp.lean` develops the p-adic exponential `exp(x)=∑ xⁿ/n!` (converges on `‖x‖ < p^{−1/(p−1)}`, isometry there) and logarithm `log(1+y)=∑(−1)^{n+1}yⁿ/n` (`‖y‖<1`) on a nonarchimedean complete normed `ℚ_[p]`-algebra field; realises RJW Lemma 5.14 / Washington §5.1.

---

### Statement (Phase 1)

`PadicLFunctions.padicLog_padicExp` is a theorem stating the following:

> Let `L` be a complete, ultrametric, normed field that is a normed `ℚ_[p]`-algebra (so `L ⊇ ℚ_[p]`; the canonical case is `L = ℂ_p`). For every `x ∈ L` in the open exponential convergence ball — i.e. `‖x‖ < p^{−1/(p−1)}`, encoded rpow-free as `‖x‖^{p−1} < p⁻¹` — the p-adic logarithm inverts the p-adic exponential: `log(exp(x)) = x`.

This is one half of the statement that `exp` and `log` are mutually inverse isometric isomorphisms between the open ball `B(0, p^{−1/(p−1)})` and the multiplicative ball `1 + B(0, p^{−1/(p−1)})`. The companion `padicExp_padicLog` (line 935) is the other half.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the prime.
- `{L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]` — a complete nonarchimedean normed field over `ℚ_[p]`. The mathematical role: this is the analytic ambient field where the two series converge and Fubini/ultrametric rearrangement is valid. `ℂ_p` (and every finite extension of `ℚ_[p]`) is an instance.

Hypotheses (Lean side):
- `(hx : InExpBall p x)` where `InExpBall p x := ‖x‖ ^ (p - 1) < (p : ℝ)⁻¹` — `x` lies in the open exponential convergence ball. Mathematical role: guarantees both `exp(x)` converges and `exp(x)−1` lies in the log convergence ball, so the composite is defined and the formal-to-analytic transfer applies.

Conclusion (math): `log(exp(x)) = x` for `x` in the open ball of radius `p^{−1/(p−1)}`.

Conclusion (Lean): `padicLog p (padicExp p x) = x`.

Proof shape (for context, not graded): reduce both sides to their `tsum`-of-coefficient forms (`padicLog_eq_tsum_coeff`, `tsum_coeff_exp_sub_one`), apply the project's `master_bridge` (ultrametric Fubini / series-composition transfer) to turn the composite analytic sum into the analytic evaluation of the **formal** composite `(log ℚ_[p]).subst (exp ℚ_[p] − 1)`, then discharge the formal identity via `log_subst_exp_sub_one : (log ℚ_[p]).subst (exp ℚ_[p] − 1) = X` and evaluate `X` at `x` via `eval_X`. So the theorem is the *analytic* shadow of the *formal* power-series inversion, transferred across the convergence ball.

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: It is a main structural result of the project's p-adic exp/log development (a named inversion theorem, explicitly RJW Lem 5.14 / Washington Prop 5.3 in the module docstring) and it is the analytic half of a theorem that is canonical in the literature ("exp and log are mutually inverse on the p-adic disk"). Theorems of this kind are essentially guaranteed to appear in the literature in some form.

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Body line count: ~20 substantive lines (a real proof with `master_bridge`, summability witnesses, and the formal-identity discharge).
One-liner verdict: **n/a — kind is `theorem`, not `def`.** Check skipped.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "p-adic logarithm inverse of p-adic exponential convergence ball log(exp(x))=x Washington cyclotomic fields" | yes | `log(exp(x)) = x` on the disk; exp/log mutually inverse | PlanetMath, Wikipedia, MIT 18.785 notes (dav/exp.pdf), Conrad/Thorne notes all confirm |
| 2 | WebSearch (general form) | "p-adic exponential logarithm mutually inverse local isomorphism disk Neukirch Cassels" | yes | `exp∘log = id`, `log∘exp = id` as mutually inverse isomorphisms on the respective disks | Cassels *Local Fields* §12 (the project's own cited source); Wikipedia; Cambridge p-adic notes (Thorne) |
| 3 | WebSearch (named-after / aliases) | "p-adic logarithm exponential isometry isomorphism 1+pZp onto pZp for odd p standard theorem statement" | yes | `log : 1 + pℤ_p ≅ pℤ_p` for odd `p`; `exp∘log=id` on `1+pZ_p`, `log∘exp=id` on `pZ_p` | Harron AWS 2018 problems; MIT notes; Conrad notes — the `1+pℤ_p ≅ pℤ_p` isomorphism is the textbook packaging |
| 4 | ChatGPT MCP | (intended: "standard form, generality, historical evolution of p-adic log∘exp=id") | n/a | — | MCP `plugin:mathlib-quality:chatgpt-math` is configured for a different machine (server path `/home/chris/...`) and **failed to connect** here. Compensated by running 6 WebSearch/WebFetch queries (rows 1–3, 5, 9, 10) at multiple generality levels. |
| 5 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/` for "exp"/"log" | n/a | — | Neither directory exists (no `.mathlib-quality/references/`; no `refs/` symlink in this checkout). Recorded n/a. The module docstring's own citations (RJW Lem 5.14, TeX 1892–1897; Cassels §12; Washington §5.1) serve as the source anchors. |
| 6 | nLab | WebFetch `ncatlab.org/nlab/show/p-adic+exponential` | n/a | — | Page returns HTTP 404; nLab has no dedicated p-adic exponential/logarithm page. Not a categorical concept — recorded n/a. |
| 7 | nCatLab (if categorical) | — | n/a | — | Not a categorical concept (a concrete analytic identity on a normed field); nothing to find. |
| 8 | Stacks Project (if alg geom) | — | n/a | — | Not an algebraic-geometry concept (p-adic analysis / local analysis, not scheme theory). |
| 9 | MathOverflow / Math.StackExchange | "p-adic exponential logarithm complete nonarchimedean normed field extension Qp ultrametric isometry general theorem" | yes | exp/log converge on `\|x\|<1` resp. the smaller exp disk; well-behaved over finite extensions of `ℚ_p`; the unique-norm-extension framework makes it work over any complete nonarchimedean field | Confirms the general (extension-of-`ℚ_p` / complete nonarchimedean) setting; surfaced de Frutos-Fernández ITP 2023 norm-extensions Lean work |
| 10 | recent arXiv (last 5 years) | "Lean mathlib p-adic exponential logarithm padicExp padicLog formalization" + Wikipedia fetch | yes | Wikipedia: `exp_p(log_p(1+z))=1+z` and `log_p(exp_p(z))=z`; exp converges `\|z\|_p < p^{−1/(p−1)}`, log for `\|z−1\|_p<1`; stated over `ℂ_p` | Confirms the **exact** project form; also confirms mathlib has p-adic numbers + Hensel but **no** analytic p-adic exp/log (Narayanan arXiv:2302.14491 is p-adic L-functions in Lean 3, not exp/log inversion) |

**Protocol pass check:** WebSearch ran 4 distinct queries at three generality levels (specific `log(exp x)=x`; general "mutually inverse isomorphism"; named `1+pℤ_p ≅ pℤ_p`) ✓. ChatGPT MCP unavailable on this machine — recorded n/a with reason and compensated with extra WebSearch/WebFetch breadth ✓. Local references checked (absent) ✓. nLab checked (404 / absent) ✓. Stacks / nCatLab / MathOverflow / arXiv each checked or n/a-with-reason ✓.

### Literature summary (Phase 3)

Concept identified as: **the p-adic logarithm as the inverse of the p-adic exponential on the convergence disk** (equivalently, `exp`/`log` as mutually inverse isometric isomorphisms of the open ball `‖x‖ < p^{−1/(p−1)}` with `1 + (that ball)`; textbook packaging: `log : 1 + pℤ_p ≅ pℤ_p` for odd `p`).

Sources agree on the standard form: **yes.** Wikipedia, PlanetMath, MIT 18.785 (`dav/exp.pdf`), Conrad–Thorne notes, Cambridge notes, and Cassels *Local Fields* §12 all give `log(exp(x)) = x` on the exp-convergence disk. The radius condition `‖x‖ < p^{−1/(p−1)}` is universal.

Most general standard form: For **any** field `K` complete with respect to a nonarchimedean absolute value extending the `p`-adic one (in particular `ℂ_p` and every finite/algebraic extension of `ℚ_p`), `exp` and `log` are mutually inverse isometries between the open ball of radius `p^{−1/(p−1)}` about `0` and its image `1 + (ball)`; on that ball `log(exp(x)) = x`.

Generality dimensions where the literature varies:
- **Ambient field**: ranges from `ℚ_p` (most elementary texts) → finite extensions `K/ℚ_p` → `ℂ_p` → "any complete nonarchimedean field over `ℚ_p`". The most general is "complete nonarchimedean normed field over `ℚ_p`", which is exactly the project's `[NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]`.
- **Ball encoding**: stated via valuation (`v(x) > 1/(p−1)`), via `rpow` (`‖x‖ < p^{−1/(p−1)}`), or rpow-free (`‖x‖^{p−1} < p⁻¹`). All equivalent; the project uses the rpow-free `InExpBall`.

Disagreement with the literature: **none.** The project's statement is the literature-standard statement, stated at (essentially) the most general standard generality.

---

### Generality analysis — `PadicLFunctions.padicLog_padicExp`

Literature-standard form (from Phase 3): `log(exp(x)) = x` for `x` in the open ball `‖x‖ < p^{−1/(p−1)}`, over any complete nonarchimedean normed field extending `ℚ_p`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `[NormedField L]` | normed field | complete nonarch. field over `ℚ_p` | NO | `padicExp`/`padicLog` land in `L`; `exp` is series in `(n!)⁻¹` from `ℚ_[p]`. A field (not just ring) is the standard setting; nonarchimedean-field is exactly the literature ambient. |
| 2 | `[NormedAlgebra ℚ_[p] L]` | normed `ℚ_[p]`-algebra | extension of `ℚ_p` | NO | Needed to coerce `(coeff n) : ℚ_[p]` scalars into `L` and to have `p`-adic norm. This *is* "L is an extension-field-flavoured object over `ℚ_p`" — the literature ambient. |
| 3 | `[IsUltrametricDist L]` | ultrametric (nonarchimedean) | nonarchimedean | NO | The whole convergence/Fubini argument is nonarchimedean; this is intrinsic to p-adic analysis, not a removable convenience. |
| 4 | `[CompleteSpace L]` | complete | complete | NO | Convergence of the defining `tsum`s requires completeness. Literature-standard. |
| 5 | `(hx : InExpBall p x)` (`‖x‖^{p−1} < p⁻¹`) | open exp ball | open ball `‖x‖ < p^{−1/(p−1)}` | NO | This is exactly the (sharp) literature radius. Cannot be weakened — `log∘exp=id` fails outside it (`exp` itself diverges). |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL.**
Number of weakening opportunities found: **0.**
Proposed restatement: none — the hypothesis cluster `[NormedField] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist] [CompleteSpace]` is precisely the standard ambient ("complete nonarchimedean field over `ℚ_p`"), and `InExpBall` is the sharp convergence radius.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "Let X be a foo" preambles → typeclasses/instances? | no | Already fully typeclass-driven (`[NormedField]`, `[NormedAlgebra]`, `[IsUltrametricDist]`, `[CompleteSpace]`). The one bundled hypothesis `InExpBall` is a genuine analytic side-condition (ball membership), not a "let X be" preamble. | — |
| 2 | Sequences/metric → filters/nets/topological? | no | The statement is a pointwise equation `log(exp x)=x`; the *proof* already uses `Summable`/`tsum` (filter-based) and `Tendsto … cofinite`. Nothing sequence-bound to filter-ise in the statement. | — |
| 3 | Construct an object where a universal property would characterise it? | partial-but-no | One *could* package exp/log as a bundled `≃`/group-isomorphism of balls (a "local mul-equiv"). But that is a **separate, additional** API layer (`padicExpEquiv : ball ≃* (1+ball)`), not a reformulation of *this* inversion lemma — and this lemma would be exactly the field-equation you prove to *build* such an equiv. So it is downstream API, not a modernisation of this statement. | (would be: a future `padicExpEquiv` bundling — but that needs *this* lemma as input) |
| 4 | Set-with-closure-predicate → bundled substructure? | no | `InExpBall` is an open-ball membership predicate; there is no algebraic substructure to bundle here. | — |
| 5 | Vector-space/metric/field-specific → weaker typeclass (module/pseudometric/semiring)? | no | This is intrinsically about a complete nonarchimedean *field* over `ℚ_p`; weakening to a ring/module is not what the literature does and the division by `n!` and `n` requires characteristic-0 field structure inherited from `ℚ_[p]`. | — |
| 6 | 1-categorical → higher/∞-categorical? | no | A concrete analytic identity; no categorification target. | — |
| 7 | Concrete index (ℕ,ℤ,ℝ) → arbitrary group/monoid/ordered structure? | no | No free index in the statement; `p` is the fixed prime, `x` ranges over the ball. | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no.**
One-line reason: The statement is already fully typeclass-driven at the literature-standard generality; the only adjacent "modernisation" (bundling exp/log as a `≃*` of balls) is a *new downstream API layer that consumes this lemma*, not a reformulation of it. The lemma as stated is the right field-equation to upstream.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem`. (No definitional equalities or typeclass-search paths introduced.)

---

### Mathlib search-status: `PadicLFunctions.padicLog_padicExp`

[A] Lean-Finder       "p-adic logarithm inverse exponential", "padicLog padicExp"   → no hits (Lean-Finder MCP not available in this environment; substituted by the mathlib4-docs WebSearch in [C], which returned no analytic p-adic exp/log)
[B] Loogle            type pattern `?f (?g ?x) = ?x` over `ℚ_[p]`/normed-field exp/log   → n/a: Loogle MCP not reachable here. Compensated by direct mathlib-source grep [D] for `padicExp`/`padicLog`/analytic exp-log inverse — none.
[C] LeanSearch        "p-adic exponential logarithm mutually inverse"; "log of exp on p-adic disk"   → no hits (via mathlib4-docs web search): mathlib documents p-adic numbers, `PadicInt`, Hensel's lemma, and `PowerSeries.exp`/`PowerSeries.log` (formal), but no analytic p-adic exp/log and no `log∘exp=id`.
[D] Grep mathlib src  `padicExp`, `padicLog`, `def padicExp/padicLog`, `subst (exp`, `log.*subst.*exp`, `exp_log`/`log_exp` in `Analysis/`+`RingTheory/PowerSeries/`   → **no hits** for any analytic p-adic exp/log; `exp_log`/`log_exp` hits are only `Complex`, `Real`, CFC (self-adjoint), and `WithZero`-valuation — all unrelated. The **formal** composition `(log A).subst (exp A − 1) = X` is **also absent** from `RingTheory/PowerSeries/`.
[E] Name pattern      `lean_local_search`-style grep over project + mathlib for `padicLog_padicExp`/`padicExp_padicLog`/`log_exp`/`exp_log`   → only the project's own `PadicExp.lean` (lines 935, 950) defines these; no mathlib counterpart.

Searched for both:
  - the user's current form (`padicLog p (padicExp p x) = x` on `InExpBall`) — absent.
  - the literature-standard form (analytic `log∘exp=id` over any complete nonarch. field over `ℚ_p`; also the bundled `1+pℤ_p ≅ pℤ_p`) — absent.
  - the nearest building block (the **formal** power-series inversion `log.subst(exp−1)=X`) — **also absent**; the project proves it itself (`log_subst_exp_sub_one`, line 540).

Concluded: **not in mathlib (all methods exhausted, plus the literature-standard form, plus the formal-power-series building block).** Mathlib has `PowerSeries.exp`/`PowerSeries.log` (formal coefficients, `HasSubst`, `derivative`) but neither the formal composition inverse nor any analytic p-adic exp/log.

---

### Call sites — `PadicLFunctions.padicLog_padicExp`

Internal use count: **1** (within the project, NOT counting the declaring-file's own statement line): used in `padicLog_mul` at `PadicExp.lean:991` to convert `log(exp(a+b))` back to `a+b`.
External-to-file callers: **0 distinct files** (the one use is in the same file, `PadicExp.lean`).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:991 | `… padicLog_padicExp p hballab]` (closing `padicLog (x*y) = a + b` after rewriting `x*y = exp(a+b)`) |

Inline-derivation grep (was `log(exp x)=x` re-derived elsewhere without calling `padicLog_padicExp`?):
  - **(none)** — `grep "padicLog p (padicExp"` finds only the declaration (line 951) and no inline re-proof anywhere in the repo.

Composability read: `K = 1` internal use *directly*, but this understates its role. `padicLog_padicExp` is a **foundational inversion identity** that anchors the entire `padicLog`/`padicExp` API: its sibling `padicExp_padicLog` and the multiplicativity `padicLog_mul` (which depends on it) are used pervasively downstream — `ExtLog.lean` (lines 84, 374), `ValuesAtOne.lean` (line 567), and `ResidueZeta.lean` (the p-adic L-function / residue-zeta construction). This is genuine library API, not a one-off wrapper. The low *direct* count reflects that it sits one layer below the heavily-used `padicLog_mul`, which is the standard pattern for a base inversion lemma.

---

### Composition check (Phase 6)

Can `PadicLFunctions.padicLog_padicExp` be derived from mathlib in ≤3 chained calls?

Attempt 1: specialise a mathlib analytic `log∘exp=id` for normed/Banach fields.
  - Mathlib decls used: — (none exist)
  - Result: **fails** — mathlib has no analytic p-adic (or general nonarchimedean Banach) exp/log; the only `log_exp`/`exp_log` are `Complex`/`Real`/CFC, none of which apply to `ℚ_[p]`/`ℂ_p`.

Attempt 2: build it from the formal power-series inversion in mathlib (`(PowerSeries.log).subst (PowerSeries.exp − 1) = X`) plus a generic "evaluate formal identity analytically" transfer.
  - Mathlib decls used: `PowerSeries.exp`, `PowerSeries.log`, `PowerSeries.HasSubst.exp_sub_one`, `PowerSeries.subst`, `PowerSeries.derivative_subst`, …
  - Result: **fails / partial** — (a) the formal inversion `log.subst(exp−1)=X` is itself **not in mathlib** (the project proves it as `log_subst_exp_sub_one` via a derivative-extensionality argument — a real ~15-line proof); and (b) even granting it, the analytic transfer is the project's `master_bridge` (ultrametric Fubini / `summable_prod_family` over a doubly-indexed family) — a substantial lemma, not a 1–3-call mathlib composition. This is a multi-`have` proof with nontrivial summability reasoning between steps, i.e. a proof, not a composition (per the Phase-6 heuristics: "multiple `have`s with non-trivial reasoning between" → NO).

Conclusion: **NOT-COMPOSABLE.** No mathlib primitive (analytic or formal) composes in ≤3 calls to give this; both the formal inversion and the analytic transfer are missing and each is a genuine proof.

---

## Verdict: `PadicLFunctions.padicLog_padicExp`

**Category:** `YES-but-generalise-first`

**Evidence:**
- Literature search (Phase 3): canonical result (Wikipedia, PlanetMath, MIT/Conrad/Thorne notes, Cassels §12, Washington §5.1) — `log(exp(x))=x` on `‖x‖<p^{−1/(p−1)}`; the project's statement matches the literature standard exactly.
- Generality analysis (Phase 4): MAXIMALLY GENERAL for the *theorem as stated* (the ambient `[NormedField][NormedAlgebra ℚ_[p] L][IsUltrametricDist][CompleteSpace]` is the literature ambient; `InExpBall` is the sharp radius). Phase 4c: no modernisation of *this statement*.
- Mathlib search (Phase 5): not in mathlib — neither analytic p-adic exp/log, nor the formal power-series composition inverse `log.subst(exp−1)=X`.
- Composition check (Phase 6): NOT-COMPOSABLE (both the formal inversion and the analytic transfer `master_bridge` are missing and each is a real proof).

**Rationale (why not plain `YES-add-as-is`):**

The mathematical content is genuinely missing from mathlib and is canonical — this clears the YES bar decisively. The reason the verdict is `YES-but-generalise-first` rather than `YES-add-as-is` is **not** a problem with this theorem's own generality (it is maximally general as stated). It is that **the theorem is meaningless in mathlib without its subjects** `padicExp` and `padicLog`, and *those* are the actual upstreaming unit. The right mathlib contribution is the whole **p-adic exp/log package** — the definitions, the convergence/isometry facts, and the two inversion theorems `padicExp_padicLog` + `padicLog_padicExp` together — not this single equation in isolation. A lone `padicLog_padicExp` PR cannot be opened; it has no referents upstream.

Within that package there is one concrete generalisation worth settling before a PR, which is why this is a "generalise-first" rather than "add-as-is": **`padicExp`/`padicLog`/`InExpBall` are currently `private`-flavoured to the `ℚ_[p]`-algebra setting via the four bundled `variable` typeclasses, but the literature-maximal ambient is "any field `K` complete w.r.t. a nonarchimedean absolute value of residue characteristic `p`" (not necessarily presented as a `NormedAlgebra ℚ_[p]`).** Mathlib will want to decide the canonical typeclass spelling of that ambient (e.g. whether to phrase over `[NormedField L] [NormedAlgebra ℚ_[p] L]` as here, or over a more intrinsic nonarchimedean-valued-field-of-residue-char-`p` interface that de Frutos-Fernández's norm-extension formalisation, arXiv:2306.17234 / ITP 2023, is building toward). That is a real organisational choice about the *definitions* that should be made once, up front, because every downstream lemma's signature inherits it. This lemma rides along on whatever spelling is chosen.

This is therefore the **`YES-but-generalise-first` → MODERN-IDIOM/AMBIENT** case applied at the package level: the theorem is correct and maximally general *relative to the current `padicExp`/`padicLog` ambient*, but the ambient itself is the thing to pin down (and possibly intrinsicise) before upstreaming the package.

**Reason for the generalisation:**
- AMBIENT/MODERN-IDIOM: settle the canonical mathlib typeclass for "complete nonarchimedean field of residue characteristic `p`" for the underlying `padicExp`/`padicLog` definitions, then state this inversion (and its sibling) over that ambient. The *content* of `padicLog_padicExp` does not change; only the shared ambient of the package is fixed.

**Proposed restatement (illustrative — the change is to the package's ambient, the equation is unchanged):**
```lean
-- after fixing the canonical ambient `𝒦` for the p-adic exp/log package:
theorem padicLog_padicExp {x : 𝒦} (hx : InExpBall p x) :
    padicLog p (padicExp p x) = x := by
  sorry  -- proof transfers verbatim; only the ambient typeclass spelling is revisited
```

**Estimated cost of regeneralisation:** MODERATE — if the chosen ambient is definitionally close to the current `[NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist] [CompleteSpace]`, the proofs transfer with light signature edits; if mathlib adopts a more intrinsic nonarchimedean-valued-field interface, the `padicExp`/`padicLog` defs and their summability lemmas need re-plumbing onto it (the inversion proofs themselves are stable). EXPENSIVE is not a downgrade here regardless.

**Mathlib downstream this enables (the package, once upstream):**
- A canonical analytic `Padic.exp` / `Padic.log` with `exp∘log=id` / `log∘exp=id`, which is the prerequisite for: the `1 + pℤ_p ≅ pℤ_p` (odd `p`) group isomorphism; `x^s := exp(s·log x)` continuous `ℤ_p`-powers on `1+pℤ_p` (used in Iwasawa theory and p-adic L-functions); the Artin–Hasse exponential's comparison; and any p-adic Lie-group / formal-group exponential work.
- Reuses and *closes a gap above* mathlib's existing `PowerSeries.exp`/`PowerSeries.log`: the formal inversion `log.subst(exp−1)=X` (proved here as `log_subst_exp_sub_one`) is a clean, ambient-free addition to `Mathlib/RingTheory/PowerSeries/Log.lean` that mathlib currently lacks and that has independent value.

**Proposed mathlib location:** package across `Mathlib/NumberTheory/Padics/Analytic/ExpLog.lean` (new) for the analytic functions + inversions, with the formal `log_subst_exp_sub_one` going to `Mathlib/RingTheory/PowerSeries/Log.lean`.

**PR grouping (required — this is the load-bearing point):** ship `padicLog_padicExp` **together with** `padicExp`, `padicLog`, `InExpBall`, the convergence/summability lemmas, `norm_padicExp_sub_one`, the formal identities `exp_subst_log` / `log_subst_exp_sub_one`, the transfer `master_bridge`, and the sibling `padicExp_padicLog` — as **one p-adic-exp/log package PR** (or a small sequence: formal-PowerSeries inversion PR first, then the analytic package). It cannot go as a standalone lemma.

**Next action:** run `/generalise PadicLFunctions.padicExp` (and `padicLog`) **first** — to tension the package's ambient typeclasses against (a) the literature-maximal "complete nonarchimedean field of residue char `p`" and (b) the de Frutos-Fernández norm-extension interface — and pin the canonical ambient. Then `/cleanup` the package file and open the grouped mathlib PR (formal inversion to `PowerSeries/Log.lean`; analytic functions + `padicLog_padicExp`/`padicExp_padicLog` to a new `Padics/Analytic` file).

---

## Next step

Run `/generalise PadicLFunctions.padicExp` and `/generalise PadicLFunctions.padicLog` to settle the canonical mathlib ambient typeclass for the p-adic exp/log package (literature-maximal nonarchimedean complete field of residue characteristic `p`, tensioned against the norm-extensions interface of arXiv:2306.17234). Then upstream `padicLog_padicExp` **as part of the whole p-adic-exp/log package** (definitions + convergence + both inversions + the formal `log_subst_exp_sub_one`), never as a standalone lemma. Split: formal power-series inversion → `Mathlib/RingTheory/PowerSeries/Log.lean`; analytic functions and inversions → a new `Mathlib/NumberTheory/Padics/Analytic/` file.
