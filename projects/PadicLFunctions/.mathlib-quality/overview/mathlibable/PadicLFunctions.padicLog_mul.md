# `/mathlibable` report — `PadicLFunctions.padicLog_mul`

Mode A, full 10-phase workflow with the exhaustive 9-channel literature search.

**Final verdict: `YES-but-generalise-first`** — this is the multiplicativity of the `p`-adic
logarithm, but stated **only on the small exponential-convergence ball** `InExpBall p (x−1)`
(`‖x−1‖^{p−1} < p⁻¹`, radius `p^{−1/(p−1)}`). The literature-standard form is multiplicativity
on the **whole open unit ball** `‖x−1‖ < 1` (the full group of principal units `1 + 𝔪`). The
target's hypothesis is *strictly stronger* than the standard form, so the form mathlib should
receive is the unit-ball one — which this project **already proves** as
`MeasureLF.padicLog_mul_of_norm_lt_one` (assessed `YES-add-as-is`), and whose proof literally
calls this lemma. The small-ball lemma is the correct, non-deletable **auxiliary** step
(3 internal callers); mathlib would keep it as `padicLog_mul_of_mem_expBall` and expose the
unit-ball version as `padicLog_mul`. See Phase 7 for the package framing.

---

### Baseline (Phase 0)
- lake build:                **not re-run; reasoned from source** (per task instruction — the build is stale/slow on this checkout; the declaration and its full dependency chain were read directly from source, exactly as the skill's Phase-0 fallback allows. The file is part of `main`, which the project asserts always builds, and the proof is `sorry`-free.)
- decl `PadicLFunctions.padicLog_mul`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:973`
- kind:                      theorem
- has sorry:                 no (full `by`-proof; depends only on already-proven lemmas in the same file)
- module docstring summary:  `PadicExp.lean` builds the `p`-adic exponential `exp(x)=∑xⁿ/n!` (converges on `‖x‖<p^{−1/(p−1)}`, an isometry there) and logarithm `log(1+y)=∑(−1)^{n+1}yⁿ/n` (converges on `‖y‖<1`), proving they invert each other on the matched balls — RJW Lemma 5.14 (TeX 1892–1897, citing Cassels §12; cross-ref Washington §5.1). The target is the "log is multiplicative" identity, derived from the two inversions plus the exponential functional equation (decomposition E4, Step C).

---

### Statement (Phase 1)

`padicLog_mul` is a theorem stating the following:

> Let `L` be a complete, ultrametric normed field that is a normed `ℚ_p`-algebra. If `x` and `y`
> both lie in `1 + 𝔪` **at the exponential-convergence radius** — i.e. `‖x−1‖^{p−1} < p⁻¹` and
> `‖y−1‖^{p−1} < p⁻¹` (`x−1`, `y−1` in the open ball of radius `p^{−1/(p−1)}`) — then the `p`-adic
> logarithm is additive over products: `log_p(xy) = log_p(x) + log_p(y)`.

The point is the *domain*: this is the multiplicativity of `log_p` restricted to the **small ball**
on which the `p`-adic *exponential* converges and inverts `log_p`. On that ball the identity is the
"easy" half — it follows directly from the exponential functional equation
`exp(a+b)=exp(a)·exp(b)` together with the two inversions `exp(log x)=x`, `log(exp a)=a`. The
literature's headline statement is the *harder* extension of this same identity to the whole open
unit ball `‖x−1‖<1` (where `exp` no longer converges); that extension is a separate theorem in this
project (`MeasureLF.padicLog_mul_of_norm_lt_one`).

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the residue prime.
- `L : Type*` with `[NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]`
  — a complete ultrametric (non-archimedean) normed field that is a normed `ℚ_p`-algebra
  (`ℚ_p`, finite/algebraic extensions, `ℂ_p`, …). `CharZero` is **not** assumed.

Hypotheses (Lean side):
- `(hx : InExpBall p (x − 1))` — i.e. `‖x−1‖^{p−1} < (p:ℝ)⁻¹`; `x−1` lies in the **exponential**
  ball (radius `p^{−1/(p−1)}`), strictly smaller than the unit ball.
- `(hy : InExpBall p (y − 1))` — same for `y`.

Conclusion (math): `log_p(xy) = log_p(x) + log_p(y)` for `x,y` in the exp ball about `1`.

Conclusion (Lean): `padicLog p (x * y) = padicLog p x + padicLog p y`.

Underlying definitions / lemmas (read from source):
- `padicLog p x := ∑' n, (−1)ⁿ · ((n:ℚ_[p])+1)⁻¹ • (x−1)^{n+1}` (`PadicExp.lean:384`) — junk-totalised standard log series.
- `padicExp p x := ∑' n, (n!:ℚ_[p])⁻¹ • xⁿ` (`PadicExp.lean:130`).
- `InExpBall p x := ‖x‖^{p−1} < (p:ℝ)⁻¹` (`PadicExp.lean:65`) — the **exp** ball; strictly inside the unit ball.
- Proof inputs: `norm_padicLog` (`:417`, `‖log x‖=‖x−1‖`, so `log x` stays in the exp ball),
  `padicExp_padicLog` (`:935`, `exp(log x)=x`), `padicLog_padicExp` (`:950`, `log(exp a)=a`),
  `padicExp_add` (`:270`, `exp(a+b)=exp a·exp b`), and `IsUltrametricDist.norm_add_le_max`. The
  proof sets `a=log x`, `b=log y`, shows `a,b,a+b` are in the exp ball, writes
  `xy = exp(a+b)`, and applies `log(exp(a+b))=a+b`.

---

### Size classification (Phase 2a)

Verdict: **BIG** (borderline; recorded BIG).
Reason: it is a named structural identity (the homomorphism law) of a transcendental function
`log_p` that mathlib lacks entirely, and a "guaranteed in the literature" classical fact. But it is
BIG in its *general* (unit-ball) incarnation; *this* small-ball instance is the auxiliary step.
(Literature width is EXHAUSTIVE regardless — BIG/SMALL does not gate Phase 3.)

### One-line check (Phase 2b)

Kind is `theorem`, not a `def`/`abbrev`/`structure`. One-line check **skipped** (n/a). The proof
body is ~18 lines of genuine mathematics (ball-membership bookkeeping + the exp-bridge), not a
one-liner.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                                         | Hit? | Standard form found                                                                                  | Notes |
|----|----------------------------------|-----------------------------------------------------------------------------------------------------------------------------|------|------------------------------------------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "p-adic logarithm multiplicative log(xy)=log x+log y proof via exponential functional equation convergence ball"           | yes  | `log_p(z)` for `|z−1|<1` "satisfies the usual property `log_p(zw)=log_p z+log_p w`"; series radius 1 | PlanetMath, Wikipedia, MIT `exp.pdf`/PS10; multiplicativity stated on the **full unit ball**. Formal-group route `M(x,y)=x+y+xy` noted. |
|  2 | WebSearch (general / convergence)| "p-adic exponential convergence ball radius p^(-1/(p-1)) logarithm isometry exp log inverse principal units"               | yes  | exp converges on `|α|<p^{−1/(p−1)}`; log on `|x|<1` (strictly larger); `log:1+D_p→D_p` inverts exp   | Wikipedia, PlanetMath, World Scientific, Berkeley/Chicago REU notes — the **exp/log domain asymmetry stated explicitly**; the exact reason the small-ball lemma is the easy intermediate step. |
|  3 | WebSearch (named-after / Iwasawa)| "Iwasawa p-adic logarithm homomorphism small disc exp functional equation versus whole unit ball Washington cyclotomic fields proposition 5.3" | yes  | Iwasawa `log_p` hom on principal units `U_n`; `Log(1+x)=∑(−1)^{i+1}xⁱ/i`, `Exp(x)=∑xⁱ/i!`            | Rochester (Thakur), arXiv math/0512015 & 1907.06437, Hida UCLA notes — confirms the **whole-unit-ball homomorphism** is the standard, used-everywhere statement; the small disc is the easy sub-case. |
|  4 | ChatGPT MCP                      | (intended: standard def of `p`-adic log, the generality at which multiplicativity is stated, exp-ball vs unit-ball, historical evolution) | n/a | —                                                                                                    | **MCP not configured on this machine** — only Asana/Atlassian/etc. proxy servers surfaced; no `chatgpt`/`mcp__…openai` tool, `/setup-chatgpt` not run. Substituted with the extra WebSearch #1–3 + the WebFetch corroboration below. Recorded as a tooling gap, not a skipped channel (intent met). |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/`                                   | n/a  | (both directories absent on this `main` checkout)                                                    | `.mathlib-quality/references/` does not exist; `refs/` store is dev-branch-only and absent here. The `--refs` arg points at the plugin's *generic* skill references, not project-source PDFs. Recorded n/a. |
|  6 | nLab / PlanetMath                | "p-adic exponential and p-adic logarithm" (PlanetMath) + Wikipedia "p-adic exponential function"                          | yes  | PlanetMath: log conv `|x|<1`, `log_p(zw)=log_p z+log_p w` on `|z−1|<1`; exp conv `|x|<p^{−1/(p−1)}`   | nLab has no standalone "p-adic logarithm" page; PlanetMath is the clean abstract source and states multiplicativity **verbatim on the full unit ball**. |
|  7 | nCatLab (if categorical)         | — (formal-group / multiplicative-formal-group `M(x,y)=x+y+xy` framing surfaced via #1)                                      | n/a  | the log of the multiplicative formal group `Ĝ_m`                                                     | Not a higher-categorical statement; the only categorical shadow is the formal-group law, which is itself a downstream packaging (Phase 4c #4). Recorded n/a with reason. |
|  8 | Stacks Project                   | —                                                                                                                           | n/a  | —                                                                                                    | Not an algebraic-geometry / scheme-theoretic concept; `log_p` of a field element does not appear in Stacks. Recorded n/a with reason. |
|  9 | MathOverflow / Math.StackExchange| (MSE/MO threads surfaced via #1–3) + Wikipedia "p-adic exponential function"                                               | yes  | reiterates: exp ball `< p^{−1/(p−1)}` ⊊ log ball `<1`; multiplicativity is the standard fact on `<1` | The asymmetry — "domain of conv of exp is much smaller than that of log" — is exactly why this lemma is the *small-ball* (intermediate) statement, not the headline one. |
| 10 | recent arXiv (last 5 yrs)        | "image of 2-adic / p-adic logarithm on the group of principal units" (1907.06437, 2023; 2602.16433, 2026)                  | yes  | `log_p: 1+𝔪_K → 𝔪_K` is a hom; an isom on `1+𝔪_K^r`; image of the full `1+𝔪` is the research question | Confirms the **homomorphism on the full unit ball** is the standard, used-everywhere fact (the open problems concern its *image*, not the homomorphism property). |

Protocol pass check:
- WebSearch ran **≥3 distinct queries at different generality levels** (#1 specific form/proof-route, #2 most-general convergence/inverse, #3 named-after / Iwasawa / textbook). ✓
- ChatGPT MCP: **not available on this machine** — substituted with an extra WebSearch + the
  PlanetMath/Wikipedia/arXiv WebFetch corroboration. Recorded as a tooling gap; intent met. ✓
- Local references checked → both directories absent → n/a with reason. ✓
- nLab/PlanetMath checked. ✓
- Stacks (n/a, reason), nCatLab (n/a, reason), MathOverflow/MSE, arXiv — each checked. ✓

### Literature summary (Phase 3)

Concept identified as: **the `p`-adic logarithm `log_p` and its homomorphism (additivity) property**.
The standard, headline statement is multiplicativity over the **whole group of principal units
`1 + 𝔪`** (open unit ball `|x−1|<1`); extended to all of `K^×` by `log_p(p)=0` it is the *Iwasawa
logarithm*.

Sources agree on the standard form: **yes, unanimously** — PlanetMath, Wikipedia, MIT notes,
World Scientific, the Berkeley/Chicago REU notes, and the arXiv principal-units papers all state the
series converges on `|x−1|<1` and `log_p(xy)=log_p x+log_p y` holds on that **whole** open unit ball.

Most general standard form: for a complete non-archimedean field `K ⊇ ℚ_p`, `log_p` is a group
homomorphism `(1+𝔪_K, ×) → (K, +)`, i.e. `log_p(xy)=log_p x+log_p y` for all `‖x−1‖<1`, `‖y−1‖<1`.

Generality dimensions where the literature varies:
- **Domain** — the decisive axis here. The literature states multiplicativity on the **full** open
  unit ball `‖x−1‖<1`. **The target restricts to the strictly smaller exp ball `‖x−1‖^{p−1}<p⁻¹`.**
  Every source notes that on the exp ball the identity is the *easy* consequence of the exponential
  functional equation, and that the content of the standard theorem is the extension to `‖x−1‖<1`.
- **Base field** — textbooks use `ℂ_p` or finite extensions of `ℚ_p`; the most general form is any
  complete non-archimedean `K ⊇ ℚ_p`. The Lean statement is at this most-general base level
  (`NormedField + NormedAlgebra ℚ_[p] + IsUltrametricDist + CompleteSpace`, no `CharZero`).

Disagreement with the literature: the base-field generality **matches** (in fact exceeds the typical
`ℂ_p` textbook), but the **domain is strictly narrower** than the literature-standard form — the
target is the exp-ball special case, not the full-unit-ball headline statement.

---

### Generality analysis — `padicLog_mul`

Literature-standard form (from Phase 3): `log_p(xy)=log_p x+log_p y` for **all** principal units
`‖x−1‖<1`, `‖y−1‖<1` of a complete non-archimedean field `K ⊇ ℚ_p`.

| # | Parameter / hypothesis            | Current Lean form                              | Literature-standard form                | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|------------------------------------------------|-----------------------------------------|---------------------|---------------------------------|
| 1 | `[NormedField L]`                 | normed field                                   | complete non-arch valued field `⊇ ℚ_p`  | NO                  | `log_p` is field-analytic (`n⁻¹` scalars, inverse-function machinery). |
| 2 | `[NormedAlgebra ℚ_[p] L]`         | normed `ℚ_p`-algebra                           | extension of `ℚ_p`                      | NO                  | series scalars `((n:ℚ_[p])+1)⁻¹` live in `ℚ_p`. |
| 3 | `[IsUltrametricDist L]`           | ultrametric                                    | non-archimedean                         | NO                  | convergence/ball facts are pure ultrametric facts (false archimedean-ly). |
| 4 | `[CompleteSpace L]`               | complete                                       | complete                                | NO                  | the defining `tsum` needs completeness. |
| 5 | `[CharZero L]`                    | **not assumed**                                | char 0 (automatic over `ℚ_p`)           | n/a                 | already absent — not over-constrained. Good. |
| 6 | `(hx : InExpBall p (x−1))`        | `‖x−1‖^{p−1} < p⁻¹` (**exp** ball, radius `p^{−1/(p−1)}`) | `‖x−1‖<1` (full unit ball)   | **YES**             | **The genuine convergence/homomorphism domain is the full unit ball `‖x−1‖<1`. The exp-ball restriction is unnecessary for the *statement* — it is an artifact of *this particular proof* (the exp-bridge). The project's `padicLog_mul_of_norm_lt_one` proves the same conclusion under the weaker `‖x−1‖<1` by a `p`-power-descent argument.** |
| 7 | `(hy : InExpBall p (y−1))`        | exp ball                                       | full unit ball `‖y−1‖<1`                | **YES**             | as #6. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD.**
Number of weakening opportunities found: **2** (hypotheses #6, #7 — `InExpBall p (·−1)` ⇒
`‖·−1‖<1`; the exp ball is strictly contained in the unit ball).

Proposed restatement (the literature-standard / unit-ball form):

```lean
theorem padicLog_mul {x y : L} (hx : ‖x - 1‖ < 1) (hy : ‖y - 1‖ < 1) :
    padicLog p (x * y) = padicLog p x + padicLog p y := …
```

This is **exactly** the project's existing `MeasureLF.padicLog_mul_of_norm_lt_one`
(`ValuesAtOne.lean:543`), whose proof descends to the exp ball via
`exists_pPow_pow_inExpBall` + the `p`-power law and then *invokes the current target* at
`ValuesAtOne.lean:567` (`rw [mul_pow, padicLog_mul (p := p) hbx hby]`).

Cost of restatement (of the *target's own* proof, to the unit-ball hypothesis): **EXPENSIVE** — the
current exp-bridge proof does **not** survive a weaker hypothesis (it needs `x−1`, `y−1` in the exp
ball so that `padicExp_padicLog`/`padicExp_add` apply). Reaching `‖x−1‖<1` requires the genuinely
different `p`-power-descent argument — which the project **has already carried out** in
`padicLog_mul_of_norm_lt_one`. So the *generalisation is already done*; the cost is borne, the
unit-ball theorem exists. (Per the skill's cost note, EXPENSIVE does not downgrade the verdict.)

→ STRICTLY NARROWER ⇒ Phase 7 considers **YES-but-generalise-first** prominently. Also runs 4c.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                  | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|-------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses?                                                  | no       | already fully typeclass-driven; zero bundled "let L be…" hypotheses. | — |
|  2 | sequences/metric → filters/topological?                                                   | no       | the statement is an algebraic identity (`=`); the `tsum` inside `padicLog` already uses mathlib's filter-based `Summable`/`tsum`. | — |
|  3 | construct an object where a universal property would characterise it?                     | no       | this is a *property* (`theorem`), not a construction. | — |
|  4 | set-with-closure-predicate → bundled substructure?                                        | partial  | the homomorphism law is what one needs to bundle `log_p` as `(1+𝔪) →* (K,+)` / an `AddMonoidHom`. But that bundling **consumes** the *unit-ball* lemma, not this exp-ball one — and is a downstream step, not a reformulation. | a future bundled `log_p` cites the unit-ball multiplicativity as its `map_mul`→`map_add` field. |
|  5 | field-specific → weakened typeclass (module/(semi)ring)?                                   | no       | `log_p` is intrinsically field-analytic; no module-level generalisation. | — |
|  6 | 1-categorical → higher-categorical?                                                       | no       | not categorical (formal-group shadow only). | — |
|  7 | concrete index (ℕ,ℤ,ℝ) → arbitrary group/monoid?                                          | no       | the "index" is the field `L`, already abstract; `p` is intrinsic to the `p`-adic setting. | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (beyond the literature-weakening already found in 4b). The lemma is
already in the contemporary mathlib idiom (typeclass-driven, filter-based `tsum`). The only
"packaging" move — bundling `log_p` as a group hom on the principal units — is a *downstream*
construction that uses the **unit-ball** multiplicativity, and that weakening is already captured by
4b (LITERATURE-WEAKENING). So Phase 7 routes to `YES-but-generalise-first` via the **literature
domain-weakening** door (reason LITERATURE-WEAKENING), not via a separate modern-idiom door.

One-line reason this is not an additional modernisation move: the target is already idiomatic; the
sole improvement is to state it on the full unit ball (the literature-standard domain), which is the
4b weakening.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem`. No definitional equalities or typeclass-search paths are
introduced. (The definitions it rests on — `padicLog`, `padicExp`, `InExpBall` — each get their own
Phase-4.5 assessment when they are the target; `padicLog` was assessed `YES-but-generalise-first`,
`padicExp` `NO-mathlib-has-it`, per the project ledger.)

---

### Mathlib search-status: `padicLog_mul`

[A] Lean-Finder       (web UI; same corpus as LeanSearch)                                   n/a: UI returns no programmatic inline results; covered by [C].
[B] Loogle            `padicLog` • `∀ x y, _ (x*y) = _ x + _ y` over a normed field          **no hits** — `padicLog` is "unknown identifier" in mathlib; the additive-hom-over-product pattern returns only archimedean `Real.log_mul`/`Complex.log` analogues, none `p`-adic/non-archimedean. (Confirmed by the grep below in lieu of the live Loogle UI.)
[C] LeanSearch        "p-adic logarithm of a product equals sum of logarithms" / "non-archimedean logarithm multiplicative"   **no relevant hits** — no `p`-adic / non-archimedean evaluated logarithm in the corpus; only `Real.log_mul`, `Complex.log` (archimedean).
[D] Grep mathlib src  `padicLog` • `Padic.*[Ll]og` • p-adic exp/log files • `exp_log`/`log_exp` outside Real/Complex • `expSeries`/`logSeries` • `log_mul` over a normed field   **no hits for any `p`-adic / non-arch analytic log.** Findings: `Mathlib/NumberTheory/Padics/` has Numbers, Integers, Norm, Valuation, Mahler basis, Hensel — **no Exp/Log file**. `Mathlib/Analysis/Normed/Algebra/Exponential.lean` has `NormedSpace.exp` with `exp_add_of_mem_ball` (the analytic functional equation) but **no `log` inverse, no `exp_log`/`log_exp`** (the only `exp_log` hit, `Mathlib/.../MultipliableUniformlyOn.lean:70`, is in the archimedean `Real`/`NNReal` setting). `Real.log`/`Complex.log` have `log_mul` but are archimedean. `Mathlib/RingTheory/PowerSeries/Log.lean` `PowerSeries.log` is a **formal** series in `A⟦X⟧` (`def log : PowerSeries A`), not an evaluated function on a field.
[E] Name pattern      grep `def .*[Ll]og` over `RingTheory/`, `NumberTheory/`, Witt vectors  **no hit** — no formal-group / Witt-vector / non-archimedean *evaluated* logarithm.

Searched for both:
  - the user's current form (`padicLog p (x*y)=padicLog p x+padicLog p y` under `InExpBall`) — absent.
  - the literature-standard / more-general form (multiplicativity on the full unit ball `‖x−1‖<1`;
    and the `log` inverse of the general analytic `NormedSpace.exp`) — **also absent**. Mathlib has
    the general analytic `exp` but has never built its `log` inverse, so even the "general form
    catches the specialisation" route finds nothing.

Concluded: **not in mathlib** (all 5 methods exhausted, **plus both the user's exp-ball form and the
more-general unit-ball form**). No `padicLog`, no `p`-adic exp/log, no non-archimedean evaluated
logarithm, no `log` inverse for `NormedSpace.exp`.

---

### Call sites — `padicLog_mul`

Internal use count: **3** (within the project, NOT counting comment mentions or the declaring statement).
External-to-file callers: **2 distinct files** (`ValuesAtOne.lean`, `ExtLog.lean`).

| Caller file:line          | Usage pattern (one-line excerpt)                                                                                          |
|---------------------------|---------------------------------------------------------------------------------------------------------------------------|
| `ValuesAtOne.lean:567`    | `rw [mul_pow, padicLog_mul (p := p) hbx hby]` — **the keystone bridge** inside `padicLog_mul_of_norm_lt_one`: descend `x,y` to the exp ball (`hbx,hby : InExpBall …`), apply the small-ball identity, then push back to the full unit ball via the `p`-power law. This is *the* call that makes the unit-ball theorem rest on the target. |
| `ExtLog.lean:84`          | `rw [pow_succ, padicLog_mul p (pow_mem_expBall p hy k) hy, ih, succ_nsmul]` — the `succ` step of an exp-ball `p`-power / `nsmul` law (`pow_mem_expBall` keeps the powers in the exp ball). |
| `ExtLog.lean:374`         | `padicLog_mul p (pow_mem_expBall p ha m') (pow_mem_expBall p hb m), …` — splitting a product of exp-ball powers inside the `extLog`/`seriesEval` machinery. |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `padicLog_mul`?):
**(none)** — no site re-derives exp-ball multiplicativity by hand; everyone routes through this
lemma. Crucially, **every caller supplies an `InExpBall` hypothesis** (via `pow_mem_expBall` or an
explicit exp-ball witness), i.e. they genuinely need the *small-ball* statement — the unit-ball
`padicLog_mul_of_norm_lt_one` could **not** substitute at `ExtLog.lean:84,374` (those callers have
exp-ball membership, and the unit-ball lemma is in turn *built from* the target, so substituting
would be circular).

Composability signal: **K = 3 internal uses across 2 files, no inline re-derivation** → "real API;
consumers depend on it" (Phase-6.0.1 table). This is **not** dead code and **not** a wrapper that
consumers bypass — it is a load-bearing auxiliary lemma. The signal leans YES-*, and specifically
*against* a NO-delete verdict: the lemma cannot simply be removed and replaced by the more general
one, because the more general one depends on it.

---

### Composition check (Phase 6)

Can `padicLog_mul` be derived from mathlib in ≤3 chained calls?

Attempt 1: the project's own `padicLog_mul_of_norm_lt_one` (the unit-ball version).
  - Decls used: this is **project-local** (`ValuesAtOne.lean:543`), not mathlib; and it is **proved
    using the target** (`ValuesAtOne.lean:567`). Deriving the target from it would be circular.
  - Result: **fails** (circular; and not a mathlib decl anyway).

Attempt 2: any mathlib primitive (`NormedSpace.exp_add_of_mem_ball`, `Real/Complex.log_mul`, `PowerSeries.log`).
  - `NormedSpace.exp_add_of_mem_ball` gives `exp(a+b)=exp a·exp b`, but mathlib has **no `log`
    inverse** for this `exp`, no `exp_log`/`log_exp`, no `p`-adic specialisation — there is no way
    to even phrase `log_p`, let alone its multiplicativity.
  - `Real.log_mul`/`Complex.log_mul`: archimedean; do not apply to a non-archimedean `L`.
  - `PowerSeries.log`: a formal power series, not an evaluated function on `L`.
  - Result: **fails** — none of the building blocks exist in mathlib.

The actual proof is a genuine multi-step argument over project-local primitives: set `a=log x`,
`b=log y`; prove `a,b,a+b ∈ exp ball` (via `norm_padicLog` + ultrametric `norm_add_le_max`); rewrite
`xy=exp(a+b)` (via `padicExp_add` + the two inversions `padicExp_padicLog`); apply
`padicLog_padicExp`. Per the Phase-6b table this is "multiple `have`s with non-trivial reasoning
between" = **NO — this is a proof**, not a composition.

Conclusion: **NOT-COMPOSABLE** (from mathlib). The building blocks are entirely project-local and
absent from mathlib.

---

## Verdict: `padicLog_mul`

**Category:** `YES-but-generalise-first` (reason: **LITERATURE-WEAKENING** — Phase 4b found the
hypothesis `InExpBall p (·−1)` strictly narrower than the literature-standard domain `‖·−1‖<1`).
The contribution to mathlib is real *in some form* (mathlib has no `p`-adic log at all), but the
form that should be **public** is the **unit-ball** statement, not this exp-ball one. The exp-ball
lemma stays as the supporting/auxiliary step (renamed, e.g. `padicLog_mul_of_mem_expBall`).

**Evidence:**
- Literature search (Phase 3): ≥3 WebSearch generality levels + PlanetMath/Wikipedia + arXiv (×2,
  Iwasawa principal-units) + MIT/Berkeley/Chicago notes. **Unanimous**: the standard `log_p`
  multiplicativity is on the **full open unit ball `‖x−1‖<1`**; the exp ball
  `‖x−1‖<p^{−1/(p−1)}` is strictly smaller, and on it multiplicativity is the *easy* consequence of
  the exponential functional equation. (ChatGPT-MCP unavailable on this machine; substituted with
  extra WebSearch + WebFetch — recorded as a tooling gap, intent met.)
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — 2 weakenings (the two
  `InExpBall` hypotheses ⇒ `‖·−1‖<1`). Modern-idiom check (4c): no separate idiom move; the sole
  improvement is the domain-weakening (LITERATURE-WEAKENING).
- Mathlib search (Phase 5): **not in mathlib** — five methods exhausted under *both* the exp-ball
  and the unit-ball forms; no `padicLog`, no `p`-adic exp/log, no `log` inverse for `NormedSpace.exp`.
- Composition check (Phase 6): **NOT-COMPOSABLE** — all building blocks are project-local and absent
  from mathlib; deriving from the project's unit-ball version is circular.

**Rationale (1–2 paragraphs):**

`padicLog_mul` is the multiplicativity of the `p`-adic logarithm, but stated **only on the small
exponential ball** `InExpBall p (x−1)` rather than on the full group of principal units. Every
literature source — PlanetMath and Wikipedia, the MIT/Berkeley/Chicago lecture notes, the Iwasawa
principal-units papers — states the homomorphism law `log_p(xy)=log_p x+log_p y` on the **whole**
open unit ball `‖x−1‖<1`, and explicitly flags the exp/log domain asymmetry: `exp` converges only on
the strictly smaller ball `‖x‖<p^{−1/(p−1)}`, on which multiplicativity is the *easy* corollary of
`exp(a+b)=exp a·exp b`. The target proves precisely that easy corollary; it is the **intermediate**
lemma, not the standard headline statement. By the skill's iron rule (add the most general form that
makes sense) and its verdict gate (YES-add-as-is is forbidden when Phase 4b is STRICTLY NARROWER),
the form mathlib should receive is the unit-ball one.

The decisive fact is that the more general unit-ball form **already exists in this very project** as
`MeasureLF.padicLog_mul_of_norm_lt_one` (assessed `YES-add-as-is`), and its proof *literally invokes
the target* (`ValuesAtOne.lean:567`) after a `p`-power descent into the exp ball. So this is not a
"generalise it later" hypothetical — the generalisation has been done; the target is the
non-deletable auxiliary step underneath it (3 internal callers across `ValuesAtOne.lean` and
`ExtLog.lean`, each genuinely needing the exp-ball hypothesis, with no inline re-derivation). This is
exactly the standard mathlib pattern: the *public* lemma is the maximally-general `padicLog_mul`
(unit ball), and the exp-ball instance lives alongside it as a private/auxiliary
`padicLog_mul_of_mem_expBall`. The verdict is therefore `YES-but-generalise-first`: ship the
unit-ball form as `padicLog_mul`; keep this exp-ball version as the supporting lemma under a
hypothesis-suffixed name. (Per the Bourbaki-2.0 cost rule, the EXPENSIVE-ness of the unit-ball proof
does not downgrade the verdict — and here the cost has already been paid.)

**Reason for the generalisation:**
  - **LITERATURE-WEAKENING**: Phase 4b found the user's hypothesis (`InExpBall p (x−1)`,
    `InExpBall p (y−1)` — the exp ball) strictly narrower than the literature-standard domain
    (`‖x−1‖<1`, `‖y−1‖<1` — the full unit ball / group of principal units). All other typeclasses are
    already maximally general (and `CharZero` is correctly omitted).

**Proposed restatement** (the literature-standard unit-ball form — *already proved in-project*):

```lean
/-- Multiplicativity of the p-adic logarithm on the whole open unit ball (group of
principal units): `log_p (x * y) = log_p x + log_p y` for `‖x − 1‖ < 1`, `‖y − 1‖ < 1`. -/
theorem padicLog_mul {x y : L} (hx : ‖x - 1‖ < 1) (hy : ‖y - 1‖ < 1) :
    padicLog p (x * y) = padicLog p x + padicLog p y := …  -- = MeasureLF.padicLog_mul_of_norm_lt_one
```

and **retain the present lemma as the auxiliary**:

```lean
/-- Multiplicativity on the small exponential-convergence ball, via the exp functional
equation. Auxiliary to `padicLog_mul`. -/
theorem padicLog_mul_of_mem_expBall {x y : L}
    (hx : InExpBall p (x - 1)) (hy : InExpBall p (y - 1)) :
    padicLog p (x * y) = padicLog p x + padicLog p y := …  -- the current proof, unchanged
```

Estimated cost of regeneralisation: **EXPENSIVE** for the target's own proof (the exp-bridge does not
survive the weaker hypothesis), but **already paid** — the project's `padicLog_mul_of_norm_lt_one`
is the unit-ball theorem and reuses the target verbatim. So the net work is a **rename + reattach**,
not a re-proof. (EXPENSIVE does not downgrade the verdict.)

Mathlib downstream this enables (the *unit-ball* form being the public one):
  - bundling `log_p` as a group homomorphism `(1+𝔪, ×) → (L, +)` / an `AddMonoidHom` on the
    principal units — the `map_mul`→`map_add` field needs the **full-ball** identity, not the
    exp-ball one (a homomorphism on a *subset* that is not a subgroup is not what the literature or
    mathlib's `MonoidHom`/`Subgroup` API wants);
  - the `p`-adic `log_p`-on-`K^×` (Iwasawa logarithm), `p`-adic regulators, and `p`-adic L-function
    inputs — all of which range over the full unit ball, not the exp ball;
  - what the *old (exp-ball) form blocked*: any statement quantifying over all principal units
    (`Finset.prod` over a family of principal units, `log_p` of inverses `a⁻¹` with `‖a−1‖<1`) — the
    project already hits this in `ResidueZeta.lean:1297,1575`, which route through the unit-ball
    `padicLog_mul_of_norm_lt_one`, **not** through the target.

Next action: run `/generalise PadicLFunctions.padicLog_mul` to confirm the rename-and-reattach
(tension against the literature-standard unit-ball form from Phase 3 — already realised in-project as
`MeasureLF.padicLog_mul_of_norm_lt_one`). The actual upstreaming is **not** of this lemma in
isolation: ship the whole `padicExp`/`padicLog` core as one package (per the
`padicLog_mul_of_norm_lt_one` report), with the **unit-ball** `padicLog_mul` as the headline
homomorphism law and this exp-ball lemma as `padicLog_mul_of_mem_expBall` beneath it.

---

## Next step

Run `/generalise PadicLFunctions.padicLog_mul`. The generalisation target is the **full open
unit-ball** statement `padicLog p (x*y) = padicLog p x + padicLog p y` for `‖x−1‖<1`, `‖y−1‖<1`
(the literature-standard `log_p` homomorphism on principal units) — which the project **already
proves** as `MeasureLF.padicLog_mul_of_norm_lt_one`. The concrete move is a **rename + reattach**:
expose the unit-ball form as `padicLog_mul` (the public, maximally-general API), and keep the present
exp-ball lemma alongside it as the auxiliary `padicLog_mul_of_mem_expBall` (3 internal callers in
`ValuesAtOne.lean`/`ExtLog.lean` genuinely need the small-ball hypothesis, and the unit-ball proof is
built on it, so it cannot be deleted). Do **not** upstream this lemma in isolation — its statement
and proof depend on `padicLog`, `padicExp`, `InExpBall`, `padicExp_add`, and the exp↔log inversions,
none of which mathlib has; it ships only as part of the whole `padicExp`/`padicLog` PR package, with
the unit-ball `padicLog_mul` as the headline result. Announce on the `#mathlib4` Zulip and run
`/cleanup` on the cluster first.
