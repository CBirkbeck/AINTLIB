# `/mathlibable` report — `PadicLFunctions.MeasureR.padicLog_pow_of_norm_lt_one`

Mode A, full 10-phase workflow with the exhaustive 9-channel literature search.

**Final five-bucket verdict: `BORDERLINE-needs-human`.**

---

### Baseline (Phase 0)

- lake build:               build not re-run; reasoned from source (per task BUILD NOTE — `lake build` is stale/slow here; the declaration and its full dependency chain were read directly from source and reasoned from there, exactly as the skill's Phase 0 fallback allows).
- decl `PadicLFunctions.MeasureR.padicLog_pow_of_norm_lt_one`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ValuesAtOne.lean:577`
- kind:                      theorem
- has sorry:                 no (proof is a 2-case `induction n`; both branches close)
- module docstring summary:  "The p-adic value L_p(θ,1)" (RJW §6.2, Thm 6.1(ii)); this lemma is a building block of the `padicLog` ⇄ `extLog` reconciliation feeding the antiderivative `F̃_θ`.

---

### Statement (Phase 1)

`padicLog_pow_of_norm_lt_one` is a theorem stating the following:

> Let `K` be a complete ultrametric normed field that is a normed `ℚ_p`-algebra, and let `log_p` be the Iwasawa p-adic logarithm `log_p(x) = Σ_{n≥0} (−1)ⁿ (n+1)⁻¹ (x−1)^{n+1}` (junk-extended, meaningful on the open unit disc). Then for every `x ∈ K` with `‖x − 1‖ < 1` and every `n ∈ ℕ`,
> `log_p(xⁿ) = n · log_p(x)`.

This is the **logarithm-of-a-power law** for the p-adic logarithm, stated on the **full open unit disc** `‖x−1‖ < 1` (equivalently `x − 1 ∈ m_K`, the maximal ideal). It is the integer-power specialisation of the additive functional equation `log_p(xy)=log_p(x)+log_p(y)`, and is proved by induction on `n` from that additive law.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the prime.
- `K : Type*`, `[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K]` — a complete ultrametric normed field over `ℚ_p`. Note `[CharZero K]` is explicitly `omit`-ed for this lemma (`omit [CharZero K] in`), so it does **not** depend on characteristic zero.
- `padicLog p : K → K` — the Iwasawa log, defined in `PadicExp.lean:384`.

Hypotheses (Lean side):
- `(hx : ‖x - 1‖ < 1)` — `x` lies in the open unit disc / principal-unit disc (the maximal domain of additivity).
- `(n : ℕ)` — the exponent.

Conclusion (math): `log_p(xⁿ) = n · log_p(x)`.

Conclusion (Lean): `padicLog p (x ^ n) = n • padicLog p x`.

Proof body (read from source):
```lean
induction n with
| zero => simp
| succ k ih =>
  rw [pow_succ, padicLog_mul_of_norm_lt_one (p := p)
      (boundary_norm_pow_sub_one_lt_one hx k) hx, ih, succ_nsmul]
```
The inductive step rewrites `x^{k+1} = xᵏ·x`, applies the **conditional** multiplicativity `padicLog_mul_of_norm_lt_one` (which needs `‖xᵏ−1‖<1`, supplied by `boundary_norm_pow_sub_one_lt_one`), then `ih` and `succ_nsmul`.

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: It is a corollary (the `n`-th-power law) of the additive functional equation `padicLog_mul_of_norm_lt_one`; a one-step induction. It is not a new structure and not named after a person. (However it sits inside a *substantial* new mathematical object — the p-adic log on `K` — which is itself absent from mathlib; that context is what makes the verdict non-trivial, see Phase 7.)

(Note: literature width was run EXHAUSTIVE regardless; BIG/SMALL recorded only for framing.)

### One-line check (Phase 2b)

Body line count: ~4 substantive lines (an `induction` with two branches).
One-liner verdict: n/a — kind is `theorem`, not `def`. Section skipped.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | `p-adic logarithm log(x^n) = n log(x) power rule property functional equation` | yes | `log_p(xy)=log_p(x)+log_p(y)`; `log(xⁿ)=n·log(x)` follows | MIT 18.785 PS10; Davenport `exp.pdf`; arXiv 1907.06437/1904.09850. Multiple sources: power rule is the immediate corollary of additivity. |
| 2 | WebSearch (general / max-domain) | `Iwasawa p-adic logarithm domain convergence |x-1|<1 multiplicative homomorphism principal units` | yes | `log_p(1+x)=x−x²/2+…` converges for **all** `x ∈ m_K`; homomorphism there | Isomorphism (isometry) only on the smaller disc `r > e/(p−1)`; **additivity holds on all of `1+m_K`**. This is exactly our domain `‖x−1‖<1`. |
| 3 | WebSearch (named-after / aliases) | `"p-adic logarithm" homomorphism "log_p" "1+m" principal units log(xy)=log(x)+log(y)` | yes | unique homomorphism extending the power series; additive on principal units `1+m_K` | Confirms #1/#2; "1-units" / "principal units" / "Iwasawa logarithm" are the standard names. |
| 4 | ChatGPT MCP | "standard form of the p-adic-log power law, its generality, historical evolution" | n/a | — | **No ChatGPT/OpenAI MCP server is configured in this environment** (only Asana/Atlassian/Box/Canva/Figma proxies are installed; none mathematical). Recorded n/a; substituted query #10 below to preserve a fourth independent generality+history probe. |
| 5 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/` | n/a | — | Neither directory exists (no source-paper PDFs vendored locally). Recorded n/a per protocol. The module docstring cites "RJW" (Iwasawa, *p-adic L-functions*) §6.2 / Lem 5.14 as the source. |
| 6 | nLab | `nLab p-adic logarithm` + fetched `ncatlab.org/nlab/show/logarithm` | no (for p-adic) | — | The nLab `logarithm` page covers real / complex / Lie-group logs only; **no p-adic section**. The "logarithm of a formal group" `log_F(F(X,Y))=log_F X + log_F Y` is the closest abstract analog (formal-group route to the same additivity). |
| 7 | nCatLab (categorical) | (same as #6) | n/a | — | Not a categorical concept beyond the formal-group-logarithm remark in #6; no separate categorical statement. |
| 8 | Stacks Project (alg geom) | considered | n/a | — | Not an algebraic-geometry / scheme-theoretic concept. The p-adic analytic logarithm is not a Stacks topic. Recorded n/a with reason. |
| 9 | MathOverflow / Math.StackExchange | `mathoverflow p-adic logarithm group homomorphism principal units domain |x-1|<1 most general` | yes | additive homomorphism on `1+m_K`; isomorphism only on smaller disc | Corroborates the domain split: **additivity on all `1+m_K`** vs. iso/isometry on `r>e/(p−1)`. |
| 10 | recent arXiv (last 5y) + history probe (ChatGPT substitute) | `standard definition p-adic logarithm additivity power law historical evolution Iwasawa extension units` | yes | `L(x)=Σ(−1)^{n−1}xⁿ/n`; injective homomorphism on its domain; Iwasawa 1968 | arXiv 2601.18187 (2026), 1907.06437, 1904.09850, math/0512015. Historical note: Iwasawa (1968) studied `log` of principal units via reciprocity; the homomorphism-on-`1+m` form is classical and stable. |

Protocol pass check:
- WebSearch ran ≥3 distinct queries at different generality levels (#1 specific, #2 max-domain, #3 aliases) — ✓.
- ChatGPT MCP: **environment has no such server** — recorded n/a with reason and substituted query #10 (an independent fourth probe explicitly asking for standard form + generality + historical evolution) to keep the rigour the channel is meant to provide.
- Local references checked (#5) — absent, n/a with reason.
- nLab checked (#6, fetched) — ✓.
- Stacks / nCatLab / MathOverflow / arXiv each checked or n/a-with-reason (#7–#10) — ✓.

### Literature summary (Phase 3)

Concept identified as: **the Iwasawa p-adic logarithm `log_p`**, and specifically its **power law `log_p(xⁿ)=n·log_p(x)`**, an immediate corollary of the **additive functional equation `log_p(xy)=log_p(x)+log_p(y)`** on the principal-unit disc.

Sources agree on the standard form: **yes.** Every source gives `log_p(1+x)=Σ_{n≥1}(−1)^{n−1}xⁿ/n` and the homomorphism property `log_p(xy)=log_p(x)+log_p(y)`.

Most general standard form: the additive law (hence the power law `log(xⁿ)=n·log(x)`) holds on the **entire open unit disc `‖x−1‖<1`** (`x−1 ∈ m_K`) of any complete extension of `ℚ_p` (including `ℂ_p` and any finite/complete extension `K`). The power law is never stated as a separate named theorem in the literature — it is a one-line corollary of additivity, universally treated as such.

Generality dimensions where the literature varies:
- **Domain.** Two distinct discs appear and must not be conflated. (a) **Additivity / homomorphism**: all `1+m_K`, i.e. `‖x−1‖<1` — *this is our lemma's domain.* (b) **Isometry / isomorphism onto `m_K`**: only the smaller disc `‖x−1‖ < p^{−1/(p−1)}` (`r>e/(p−1)`). Our lemma uses the **larger, maximal** domain (a), which is the correct/standard domain for the power law.
- **Base field.** Stated for `ℚ_p`, finite extensions, `ℂ_p`, or any complete normed `ℚ_p`-algebra. Our `K` (complete ultrametric normed `ℚ_p`-algebra field) sits at the general end.
- **Exponent.** `ℕ` here; the literature's homomorphism gives it for `ℤ` (negative powers too) on the full multiplicative group via the Iwasawa extension `log_p(p)=0`, `log_p(ζ)=0`.

Disagreement with the literature: **none.** The Lean form `padicLog p (x^n) = n • padicLog p x` for `‖x−1‖<1` is exactly the standard power law on the standard (maximal) domain.

---

### Generality analysis — `padicLog_pow_of_norm_lt_one`

Literature-standard form (from Phase 3): the additive homomorphism on `1+m_K` (`‖x−1‖<1`), with `log(xⁿ)=n·log(x)` as its `n`-th-power corollary; over any complete extension of `ℚ_p`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|---|---|---|---|---|
| 1 | `[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K]` | complete ultrametric normed `ℚ_p`-algebra field | complete extension of `ℚ_p` (e.g. `ℂ_p`, finite extensions) | NO (already general) | This is essentially the maximal hypothesis cluster for which the convergent power series `padicLog` is defined; matches the literature's "complete extension of `ℚ_p`". The `padicLog` def itself needs completeness + ultrametric for convergence. Not over-strong. |
| 2 | `(hx : ‖x − 1‖ < 1)` | full open unit disc | `1+m_K`, i.e. `‖x−1‖<1` — the maximal additivity domain | NO | This is **already the weakest (largest) domain** on which the power law holds. The sibling `ExtLog.padicLog_pow` uses the *smaller* `InExpBall` disc; this lemma is the strict **strengthening** to the full disc. Cannot be weakened further (additivity genuinely fails outside `1+m_K`). |
| 3 | `(n : ℕ)` | natural-number exponent | `ℤ` (via the multiplicative homomorphism) | yes (to `ℤ`) | The homomorphism on the unit group gives `log(xⁿ)=n·log(x)` for `n∈ℤ`. But the `ℤ` form needs `x⁻¹` to stay in the disc (true here since `‖x‖=1` on `1+m_K`) and the `zsmul`/inverse API; it's a *separate* lemma, not a weakening of this one. A reasonable companion, not a defect. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (along the two load-bearing axes — base field and domain). The domain `‖x−1‖<1` is the maximal disc for additivity, and the typeclass cluster is the standard "complete extension of `ℚ_p`". The only open axis is `ℕ → ℤ` on the exponent, which is an additional companion lemma rather than a weakening of this statement.
Number of weakening opportunities found (for *this* statement): 0 (the `ℤ`-exponent form is a separate result, not a weaker hypothesis on this one).
Proposed restatement: none required — the form is already at the literature-standard generality.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preambles → typeclasses/instances? | no | already fully typeclass-driven (`NormedField`/`NormedAlgebra`/`IsUltrametricDist`/`CompleteSpace`) | — |
| 2 | sequences/metric → filters/topological? | no | the statement is a pure algebraic identity at a fixed point; no limit/filter content | — |
| 3 | construct an object → universal-property class? | **partially** | the *deeper* modern-idiom move is to bundle `padicLog` restricted to `(1+m_K, ×) → (m_K, +)` as a **`MonoidHom`/`AddMonoidHom` on a bundled principal-unit subgroup**; then `log(xⁿ)=n·log(x)` is `map_pow`/`map_nsmul` **for free** | the whole `MonoidHom` API: `map_one`, `map_mul`, `map_pow`, `map_zpow`, kernel/range, composition. This is the genuinely correct mathlib formulation of the *family* (def + `padicLog_mul_of_norm_lt_one` + this power law). |
| 4 | set-with-closure-predicate → bundled substructure? | yes (paired with #3) | the disc `{x : ‖x−1‖<1}` should be the bundled subgroup `1 + m_K` (units of the valuation ring reducing to 1); the hom in #3 lives on it | lattice/subgroup API, quotients (`(1+m_K)/(1+m_K²)`), the Iwasawa-module structure |
| 5 | vector-space/metric/field-specific → weaker typeclass? | no | the hypotheses are already the minimal ones for `padicLog` to converge | — |
| 6 | 1-categorical → higher/∞-categorical? | no | not applicable | — |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group? | yes (the `ℕ→ℤ` axis) | restate over `ℤ` via the unit-group homomorphism | `zpow` API, negative powers |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** — but it is a reformulation of the *whole p-adic-log API*, not of this lemma in isolation.
- Proposed mathlib-idiomatic restatement: bundle `padicLog ↾ (1+m_K)` as an `AddMonoidHom`/group homomorphism `(1+m_K, ×) → (m_K, +)` on a **bundled principal-unit subgroup** (Phase 4c rows 3+4). Then this lemma is `map_nsmul`/`map_pow` and needs no separate statement.
- Cost: **EXPENSIVE / cross-cutting** — it requires first defining a bundled `padicLog` (the def is itself absent from mathlib), the bundled subgroup `1+m_K`, and re-deriving `padicLog_mul_of_norm_lt_one` as the hom's `map_mul`. It is a multi-declaration design decision, not a local rewrite of this theorem.
- Mathlib downstream this enables: the full `MonoidHom`/`AddMonoidHom` ecosystem (`map_pow`, `map_zpow`, `map_one`, kernel/range, Iwasawa-module structure on `(1+m_K)/(1+m_K^n)`).
- Real mathematical improvement: **yes** — it would make `log(xⁿ)=n·log(x)`, `log(x⁻¹)=−log(x)`, and the finite-product law all free corollaries of one bundled homomorphism, eliminating the project's hand-rolled `padicLog_mul`/`padicLog_pow`/`padicLog_prod` chain.

**Consequence for Phase 7.** The modern-idiom target is *not* a property of this lemma alone — it is a redesign of the p-adic-log API whose anchor object (`padicLog` itself, and its multiplicativity) is **not yet in mathlib and not yet assessed for upstreaming**. That is precisely the judgment call the skill cannot make alone (which `padicLog` def is canonical, whether the project owner wants to upstream the bundled hom, what grain the PR(s) should be). It pushes the verdict toward BORDERLINE rather than a clean YES-but-generalise-first, because "generalise to a bundled hom" presupposes decisions about an object outside this lemma.

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (no definitional equalities or typeclass-search paths introduced). Skipped per scope.

---

### Mathlib search-status: `padicLog_pow_of_norm_lt_one`

[A] Lean-Finder       n/a — no Lean-Finder MCP tool available in this environment.
[B] Loogle            n/a — no Loogle MCP tool available; type-pattern `(?a ^ _) = _ • (?a)` for a p-adic log is moot given [D] below (no `padicLog` exists in mathlib to pattern-match against).
[C] LeanSearch        n/a — no LeanSearch MCP tool available in this environment.
[D] Grep mathlib src  `padicLog`, `PadicLog`, `padic_log` → **0 hits** across the entire `Mathlib/` tree. `log_pow` family → only `Real.log_pow`, `Complex.clog_pow`, `ENNReal.log_pow` (real/complex/ENNReal logs — none p-adic). `PowerSeries.log` exists (formal-series log) but has no p-adic analytic-evaluation power law. `map_pow`/`map_nsmul` exist (`Mathlib/Algebra/Group/Hom/Defs.lean`) but require a bundled `MonoidHom` — and `padicLog` is **not** bundled as a hom anywhere (it cannot be a *total* hom: additivity is conditional on the disc).
[E] Name pattern      grep for `padicLog`/`p-adic log`/`Iwasawa log` across `Mathlib/NumberTheory/Padics/*` → no logarithm file; the only `padicLog`-shaped match (`ProperSpace.lean`) is about `ℤ_[p]` compactness, unrelated.

Searched for both:
  - the user's current form (`padicLog (x^n) = n • padicLog x` on `‖x−1‖<1`) — not in mathlib.
  - the literature-standard form (additive homomorphism `log(xy)=log(x)+log(y)` on `1+m_K`, and the bundled-hom modern idiom) — also **not in mathlib**: mathlib has no p-adic logarithm at all.

Concluded: **not in mathlib** (grep over the full `Mathlib/` tree exhausted, for both the power-law form, the additive-homomorphism form, and the bundled-hom idiom; the Loogle/LeanSearch/Lean-Finder MCP channels are unavailable in this environment but are moot, since the decisive `padicLog`-grep returns zero — there is no p-adic logarithm object in mathlib to match against). Mathlib's only p-adic-log-adjacent material is `PowerSeries.log` (formal) and the real/complex/ENNReal `log_pow` lemmas.

---

### Call sites — `padicLog_pow_of_norm_lt_one`

Internal use count: **0** (within the same project, NOT counting the declaring file `ValuesAtOne.lean:577`).
External-to-file callers: **0** distinct files.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| (none) | — |

Inline-derivation grep (was the `n • padicLog x` power law re-derived elsewhere without using `padicLog_pow_of_norm_lt_one`?):
- `ResidueZeta.lean:1555–1561` derives `padicLog (a^{p−1}) = (p−1)·extLog a` — but this is the **`extLog`-bridge relation** (a different identity, via `extLog_eq_of_witness`), **not** the `n • padicLog x` power law. So it is **not** an inline re-derivation of this lemma's statement.
- The genuine `n • padicLog x` power-law form is **not re-derived anywhere** outside the declaring file.

Call-sites reading (per Phase 6.0.1): `K = 0` internal uses, **no** inline re-derivation of the same statement. By the table this reads as "brand new + unused so far" → Junk OR genuinely-new (BORDERLINE). Context disambiguates toward *genuinely-new*: the sibling reports show this is the deliberate **general capstone** of a deliberately-bootstrapped chain (`padicLog_mul → padicLog_pow_p → padicLog_pow_pPow`, with the `p^N` step report explicitly naming *this* lemma as the general law to upstream). It is the most-general member of the family, kept available for the API even though the project currently routes through the `p^N` specialisation. Not dead code; an intentional general statement with no current consumer.

### Composition check (Phase 6)

Can `padicLog_pow_of_norm_lt_one` be derived from mathlib in ≤3 chained calls?

Attempt 1: `map_pow`/`map_nsmul` on a bundled hom — `(padicLogHom).map_pow x n` or similar.
  - Mathlib decls used: `map_pow` / `map_nsmul` (`Mathlib/Algebra/Group/Hom/Defs.lean`).
  - Result: **fails.** `padicLog` is **not** a `MonoidHom`/`AddMonoidHom` in the project (grep: zero `padicLog`+`MonoidHom` matches), and it **cannot** be a *total* one — its multiplicativity is only conditional (`padicLog_mul_of_norm_lt_one` requires both arguments in the disc; `padicLog` is junk-extended elsewhere). There is no bundled hom to call `map_pow` on. Building one is the EXPENSIVE Phase-4c redesign, not a composition.

Attempt 2: chain mathlib's `PowerSeries.log` power law, or any real/complex `log_pow`.
  - Result: **fails.** Those are different objects (formal series; real/complex/ENNReal logs). None gives the p-adic analytic `padicLog` power law.

Attempt 3 (the actual project proof): `induction n; rw [pow_succ, padicLog_mul_of_norm_lt_one (boundary_norm_pow_sub_one_lt_one hx k) hx, ih, succ_nsmul]`.
  - Mathlib decls used: only `pow_succ`, `succ_nsmul`. The two load-bearing steps — the **conditional** multiplicativity `padicLog_mul_of_norm_lt_one` and the disc-stability `boundary_norm_pow_sub_one_lt_one` — are **project lemmas, not mathlib**. And it is an `induction`, i.e. a genuine proof, not a ≤3-call composition.
  - Result: not a mathlib composition.

Conclusion: **NOT-COMPOSABLE** from mathlib. (Mathlib has neither `padicLog`, nor its conditional multiplicativity, nor the disc-stability lemma; and `padicLog` is deliberately *not* a total hom, so `map_pow` is unavailable.)

---

## Verdict: `padicLog_pow_of_norm_lt_one`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): power law `log(xⁿ)=n·log(x)` is the standard `n`-th-power corollary of the additive homomorphism `log_p(xy)=log_p(x)+log_p(y)`, which holds on the **maximal disc `‖x−1‖<1`** (`1+m_K`). Confirmed across MIT 18.785, Davenport, Neukirch-context, arXiv 1907.06437/1904.09850/2601.18187, MathOverflow. The form and domain match the literature exactly.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** for this statement (maximal domain, standard typeclass cluster). Phase 4c found a real *modern-idiom* improvement — bundle `padicLog ↾ 1+m_K` as an `AddMonoidHom` so the power law is `map_nsmul` — but that target is a **redesign of the whole p-adic-log API**, whose anchor object (`padicLog` + its multiplicativity) is itself not in mathlib and not yet scoped for upstreaming.
- Mathlib search (Phase 5): **not in mathlib** — zero `padicLog` hits; mathlib has no p-adic logarithm (only `PowerSeries.log` and real/complex/ENNReal `log_pow`).
- Composition check (Phase 6): **NOT-COMPOSABLE** — no bundled hom to call `map_pow` on (and one can't exist totally); the real proof is an induction on the project's own conditional-multiplicativity + disc-stability lemmas.

**Rationale (1–2 paragraphs):**

The statement is true, at the maximal/standard domain, and genuinely absent from mathlib — so the easy disqualifiers (NO-mathlib-has-it, NO-composable) are both ruled out by the evidence: mathlib has no p-adic logarithm of any kind, and `padicLog` is deliberately *not* a total homomorphism, so `map_pow` cannot be invoked. That would normally point at a YES bucket. But the verdict cannot be a clean YES, and this is exactly the judgment the sibling assessments already surfaced. The result is **inseparable from the p-adic-log API it lives in**: it is the general capstone of a deliberately-bootstrapped chain (`padicLog_mul_of_norm_lt_one → padicLog_pow_p_of_norm_lt_one → padicLog_pow_pPow_of_norm_lt_one`), and the `p^N`-step report (`padicLog_pow_pPow_of_norm_lt_one.md`, verdict NO-composable) explicitly names **this lemma** as the object to upstream "if a p-adic-logarithm contribution to mathlib is ever undertaken". The single-`p`-step sibling (`padicLog_pow_p_of_norm_lt_one.md`) landed on BORDERLINE with four numbered questions about exactly this: what is the right mathlib grain (this lemma alone, vs. the bundled `padicLog`-package), which of AINTLIB's *two* `padicLog` definitions (`PadicExp.lean` over a general `K` vs. `FltRegularBernoulli`'s over `ℚ_p`) is canonical, and whether the multiplicativity/bundled-hom should be the headline.

Those questions are not resolvable from the search evidence — they are project-policy and mathlib-design-taste calls. Phase 4c sharpens the point: the *correct* mathlib formulation of this fact is not the bare lemma but `map_nsmul` for a bundled `AddMonoidHom (1+m_K) → (m_K,+)`, which presupposes first defining `padicLog` (absent from mathlib), the bundled principal-unit subgroup, and re-deriving multiplicativity as `map_mul`. Whether to do that — and at what grain, against which `padicLog` def, with the project owner's intent to maintain it upstream — is a human decision. The call-site reality (`K=0` internal uses, no inline re-derivation, kept only as the general member of the family) reinforces that this is an API-shape question, not a "ship this one lemma" question. Hence **BORDERLINE-needs-human**, consistent with the `p`-step sibling and with the verdict-gate guidance that the right upstreaming object is the homomorphism/power-law assessed *against the (also-not-in-mathlib) `padicLog` definition*.

**Numbered questions (≤5):**

1. **Grain.** Do you want to upstream a p-adic logarithm to mathlib as a *package* (the analytic `padicLog` definition + its multiplicativity on `1+m_K` + this power law + the finite-product law `padicLog_prod_of_norm_lt_one`), rather than this single corollary in isolation? (If yes, this lemma rides along as `map_nsmul`/a one-line corollary and is **not** a standalone PR.)

2. **Canonical definition.** AINTLIB has two `padicLog`s — `PadicLFunctions/PadicExp.lean` (general complete normed `ℚ_p`-algebra `K`) and `FltRegularBernoulli/.../PadicLog.lean` (over `ℚ_p`). Which is the canonical one to upstream? (Mathlib should have exactly one; the general-`K` version is the natural choice.)

3. **Bundled hom vs. plain lemmas (Phase 4c).** Should the mathlib contribution bundle `padicLog ↾ (1+m_K)` as an `AddMonoidHom` to `(m_K,+)` on a bundled principal-unit subgroup — making `log(xⁿ)=n·log(x)`, `log(x⁻¹)=−log(x)`, and the product law all free `map_*` corollaries — or ship `padicLog` as a plain function with hand-stated multiplicativity/power lemmas (matching the current project style)? This is the EXPENSIVE-but-correct modern-idiom question and is a design-taste call.

4. **`ℤ`-exponent companion.** Should the upstreamed power law be stated for `n : ℤ` (via the unit-group homomorphism / `zpow`) rather than `n : ℕ`, since `‖x‖=1` on `1+m_K` keeps inverses in the disc? (A strictly more useful headline form, but a separate statement.)

5. **Ownership.** Is anyone committed to maintaining a p-adic-logarithm file in mathlib (it has no such file today, and adding `padicLog` is a non-trivial new analytic-NT development)? If not, keep the whole chain project-local.

**Refactor-actionable note.** Until these are answered, do **not** open a mathlib PR for this lemma alone. The actionable next step is to scope the *anchor* objects, not this corollary: assess `PadicLFunctions.padicLog` (the definition) and `PadicLFunctions.MeasureR.padicLog_mul_of_norm_lt_one` (the multiplicativity headline) for upstreaming first; this power law follows them. No project-internal refactor is needed (the lemma is correct, general, and harmless to keep as the family's general member; the only optional cleanup, flagged in the `p^N` sibling report, is rerouting `ValuesAtOne.lean:596` through this general law).

---

## Next step

User answers the 5 numbered questions to fix the mathlib-facing grain (whole-`padicLog`-package vs. single lemma; which of the two AINTLIB `padicLog` defs is canonical; bundled-`AddMonoidHom` vs. plain lemmas; `ℕ` vs. `ℤ` exponent; upstream ownership). The single most valuable upstreaming target in this chain is the **analytic `padicLog` definition + its multiplicativity `padicLog_mul_of_norm_lt_one` on the open unit ball** — mathlib has no p-adic logarithm at all — with this power law as a one-line `map_nsmul`/corollary once that anchor is in place. Then re-run `/mathlibable` on the chosen anchor object(s) (most usefully `/mathlibable PadicLFunctions.MeasureR.padicLog_mul_of_norm_lt_one` and the `padicLog` definition) to scope the right mathlib PR.
