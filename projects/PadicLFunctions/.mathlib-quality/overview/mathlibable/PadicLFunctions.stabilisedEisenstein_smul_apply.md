# `/mathlibable` report — `PadicLFunctions.stabilisedEisenstein_smul_apply`

**Mode A — single declaration, full 10-phase workflow with the exhaustive 9-channel literature search.**

---

### Baseline (Phase 0)

- lake build:               ✓ clean (`lake build PadicLFunctions.EisensteinComplex` → "Build completed successfully (3411 jobs)"). Build was *not* stale; it was re-run and is green. (The task's "build may be slow" caveat did not bite — recording that the build was actually re-run, not reasoned-from-source-only.)
- decl `PadicLFunctions.stabilisedEisenstein_smul_apply`:  ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/EisensteinComplex.lean:364`
- kind:                      theorem
- has sorry:                 no (file `EisensteinComplex.lean` has 0 occurrences of `sorry`)
- module docstring summary:  "The q-expansion of the p-stabilised Eisenstein series (RJW §8, complex side)" — defines RJW's normalised `E_k = ζ(1−k)/2 + Σσ_{k−1}(n)qⁿ`, its p-stabilisation `E_k^{(p)} = E_k(z) − p^{k−1}E_k(pz)`, and realises the latter as a genuine `ModularForm (Γ₀(p))` via the LeanModularForms level-raising operator.

---

### Statement (Phase 1)

`stabilisedEisenstein_smul_apply` is **a theorem** stating the following:

For a prime `p`, an integer `k ≥ 4`, and a point `z` in the upper half-plane `ℍ`, scaling the modular form `stabilisedEisenstein p hk` (the `Γ₀(p)`-modular form whose value is `E_k(z) − p^{k−1}E_k(pz)`, with `E_k = ModularForm.E` the *constant-term-1* normalised Eisenstein series) by the rational zeta value `ζ(1−k)/2` reproduces the p-stabilised combination of RJW's *constant-term-`ζ(1−k)/2`* Eisenstein series `rjwEisenstein`. In symbols:

  `(ζ(1−k)/2) · stabilisedEisenstein(z)  =  rjwEisenstein(z) − p^{k−1} · rjwEisenstein(pz)`,

where `rjwEisenstein z := (ζ(1−k)/2) · ModularForm.E hk z` and `pz = pScale p z`. This is purely a **bridge between two normalisation conventions** for the (already-constructed) p-stabilised Eisenstein series — mathlib/LeanModularForms's constant-term-1 `E` versus RJW's classical `ζ(1−k)/2 + Σσ_{k−1}(n)qⁿ`. It is the bookkeeping identity that lets the q-expansion theorem `hasSum_stabilisedEisenstein` (stated in RJW's normalisation) be read off from the modular-form object `stabilisedEisenstein` (stated in mathlib's).

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — a fixed prime (section variable).
- `{k : ℕ}`, `(hk : 4 ≤ k)` — the weight; `≥ 4` (the underlying objects need `≥ 3`, the bound is `4` here to match `rjwEisenstein`'s context and the q-expansion theorem).
- `(z : ℍ)` — a point of the upper half-plane.

Hypotheses (Lean side):
- `hk : 4 ≤ k` — weight bound (passed down via `by omega` to the `3 ≤ k` that `stabilisedEisenstein`, `rjwEisenstein` and `pScale` require).

Conclusion (math): the scalar `ζ(1−k)/2` distributes over the p-stabilisation difference, converting the constant-term-1 normalisation into RJW's constant-term-`ζ(1−k)/2` normalisation.

Conclusion (Lean): `(((zetaNeg (k - 1) : ℚ) : ℂ) / 2) * stabilisedEisenstein p (by omega) z = rjwEisenstein (by omega) z - (p : ℂ) ^ (k - 1) * rjwEisenstein (by omega) (pScale p z)`.

**Proof body (verbatim):**
```lean
rw [stabilisedEisenstein_apply, rjwEisenstein, rjwEisenstein]
ring
```
i.e. rewrite the modular-form value by the *project-local* `stabilisedEisenstein_apply`
(`stabilisedEisenstein z = E_k z − p^{k−1}·E_k(pScale p z)`), unfold the *project-local*
`rjwEisenstein` (`= (ζ(1−k)/2)·E_k`) on the right, then close by `ring` (scalar distributivity
`c·(a − p^{k−1}·b) = c·a − p^{k−1}·(c·b)`).

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: It is a helper "bridge" lemma — not a named theorem, not a new structure, not listed as a `## Main results` headline. It converts between two normalisation conventions for an object built elsewhere; its proof is one project-specific rewrite plus `ring`.

(Note: literature width was EXHAUSTIVE regardless — all nine channels were run below. BIG/SMALL is recorded only for the report's framing.)

### One-line check (Phase 2b)

Body line count: 2 substantive lines (`rw [...]` + `ring`).
One-liner verdict: **n/a — kind is `theorem`, not `def`** (the one-line *definition* check applies only to `def`/`abbrev`/`structure`). Recorded and skipped.

---

### PHASE 3 — Literature search (EXHAUSTIVE protocol)

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | `p-stabilization of Eisenstein series E_k^(p)(z) = E_k(z) - p^(k-1) E_k(pz) definition`                | yes  | `E_k^{(p)}(z) := E_k(z) − p^{k−1}E_k(pz)`, with `E_k = ζ(1−k)/2 + Σ_{n>0} σ_{k−1}(n)qⁿ` | Confirmed across arXiv:2205.14711, 2302.13009, Dasgupta "Evil Eisenstein". The *p-stabilisation operation* is textbook-standard; produces a form on `Γ₀(p)`. |
|  2 | WebSearch (general form)         | `normalized Eisenstein series E_k constant term zeta(1-k)/2 p-stabilized modular form`                  | yes  | `E_{2k} = 1/(2ζ(2k))·G_{2k}`, constant term 1; `E_k = 1 − (2k/B_k)Σ…` | Confirms the two standard normalisations (constant-term-1 vs `ζ`-weighted). The relation between them is `2ζ(2k)` / `B_k` scaling — exactly the bookkeeping `rjwEisenstein` encodes. |
|  3 | WebSearch (named-after / aliases)| `p-stabilization Eisenstein series alternative names "stabilized" V_p operator level Gamma_0(p) Kubota-Leopoldt` | yes  | "p-stabilisation"; also "ordinary/semi-ordinary stabilisation"; U_p/V_p operator; appears verbatim in **arXiv:2309.15692** ("An introduction to p-adic L-functions" — the RJW source) | The operation has a name; the **scalar-rescaling bridge between two normalisations of a fixed Eisenstein series does NOT have a name** — it is routine and stated in passing. |
|  4 | ChatGPT MCP                      | (intended: "standard def + generality + historical evolution of the p-stabilised Eisenstein series and any named normalisation-bridge lemma") | n/a  | —                                | **n/a — the `chatgpt-math` MCP server is configured but unauthenticated in this environment** (`~/.claude/mcp-needs-auth-cache.json` lists `plugin:mathlib-quality:chatgpt-math` as needing auth; `ToolSearch` returns no callable handle). Compensated by running 6 WebSearch queries at three generality levels + nLab + arXiv source fetch. |
|  5 | Local references                 | grep `.mathlib-quality/references/` and `refs/` for "Eisenstein", "stabili", "RJW"                     | n/a  | (no references dir)               | **n/a — no `projects/PadicLFunctions/.mathlib-quality/references/` and no `refs/` symlink exist.** The RJW paper (arXiv:2309.15692) is the de-facto reference and is named throughout the source docstrings (TeX 2371, 2391, 2394). |
|  6 | nLab                             | `Eisenstein series` (fetched ncatlab.org/nlab/show/Eisenstein+series)                                   | no   | (basic `G_{2k}`, j-invariant, Bernoulli — **no p-stabilisation, no normalisation-bridge**) | nLab's Eisenstein page does not treat p-adic / p-stabilisation at all. Confirms this is not an abstract/categorical concept with a clean nLab statement. |
|  7 | nCatLab (if categorical)         | —                                                                                                      | n/a  | —                                | n/a — not a categorical concept; it is a concrete scalar identity between two functions `ℍ → ℂ`. |
|  8 | Stacks Project (if alg geom)     | —                                                                                                      | n/a  | —                                | n/a — not an algebraic-geometry / scheme-theoretic concept; classical/p-adic modular forms over `ℍ`. |
|  9 | MathOverflow / Math.StackExchange| `Eisenstein series two normalizations bridge lemma scalar multiple modular form function relation`     | no   | (results were arXiv hep-th / number-theory PDFs; only the generic `G_{2k} = (2πi)^{2k}E_{2k}` scalar relation surfaced) | No MO/MSE thread treats the normalisation-conversion as a *named* result — reinforces that this is routine bookkeeping, not a citable theorem. |
| 10 | recent arXiv (last ≤5 years)     | (covered by #1/#3) `2302.13009` (2023), `2205.14711` (2022), `2309.15692` (2023, RJW), `2412.11332` (2024) | yes  | p-stabilisation `E_k(z) − p^{k−1}E_k(pz)` confirmed; **the scalar-bridge between normalisations is never isolated as a lemma** | Recent literature uses the operation freely; the normalisation conversion is implicit (papers fix one normalisation and move on). |

The protocol passed: WebSearch ran 6 distinct queries at three generality levels (specific form, most-general/normalisation form, named-after/aliases); the ChatGPT-MCP row is recorded `n/a` with a concrete reason (server unauthenticated) and compensated; local references recorded `n/a` (absent dir); nLab checked (no hit); Stacks/nCatLab recorded `n/a` with reasons after looking; MathOverflow checked (no named result); recent arXiv checked (operation standard, bridge unnamed). PDF source fetches (Dasgupta, RJW arXiv:2309.15692) were attempted but the PDFs are FlateDecode-compressed and did not render through WebFetch — the q-expansion convention they use is nonetheless confirmed by channels #1–#3, which quote it directly.

### Literature summary (Phase 3)

Concept identified as: **p-stabilisation of the (normalised) Eisenstein series** — `E_k^{(p)}(z) = E_k(z) − p^{k−1}E_k(pz)`. The *underlying operation* is standard (RJW §8 / arXiv:2309.15692 TeX 2387–2394; Dasgupta; the Siegel-stabilisation papers). The *specific content of this theorem* — converting between the constant-term-1 normalisation (`ModularForm.E`) and RJW's constant-term-`ζ(1−k)/2` normalisation (`rjwEisenstein`) by multiplying through by the scalar `ζ(1−k)/2` — is **not a named result anywhere**.

Sources agree on the standard form: yes — for the *p-stabilisation operation*. The normalisation conversion is universally treated as a one-line bookkeeping step (`E_k^{RJW} = (ζ(1−k)/2)·E_k^{ct=1}`, then distribute over the difference), never elevated to a lemma.

Most general standard form: the p-stabilisation `f ↦ f − p^{k−1}·(f∣V_p)` of a level-1 form `f`; specialising `f = E_k`. Mathlib's normalisation choice for `E` (constant term 1) is itself a convention; RJW's is another.

Generality dimensions where the literature varies:
  - **Normalisation of `E_k`**: constant-term-1 (`ModularForm.E`, what mathlib ships) vs `ζ(1−k)/2 + Σσqⁿ` (RJW, this file's `rjwEisenstein`) vs `1 − (2k/B_k)Σ…`. This theorem is precisely the *conversion map* between the first two — by definition local to whatever pair of normalisations a development picks.
  - **The stabilisation operator**: classical `V_p`/`U_p`; here realised concretely as `f − p^{k−1}·f(pScale p ·)`. Not a generality axis the theorem itself touches.

Disagreement with the literature: **none** — the theorem is consistent with the standard p-stabilisation; it simply records a normalisation conversion that the literature leaves implicit.

**Key Phase-3 conclusion for the verdict:** the literature confirms the *operation* but offers **no named, citable form** for *this* statement, because the statement is a conversion between two normalisation conventions, one of which (`rjwEisenstein`) is a definition introduced *in this project*. That is the classic signature of a project-internal glue/bridge lemma, not a mathlib candidate.

---

### Generality analysis — `stabilisedEisenstein_smul_apply` (Phase 4)

Literature-standard form (from Phase 3): the p-stabilisation `E_k(z) − p^{k−1}E_k(pz)`; this theorem is the scalar-rescaling bridge `(ζ(1−k)/2)·(that, in ct=1 normalisation) = (the same, in RJW normalisation)`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|---|---|---|---|---|
| 1 | `(hk : 4 ≤ k)` | weight `k ≥ 4` | `k ≥ 4` even (so `B_k ≠ 0`, `ζ(1−k) ≠ 0`) in the q-expansion context; the *pointwise* identity needs only `k ≥ 3` | yes (to `3 ≤ k`) | The identity is pure scalar distributivity; it holds whenever the constituents (`stabilisedEisenstein`, `rjwEisenstein`) are defined (`k ≥ 3`). `4` is chosen only to match `rjwEisenstein`'s downstream use; this is a *cosmetic* weakening that does not bear on mathlib-worthiness. |
| 2 | `(p : ℕ) [Fact p.Prime]` | prime `p` | a prime (for p-stabilisation) | marginally (`pScale` needs `0 < p`; the *algebra* needs nothing) | The scalar identity itself is agnostic to primality — but `stabilisedEisenstein`/`pScale` are built with `[Fact p.Prime]`, so weakening here is moot: the objects don't exist without it. |
| 3 | `rjwEisenstein`, `stabilisedEisenstein` (the two objects related) | **project-local definitions** | — | n/a | These are not mathlib objects and not literature-named objects; `rjwEisenstein` is `(ζ(1−k)/2)·ModularForm.E`, defined in this file. There is no "more general literature form" to aim at because the *statement is about two bespoke normalisations*. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL for what it states** (a scalar-distributivity bridge between two fixed normalisations). The only weakening (`4 ≤ k` → `3 ≤ k`) is cosmetic and irrelevant to mathlib-worthiness; it does not change the verdict.
Number of weakening opportunities found: 1 (cosmetic: `hk` could be `3 ≤ k`).
Proposed restatement: not warranted — the statement is intrinsically about the project's `rjwEisenstein`/`stabilisedEisenstein` pair, neither of which is a mathlib object.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c) — Bourbaki 2.0

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "Let X be a foo" preambles → typeclasses/instances? | no | — | The hypotheses are already minimal (`Fact p.Prime`, `4 ≤ k`); nothing to bundle. |
|  2 | Sequences/metric → filters/topological? | no | — | A finite scalar identity over `ℂ`; no limit/convergence content to filter-ise. |
|  3 | Construct an object → universal-property class? | no | — | No object is constructed; it equates two already-built functions. |
|  4 | Set-with-closure-predicate → bundled substructure? | no | — | No substructure involved. |
|  5 | Vector-space/metric/field-specific → weaken typeclasses? | no | — | The arithmetic is over `ℂ` because Eisenstein series live there; the scalar is a rational `ζ`-value cast to `ℂ`. No weakening that preserves meaning. |
|  6 | 1-categorical → higher-categorical? | no | — | Not categorical. |
|  7 | Concrete index (ℕ/ℤ/ℝ) → arbitrary additive/ordered structure? | no | — | The "p^{k−1}" and "ζ(1−k)/2" are intrinsic to the modular-forms statement; nothing to index-generalise. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**.
One-line reason: this is a finite scalar-distributivity identity between two project-defined normalisations of a single Eisenstein series; there is no contemporary mathlib reformulation that improves its organisation — the "right form" question is moot because the objects themselves are project-local bookkeeping, not mathlib concepts.

---

### PHASE 4.5 — Diamond / defeq risk

**n/a — declaration kind is `theorem`** (no definitional equalities or typeclass-search paths introduced). Skipped.

---

### Mathlib search-status: `stabilisedEisenstein_smul_apply` (Phase 5)

[A] Lean-Finder       (intended NL queries on "p-stabilized Eisenstein normalization bridge")  n/a — Lean-Finder not reachable as a tool in this environment; compensated by [B]/[C]/[D]/[E].
[B] Loogle            `ModularForm.E` (via loogle.lean-lang.org JSON)                            6 hits, ALL level-1 basics: `ModularForm.E`, `EisensteinSeries.E_qExpansion_coeff_zero` (ct = 1), `EisensteinSeries.q_expansion_bernoulli`, `EisensteinSeries.E_qExpansion_coeff`, `EisensteinSeries.q_expansion_riemannZeta`, `EisensteinSeries.E_ne_zero`. **None** mention p-stabilisation, scaling by `p`, two normalisations, or `E_k(z) − p^{k−1}E_k(pz)`.
[C] LeanSearch        `p-stabilized Eisenstein series relation to normalized Eisenstein series by zeta factor`  n/a — leansearch.net GET returned HTTP 405 (POST-only API; not reachable via WebFetch here). Compensated by [B]/[D].
[D] Grep mathlib src  `grep -rniE "stabili[sz]ed?.{0,15}eisenstein|eisenstein.{0,15}stabili"` over `.lake/packages/mathlib/Mathlib` → **0 hits**. `grep` for `qExpansion`/`q_expansion_bernoulli`/`ModularForm.E` → only the level-1 q-expansion API (`ModularForms/EisensteinSeries/QExpansion.lean`, `ModularForms/QExpansion.lean`). `grep` for `V_p`/`U_p`/`p * z` scaling on modular forms → **nothing** (only `mapGL`/`conjGL` congruence-subgroup plumbing).
[E] Name pattern      grep for `rjwEisenstein`, `stabilisedEisenstein`, `pScale`, `zetaNeg` across mathlib  **0 hits in mathlib** — all four are defined exclusively inside `projects/PadicLFunctions/`.

Searched for both:
  - the user's current form (the `(ζ(1−k)/2)·stabilisedEisenstein = rjwEisenstein − p^{k−1}·rjwEisenstein(p·)` bridge) — **not in mathlib**;
  - the literature-standard form (the p-stabilisation operation and any normalisation-conversion lemma about `ModularForm.E`) — **not in mathlib** (mathlib has only `ModularForm.E` + its level-1 q-expansion; no p-stabilisation layer whatsoever).

Concluded: **not in mathlib** (all reachable methods exhausted: Loogle hit only level-1 basics; grep over the full mathlib source found no p-stabilisation/normalisation-bridge; the two objects the theorem relates do not exist in mathlib). Furthermore the statement is **not expressible in mathlib at all**, because `rjwEisenstein` and `stabilisedEisenstein` are project-local definitions — there is nothing in mathlib for an analogue to even be stated about.

---

### Call sites — `stabilisedEisenstein_smul_apply` (Phase 6.0)

Internal use count: **0** (within `projects/`, excluding the declaring file).
External-to-file callers: **0 distinct files**.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| (none) | The only other occurrences of the name are **docstring mentions**: `EisensteinComplex.lean:29` (module docstring) and `EisensteinComplex.lean:334` (the `stabilisedEisenstein` docstring pointing forward to this bridge). Neither is a call. |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `stabilisedEisenstein_smul_apply`?):
  - (none) — no other site re-derives the `(ζ/2)·stabilised = rjw − p^{k−1}·rjw(p·)` identity. The sibling theorem `hasSum_stabilisedEisenstein` (line 187) proves the q-expansion of the *RJW-normalised* difference directly from `hasSum_rjwEisenstein`, never routing through this bridge; the bridge is the *intended human-facing* statement connecting the modular-form object to the q-expansion, but is not yet consumed.

What the call-sites pattern tells you: **K = 0 internal uses, no inline re-derivation** → this is a brand-new, currently-unused bridge lemma (the file's docstring at line 29 advertises it as "the bridge to `rjwEisenstein`"). On the call-sites rubric this is the "genuinely-new + unused so far" cell, which leans BORDERLINE *on the question of whether it is even kept locally* — but the mathlib question is independently settled by Phases 3+5: it relates two project-local objects, so it is not a mathlib candidate regardless of local usage.

---

### Composition check (Phase 6)

Can `stabilisedEisenstein_smul_apply` be derived from **mathlib** in ≤3 chained calls? — The relevant question for the verdict is subtler than usual, because the statement *mentions project-local definitions*. Two readings:

**Reading A — can mathlib alone state/prove it?** No: the statement names `rjwEisenstein`, `stabilisedEisenstein`, `pScale`, `zetaNeg`, none of which exist in mathlib. Mathlib cannot express the LHS or RHS. So "compose from mathlib primitives" is vacuously inapplicable: there is no mathlib statement to compose to.

**Reading B — within the project, is the proof a trivial composition of existing (project + mathlib) facts?** Yes, and trivially so:

Attempt 1: `by rw [stabilisedEisenstein_apply, rjwEisenstein, rjwEisenstein]; ring`
  - Facts used: `stabilisedEisenstein_apply` (**project-local**, line 351: `stabilisedEisenstein z = E_k z − p^{k−1}·E_k(pScale p z)`); unfolding `rjwEisenstein` (**project-local** def, `= (ζ(1−k)/2)·E_k`); `ring`.
  - Result: succeeds (this is the verbatim proof). The mathematical content is exactly `mul_sub` / scalar distributivity once `stabilisedEisenstein_apply` is in hand.
  - Notes: the ONE substantive step, `stabilisedEisenstein_apply`, is itself a project-local lemma about a project-local object; the rest is `ring`. There is **no mathlib lemma** doing any of this work — because there is no mathlib object here.

Conclusion: **NOT-COMPOSABLE-FROM-MATHLIB**, but for the degenerate reason that *mathlib has no relevant primitives at all* (not because the statement is deep). The proof is a one-rewrite-plus-`ring` composition of **project-local** facts. This is decisive evidence that the theorem belongs to the project's internal API and is outside mathlib's universe of discourse — it is the "bridge" half of a definition pair (`stabilisedEisenstein` ↔ `rjwEisenstein`) that exists only here.

---

## Verdict: `PadicLFunctions.stabilisedEisenstein_smul_apply`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the p-stabilisation *operation* `E_k − p^{k−1}E_k(p·)` is standard (RJW arXiv:2309.15692 §8 TeX 2387–2394; Dasgupta; Siegel-stabilisation papers), but the *normalisation-conversion bridge* this theorem states is **not a named/citable result** — it is routine bookkeeping between two normalisations, one of which (`rjwEisenstein`) is defined in this project. 9 channels run; ChatGPT-MCP `n/a` (unauthenticated) and local-refs `n/a` (absent) compensated by 6 WebSearches + nLab + arXiv.
- Generality analysis (Phase 4): MAXIMALLY GENERAL for what it states (only a cosmetic `4 ≤ k → 3 ≤ k` weakening; irrelevant). Modern-idiom check (4c): no modernisation available — it is a finite scalar identity between two bespoke functions.
- Mathlib search (Phase 5): **not in mathlib, and not statable in mathlib** — Loogle/grep find only the level-1 `ModularForm.E` + its q-expansion; there is no p-stabilisation layer, and `rjwEisenstein`/`stabilisedEisenstein`/`pScale`/`zetaNeg` exist only in `projects/PadicLFunctions/`.
- Composition check (Phase 6): NOT-COMPOSABLE-FROM-MATHLIB (degenerate: mathlib has no relevant primitives); the proof is a one-rewrite (`stabilisedEisenstein_apply`, project-local) + unfold `rjwEisenstein` + `ring` composition of **project-local** facts. Call sites (6.0): K = 0 internal uses, no inline re-derivation.

**Rationale (1–2 paragraphs):**

`stabilisedEisenstein_smul_apply` is a **project-internal bridge lemma** that converts the p-stabilised Eisenstein series between two normalisation conventions: LeanModularForms/mathlib's constant-term-1 `ModularForm.E` (carried by the modular-form object `stabilisedEisenstein`) and RJW's classical constant-term-`ζ(1−k)/2` normalisation (carried by the function `rjwEisenstein := (ζ(1−k)/2)·ModularForm.E`). Its entire mathematical content is "the scalar `ζ(1−k)/2` distributes over the p-stabilisation difference", which the proof discharges by rewriting with the project's own `stabilisedEisenstein_apply` and then `ring`. The literature search confirms the p-stabilisation *operation* is standard, but it equally confirms that *this* statement — a conversion between two normalisations, one of them defined in this very file — is not a named result anywhere; papers fix a single normalisation and never isolate the conversion as a lemma. Mathlib has only the level-1 `ModularForm.E` and its q-expansion; it has **no** p-stabilisation machinery, and crucially the two objects this theorem relates (`stabilisedEisenstein`, `rjwEisenstein`) do not exist in mathlib at all.

Because the statement is *not expressible in mathlib* (it mentions four project-local definitions) and its proof is a one-rewrite-plus-`ring` composition of project-local facts, it cannot be a mathlib contribution in its current form. It is exactly the kind of glue that lives in a downstream development to tie its own definitions together. The closest mathlib-shaped fact hiding inside it — "a scalar distributes over `f − c·g`" — is just `mul_sub`/`ring` and is already fully available in mathlib; there is no new general lemma to extract. The verdict is therefore `NO-composable-from-mathlib`: keep the lemma in the project (it is the human-facing bridge the file's docstring advertises), but it stays local — nothing is upstreamed. (This is a NO verdict, so no further mechanical weakening or generalisation is pursued; the cosmetic `4 ≤ k → 3 ≤ k` slack is a project-local cleanup matter, not a mathlib concern.)

**WHY not (refactor-actionable detail):**
Mathlib has the only genuinely-general building block in play — scalar distributivity over subtraction (`mul_sub`, or just `ring`) — but it does **not** have, and cannot state, the rest: the objects `stabilisedEisenstein`, `rjwEisenstein`, `pScale`, `zetaNeg` are defined exclusively in `projects/PadicLFunctions/`. So the theorem is a 1-step composition (`stabilisedEisenstein_apply` then `ring`) of project-local facts, with the only mathlib ingredient being `ring`. No new mathlib lemma is warranted.

Mathlib building blocks: `mul_sub` / the `ring` tactic (`Mathlib/Tactic/Ring/...`) — for the scalar distributivity. (That is the *entire* mathlib content; everything else is project-local.)

Composition sketch (the actual proof, ≤3 lines):
```lean
example {k : ℕ} (hk : 4 ≤ k) (z : ℍ) :
    (((zetaNeg (k - 1) : ℚ) : ℂ) / 2) * stabilisedEisenstein p (k := k) (by omega) z
      = rjwEisenstein (k := k) (by omega) z
        - (p : ℂ) ^ (k - 1) * rjwEisenstein (k := k) (by omega) (pScale p z) := by
  rw [stabilisedEisenstein_apply, rjwEisenstein, rjwEisenstein]; ring
```

Call sites in our project (from Phase 6.0): **K = 0**.

Refactor plan: **none required, and nothing to upstream.** Because K = 0, there is nothing to inline at consumers today. The lemma should be **kept in the project** as the intended bridge between `stabilisedEisenstein` (the `ModularForm` object) and `rjwEisenstein` (RJW's normalisation) — its docstring at `EisensteinComplex.lean:29`/`:334` advertises exactly this role, and it is the natural statement that connects the modular-form object to the q-expansion theorem `hasSum_stabilisedEisenstein`. Do **not** open a mathlib PR: the statement names four project-local definitions and so is outside mathlib's scope; the only mathlib-general fact inside it (`ring`/`mul_sub`) is already in mathlib. Optional project-local tidy (not a mathlib action): relax `hk : 4 ≤ k` to `3 ≤ k` to match the actual requirement of the constituents, if a future consumer wants the wider range.

Next action: **no mathlib action.** Keep `stabilisedEisenstein_smul_apply` local to `PadicLFunctions`; it is correct, sorry-free, and is the project's own normalisation bridge. (If desired, a cleanup ticket may widen `4 ≤ k` to `3 ≤ k`, but that is internal hygiene, not upstreaming.)

---

## Next step

No mathlib action. Keep `PadicLFunctions.stabilisedEisenstein_smul_apply` local to the project — it is a project-internal bridge between two project-local normalisations (`stabilisedEisenstein` ↔ `rjwEisenstein`), not expressible in mathlib, and its only mathlib-general ingredient is `ring`/`mul_sub`, which mathlib already provides. Optionally relax `hk : 4 ≤ k` to `3 ≤ k` as project-local hygiene.
