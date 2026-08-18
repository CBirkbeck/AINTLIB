# `/mathlibable` report — `PadicLFunctions.noMeasure_interpolates_pPow`

> Mode A — full 10-phase workflow with the exhaustive 9-channel literature search.
> Run date: 2026-06-19. Verdict at the bottom.

---

### Baseline (Phase 0)

- lake build:               build not re-run; reasoned from source (per task BUILD NOTE — `.lake/build` artifacts are stale/slow here; mathlib present at `.lake/packages/mathlib`). The declaration and every dependency (`PadicMeasure`, `unitsPowCM`, `norm_apply_le`, the private helper `units_pow_totient_sq_sub_self_mem`) were read directly from source.
- decl `PadicLFunctions.noMeasure_interpolates_pPow`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/EisensteinFamily.lean:308`
- kind:                      theorem
- has sorry:                 no (the file is sorry-free; `grep` for `sorry`/`admit` in `EisensteinFamily.lean` returns nothing, and the proof terminates in `omega`)
- module docstring summary:  "The p-adic family of Eisenstein series (RJW §8, TeX 2361–2446)" — the Kubota–Leopoldt pseudo-measure interpolates the *constant* coefficients of the p-stabilised Eisenstein series; the non-constant coefficients are interpolated by divisor-sums of Dirac measures; the constant term is only a *twisted pseudo-measure* (erratum #11), and this negative result motivates why.

---

### Statement (Phase 1)

`PadicLFunctions.noMeasure_interpolates_pPow` is **a theorem** stating the following:

There is **no** `ℤ_[p]`-valued measure `θ` on the units `ℤ_[p]ˣ` whose positive-integer
moments are the powers of `p`. Concretely: writing a "measure" in the Iwasawa-theory sense
as a `ℤ_[p]`-linear functional `θ : C(ℤ_[p]ˣ, ℤ_[p]) → ℤ_[p]`, and writing the `k`-th
moment as `θ(x ↦ x^k) = ∫_{ℤ_[p]ˣ} x^k dθ`, the claim is

  `¬ ∃ θ,  ∀ k > 0,  ∫_{ℤ_[p]ˣ} x^k dθ = p^k`.

This is a **rigidity / non-existence statement**: the sequence `k ↦ p^k` is *not* the
moment sequence of any (bounded) measure on `ℤ_[p]ˣ`. The mathematical mechanism is the
boundedness of measures (`‖θ(f)‖ ≤ ‖f‖`, RJW Def. 3.6 footnote): if such a `θ` existed,
then at congruence level `p²` the monomials `x^K` and `x^1` agree modulo `p²` on `ℤ_[p]ˣ`
(for `K = 1 + φ(p²)`, by Euler/Lagrange in `(ℤ/p²)ˣ`), so `‖x^K − x^1‖ ≤ p^{-2}` as a
sup norm. Boundedness forces `‖p^K − p‖ ≤ p^{-2}`. But `‖p^K − p‖ = ‖p‖·‖p^{K−1} − 1‖ =
p^{-1}` (the second factor has norm one by the ultrametric isosceles, since `K − 1 =
φ(p²) ≥ 1`), and `p^{-1} ≤ p^{-2}` is false. The docstring notes `p = 2` is allowed (no
oddness hypothesis is used). This is RJW's motivating remark at TeX 2379–2383 — it is the
reason the constant coefficient `A₀ = x·ζ_p/2` of the Eisenstein family must be a *twisted
pseudo-measure*, not a genuine measure.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the residue characteristic. (Note: `p = 2` IS allowed;
  the docstring flags that no `hp2 : p ≠ 2` is used.)

Hypotheses (Lean side): none (beyond the ambient `Fact p.Prime`). The theorem is a closed
negative statement.

Conclusion (math): the function `k ↦ p^k` is not the moment sequence of any measure on
`ℤ_[p]ˣ`.

Conclusion (Lean):
`¬ ∃ θ : PadicMeasure p ℤ_[p]ˣ, ∀ k : ℕ, 0 < k → θ (PadicMeasure.unitsPowCM p k) = (p : ℤ_[p]) ^ k`.

**Objects this statement is built from (all project-local):**
- `PadicMeasure p X` — an **`abbrev`** for `C(X, ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]`, the
  *linear-functional* notion of a p-adic measure (RJW Def. 3.6;
  `projects/PadicLFunctions/PadicLFunctions/Measure/Basic.lean:52`). This is the
  Iwasawa-theory "measure = bounded linear functional on continuous functions" convention,
  **not** mathlib's `MeasureTheory.Measure`.
- `PadicMeasure.unitsPowCM p k` — the continuous map `u ↦ (u : ℤ_[p])^k` on `ℤ_[p]ˣ`
  (`Measure/PseudoMeasure.lean:650`); `θ (unitsPowCM p k)` is the `k`-th moment.
- `PadicMeasure.norm_apply_le` — the boundedness `‖θ f‖ ≤ ‖f‖` of every such functional
  (`Measure/Basic.lean:109`); this is the load-bearing input.
- `units_pow_totient_sq_sub_self_mem` — the private helper (`EisensteinFamily.lean:280`):
  `u^{1+φ(p²)} − u ∈ (p²)` for every `u : ℤ_[p]ˣ` (Euler/Lagrange mod `p²`).

Proof body (≈40 lines): set `K = 1 + φ(p²)` (with `φ(p²) ≥ 2`); show the sup-norm bound
`‖unitsPowCM K − unitsPowCM 1‖ ≤ p^{-2}` via `ContinuousMap.norm_le` +
`PadicInt.norm_le_pow_iff_mem_span_pow` + the helper; transport it through `θ` by
`norm_apply_le` to get `‖p^K − p‖ ≤ p^{-2}`; compute `‖p^K − p‖ = p^{-1}` by factoring
`p·(p^{K−1} − 1)` and the ultrametric isosceles (`PadicInt.norm_add_eq_max_of_ne`); finish
with `zpow_le_zpow_iff_right₀` + `omega` on `-1 ≤ -2` (false).

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a self-contained negative *remark* feeding the §8 narrative. It is RJW's motivation
(TeX 2379–2383) for why the Eisenstein family's constant term is a pseudo-measure; it is
**not** listed under the module's main results, **not** a named theorem, and introduces no
new structure. It is one short illustrative rigidity fact, decorated with a private helper.

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded only for the
report's framing — it does not gate which channels Phase 3 ran.)

### One-line check (Phase 2b)

Body line count: ≈40 substantive lines.
One-liner verdict: **n/a — kind is `theorem`, not `def`.**
(The one-line def-exemption analysis does not apply to a proof; the section is skipped.)

---

### Literature search table — EXHAUSTIVE protocol

The mathematical concept is the **distribution-vs-measure boundedness dichotomy in
Iwasawa theory**: a p-adic *distribution* is a *measure* iff it is bounded, and a candidate
moment sequence with the "wrong" growth/congruence behaviour is *not* a measure. The
specific instance — `k ↦ p^k` is not a moment sequence on `ℤ_[p]ˣ` — is searched as the
RJW project context.

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "p-adic measure on Z_p units moments not interpolated boundedness Mazur measure rigidity"              | yes  | Mazur's measure on `ℤ_p^×`; measures are bounded linear functionals; the Mellin/Amice transform | Wilson/Williams Warwick notes (= RJW), Katz "p-adic interpolation of Eisenstein series", Wiese study group notes. The *boundedness* of Mazur's measure is itself a theorem; an unbounded candidate is not a measure. |
|  2 | WebSearch (general form)         | "no p-adic measure whose k-th moment is p^k unbounded distribution not a measure Iwasawa"              | yes  | **"The k-th Bernoulli distribution µ_{B,k} is unbounded, so it is not a measure."** | dergipark "Regularization of p-Adic Distributions"; this is the canonical genus — a natural distribution fails to be a measure precisely by *unboundedness*; regularization (Mazur's `μ_{c}` trick) fixes it. The target is a *different* unbounded candidate (`p^k`) of the same genus. |
|  3 | WebSearch (named-after / aliases)| "Amice transform p-adic measure bounded distribution moments characterization continuous functions Z_p"| yes  | "The Amice transform is an isometry between measures on `ℤ_p` and power series with **bounded** coefficients in `ℚ_p`." | Ploner (Wiese notes), Colmez "Fontaine's rings and p-adic L-functions". The Amice transform makes "measure ⟺ bounded" precise; **"each bounded measure is uniquely determined by its values at all monomials `x^m`"** (= moments). |
|  4 | ChatGPT MCP                      | (intended: "standard form + generality + historical evolution of 'a candidate moment sequence is not a measure because measures are bounded'") | n/a  | —                                                    | **`chatgpt-math` MCP not callable this session.** The server (`ask_chatgpt_math`, shelling to a local Codex binary) is configured in `~/.claude.json`, the Codex binary exists, but the server is listed in `~/.claude/mcp-needs-auth-cache.json` as `plugin:mathlib-quality:chatgpt-math` (needs-auth) and no `ask_chatgpt_math` tool is exposed to this harness (ToolSearch returns "no matching deferred tools"). Substituted extra WebSearch + WebFetch depth (rows 1–3, 5–10) per the skill's MCP-absent fallback. |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/`; `refs/PadicLFunctions/`                  | n/a  | (both directories absent)                            | No project references dir; no `refs/` store on this machine (`ls refs/` → not found). Recorded n/a. The source paper (RJW arXiv:2309.15692) is cited inline in the docstrings (TeX 2379–2383). |
|  6 | nLab                             | WebFetch `ncatlab.org/nlab/show/Iwasawa+theory`; Wikipedia "P-adic distribution" as the abstract-definition source | yes  | **"A p-adic distribution taking values in a normed space is called a p-adic measure if the values on compact open subsets are bounded."** (Wikipedia, verbatim) | nLab "Iwasawa theory" treats the Iwasawa *algebra* `ℤ_p[[Γ]]`/main conjecture, **not** the distribution-vs-measure boundedness dichotomy (recorded). Wikipedia's "P-adic distribution" is the clean abstract anchor: measure = *bounded* distribution. |
|  7 | nCatLab (if categorical)         | (covered by nLab Iwasawa-theory page; "a candidate moment sequence is not a measure" is not a higher-categorical concept) | n/a  | —                                                    | Not a categorical concept. The nLab page (row 6) is the relevant abstract source; no separate nCatLab entry. |
|  8 | Stacks Project (if alg geom)     | —                                                                                                      | n/a  | —                                                    | Not an algebraic-geometry concept (p-adic measure moments / Iwasawa-theory rigidity). |
|  9 | MathOverflow / Math.StackExchange| "which sequences are moments of p-adic measure on Z_p units continuous interpolation necessary condition not sufficient" | yes  | "A bounded sequence in `ℚ_p` defines a unique bounded p-adic measure (via Mahler coefficients); boundedness is *necessary*." | Returned the Mahler-coefficient characterisation (a `ℤ_p`-valued continuous function on `ℤ_p`, equivalently a bounded measure, is recovered from `c_0`-Mahler data). Confirms the rigidity: not every formal moment sequence is a measure; boundedness is the gate. (Note: the *monomial* moments `x^k` differ from Mahler coefficients, but both are determined by/determine the bounded measure.) |
| 10 | recent arXiv (last 5 years)      | "p-adic L-functions Eisenstein family pseudo-measure constant term boundedness measure not interpolate p^k"; "Formalization of p-adic L-functions in Lean" | yes  | **arXiv:2309.15692** (RJW, v2 Dec 2024) — the exact source; **arXiv:2302.14491** (Narayanan, "Formalization of p-adic L-functions in Lean 3") | RJW §8 is the family of Eisenstein series + pseudo-measures interpolating `L`-values of `p`-power-conductor characters — the project's source. Narayanan formalised the *same* "measure = bounded linear functional" notion + Bernoulli measures, **in a separate repo `github.com/laughinggas/p-adic-L-functions`, NOT merged to mathlib** (decisive for Phase 5). |

The protocol passed: WebSearch ran 3 distinct generality levels (rows 1–3 — specific
`p^k`-on-units form; the general "unbounded distribution is not a measure" form; the
Amice-transform named form); the ChatGPT MCP row is honestly recorded n/a (tool not
callable) with the fallback substitution noted; local refs checked (absent → n/a with
reason); nLab/Wikipedia checked (hit — verbatim definition); nCatLab/Stacks recorded n/a
with reasons; MathOverflow/SE perspective captured (row 9); recent arXiv located both the
exact source paper AND the prior Lean formalization (row 10).

### Literature summary (Phase 3)

Concept identified as: **the distribution-vs-measure boundedness dichotomy** of Iwasawa
theory — a p-adic *distribution* is a *measure* precisely when it is **bounded**
(`‖θ(f)‖ ≤ C‖f‖`); equivalently (Amice transform) when its generating power series has
bounded coefficients. A candidate moment sequence that would force an *unbounded* functional
is therefore **not** realised by any measure. The target is the concrete instance: `k ↦ p^k`
is not the moment sequence of any measure on `ℤ_[p]ˣ`.

Sources agree on the standard form: **yes.** Wikipedia ("P-adic distribution", verbatim):
"A p-adic distribution … is called a p-adic measure if the values on compact open subsets
are bounded." The Bowers/Conrad survey ("p-Adic Measures and Bernoulli Numbers") and the
regularization literature state the textbook exemplar: "the k-th Bernoulli distribution
`µ_{B,k}` is unbounded, so it is not a measure", repaired by Mazur's regularization. The
Amice-transform formulation (measures ⟺ bounded-coefficient power series; "a bounded measure
is determined by its values at all monomials `x^m`") is standard (Colmez, the Wiese notes).

Most general standard form: for a topological space `X` and a normed coefficient ring, a
*distribution* is a finitely-additive functional on locally constant / continuous functions;
it is a *measure* iff bounded. The **decision problem** "is this sequence a moment sequence of
a measure?" reduces to a boundedness check. The target is the special case `X = ℤ_[p]ˣ`,
coefficients `ℤ_[p]`, candidate moments `p^k` — answered *no* by an explicit two-level (`p²`)
congruence obstruction.

Generality dimensions where the literature varies:
- **Notion of "measure".** Classical/mathlib analysis: countably-additive `MeasureTheory.Measure`
  on a σ-algebra. RJW / Iwasawa theory (this project, and Narayanan's Lean-3 work): a *measure
  is a bounded `ℤ_[p]`-linear functional* on `C(X, ℤ_[p])` — the continuous dual. The target
  lives entirely in the latter framework; its content (`norm_apply_le`) is *definitional* to
  that framework.
- **Which obstruction is exhibited.** The literature's canonical witness is *growth/unboundedness*
  of Bernoulli/`p^k`-type distributions; RJW's specific witness here is a clean **congruence**
  obstruction at level `p²` (Euler/Lagrange in `(ℤ/p²)ˣ`), which is a sharper, finitary route
  to the same "unbounded ⟹ not a measure" conclusion. Mathematically identical genus.
- **Coefficient ring.** Most general: the source's `𝒪_L`-valued measures (RJW §5). Here it is
  `ℤ_[p]`; the project explicitly defers the general `𝒪_L` case.

Disagreement with the literature: **none.** The declaration is a faithful, correct instance of
the standard "an unbounded candidate is not a measure" phenomenon. It is **not** a re-statement
of a universally-named theorem; it is RJW's bespoke motivating example (TeX 2379–2383) that
*instantiates* a textbook dichotomy for a project-specific candidate sequence.

---

### Generality analysis — `PadicLFunctions.noMeasure_interpolates_pPow`

Literature-standard form (from Phase 3): "a p-adic distribution is a measure iff bounded;
hence a candidate moment sequence whose realisation would be unbounded is not a measure."
The maximally-general *theorem* of this genus would be a boundedness criterion / a
characterisation of moment sequences of measures — a much larger object than this one
instance.

| # | Parameter / hypothesis            | Current Lean form                                  | Literature-standard form                              | Weaker/more-general form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|----------------------------------------------------|-------------------------------------------------------|----------------------------------|---------------------------------|
| 1 | the candidate sequence `k ↦ p^k`  | the specific sequence `p^k`                         | *any* candidate moment sequence; or the full "bounded ⟺ measure" criterion | yes (in principle)               | The general statement is a *characterisation theorem* (moments of measures ⟺ boundedness), not a generalisation of *this* instance — and it would be stated over the same non-mathlib `PadicMeasure` type. Different, much bigger object; see Phase 6/7. |
| 2 | the space `ℤ_[p]ˣ`                 | units of `ℤ_[p]`                                    | a general profinite/compact `X` (e.g. `ℤ_[p]`)        | partial                          | The congruence obstruction uses the group structure of `(ℤ/p²)ˣ` and Euler's theorem; the *phenomenon* (unbounded ⟹ not a measure) is space-agnostic, but *this proof* is `ℤ_[p]ˣ`-specific. Generalising the space changes the witness, not the genus. |
| 3 | coefficient ring `ℤ_[p]`          | p-adic integers                                     | the source's `𝒪_L`-valued measures (RJW §5)          | yes (deferred)                   | The project deliberately defers general `𝒪_L` coefficients (`Measure/Basic.lean` docstring). Not a weakening available *now* without that infrastructure. |
| 4 | `[Fact p.Prime]` (incl. `p = 2`)  | any prime; `p = 2` allowed (docstring flags it)     | any prime                                             | already maximal                  | No oddness assumption is used — already the most general primality hypothesis. Good. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN the literature-standard *phenomenon*, but
NOT in a way that yields a mathlib-worthy regeneralisation of this decl.** The only genuine
"more general" target is a *characterisation theorem* (moment sequences of measures ⟺
boundedness) or a generic "an unbounded candidate is not a measure" lemma — a *different,
larger* object, and one stated over the project's non-mathlib `PadicMeasure` type. Weakening
the space (row 2) swaps one bespoke witness for another; weakening the coefficient ring (row 3)
is deferred project infrastructure; the primality hypothesis (row 4) is already maximal.

Number of weakening opportunities found: **0** that yield a *mathlib-worthy regeneralisation
of this specific lemma*. (The "characterisation theorem" direction is a new, bigger result —
appropriately handled as a BORDERLINE question, not an in-place generalise-first restatement.)

Proposed restatement (if STRICTLY NARROWER): **none of *this* lemma.** A generic
"`unbounded-candidate ⟹ not a measure`" or a "moments ⟺ boundedness" characterisation would
be the right *mathlib* target, but (i) it is a different theorem, not a restatement, and (ii)
it presupposes the `PadicMeasure` (continuous-dual) framework, which is not in mathlib — so it
cannot be a self-contained YES-but-generalise restatement here. See Phase 7.

Cost of restatement: n/a (no in-place restatement; the general theorem is separate new work).

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                  | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|-------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                        | no       | —                      | Hypotheses are already minimal (`Fact p.Prime`); nothing to typeclass-ify. |
|  2 | sequences/metric → filters/topological?                                                   | no       | —                      | The "sequence" `k ↦ p^k` is the *object of study* (a candidate moment sequence indexed by `k`), not a convergence notion to filter-ise. The proof's only limit-like step is a finitary norm comparison. |
|  3 | construct an object where a universal-property class would characterise it?               | no       | —                      | This is a *non-existence* statement; no object is constructed. |
|  4 | set-with-closure-predicate → bundled-substructure type?                                    | no       | —                      | No substructure involved. |
|  5 | vector-space/metric/field-specific → weaken to modules/pseudometric/(semi)ring?           | partial  | (would re-aim at a generic "bounded functional ⟹ moment constraint" over an abstract continuous-dual) | The abstraction is exactly the row-1/row-2 generalisation of Phase 4a; but the target type ("measure = continuous dual of `C(X, ℤ_[p])`") is not a mathlib concept, so there is no mathlib downstream — it would be a *new framework + new characterisation theorem*, not a modern restatement of *this* lemma. Flagged, not recommended as an in-place move. |
|  6 | 1-categorical → higher/∞-categorical?                                                       | no       | —                      | Not categorical. |
|  7 | concrete index (ℕ, ℤ, ℝ) → arbitrary additive groups/monoids/ordered structures?          | no       | —                      | The exponent `k` and the prime `p` are intrinsically arithmetic; the congruence obstruction is specifically about `(ℤ/p²)ˣ`. Generalising removes the content. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for a mathlib contribution that is a *restatement of this
lemma*).
Reason: the only abstraction on offer (row 5 — a generic "bounded functional forbids this
moment sequence" / a "moments ⟺ boundedness" characterisation) is stated over the project's
linear-functional `PadicMeasure` type, which is itself not in mathlib. There is no contemporary
mathlib idiom that turns *this* one-instance non-existence fact into a better *mathlib* lemma;
the abstraction would first require upstreaming the whole "p-adic measure = continuous dual"
framework (the exact thing Narayanan's Lean-3 work kept in a separate repo) — a separate, much
larger question (see Phase 7).

---

### Diamond / defeq risk — `PadicLFunctions.noMeasure_interpolates_pPow`

**n/a — declaration kind is `theorem`.** (No definitional equalities or typeclass-search
paths are introduced by a proof; Phase 4.5 is skipped per the skill's scope rule.)

### Risk verdict (Phase 4.5)

Overall risk: **n/a (theorem)**.

---

### Mathlib search-status: `PadicLFunctions.noMeasure_interpolates_pPow`

[A] Lean-Finder       — (server not configured this session; substituted by direct mathlib-source grep [D] + name-pattern [E], authoritative on the local pinned mathlib).  n/a: tool unavailable.
[B] Loogle (type-pattern) — searched `.lake/packages/mathlib` for the `PadicMeasure` *type* `C(X, ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]` and for any "no measure with prescribed moments / unbounded ⟹ not a measure" pattern.  **no hit** (the type itself is absent — see [E]).  Server not configured; pattern-grep substituted.
[C] LeanSearch (NL)   — concept "p^k is not the moment sequence of a p-adic measure on the units / a distribution is a measure iff bounded" — covered by the literature search (Phase 3) + grep below.  n/a: server not configured; substituted by [D]/[E].
[D] Grep mathlib src  — terms tried: `PadicMeasure`, `C(.*, ?ℤ_\[p\]) →ₗ`, `padic.*distribution`, `Iwasawa`, `bernoulliMeasure`, `kubota`/`Kubota`, `padicLFunction`, `Amice`, `mahler`/`Mahler`, `unitsPowCM`, `noMeasure`/`interpolat`/`pPow`, `moment.*measure`.  Hits found only for *different* objects (see below).
[E] Name pattern      — `PadicMeasure`, `unitsPowCM`, `noMeasure_interpolates_pPow` — exist **only** in this project; **zero** mathlib hits. The grep `C(.*, ?ℤ_\[p\]) →ₗ` over all of `Mathlib/` returns **empty** — the linear-functional p-adic-measure type is not in mathlib.

Searched for both:
- the user's current form (no measure with moments `p^k` over the project's `PadicMeasure`) —
  **no mathlib hit** (the objects are project-local; the prior Lean-3 formalization of this
  exact notion lives in a *separate* repo, not mathlib — arXiv:2302.14491).
- the literature-standard form (the boundedness dichotomy / a moment-sequence characterisation)
  — mathlib has only **orthogonal / unrelated** pieces:
  - `Mathlib/GroupTheory/GroupAction/Iwasawa.lean` — the **group-theoretic Iwasawa criterion**
    (`IwasawaStructure`, BN-pairs, a simplicity criterion). **Unrelated** to Iwasawa theory of
    p-adic L-functions / measures.
  - `Mathlib/Probability/Distributions/Bernoulli.lean`, `.../Moments/*` — **probability**
    Bernoulli distributions and **probability** moments (MGF). A *different mathematical
    encoding* (real/complex measure theory), not the Iwasawa Bernoulli *measure* nor the
    `ℤ_[p]`-functional moments here.
  - `Mathlib/NumberTheory/Padics/MahlerBasis.lean` — the **Mahler basis** for `C(ℤ_[p], E)`
    (`mahler`, `mahlerSeries`, `mahlerEquiv : C(ℤ_[p], E) ≃ₗᵢ[ℤ_[p]] C₀(ℕ, E)`). This is the
    *function-side* of the Amice picture — but mathlib has **no measure / dual / Amice-transform
    layer on top of it**, and nothing about `ℤ_[p]ˣ`-moments or the non-existence statement.
  - `Mathlib/RingTheory/Teichmuller.lean`, `Mathlib/NumberTheory/Padics/{PadicIntegers,ProperSpace}.lean`,
    `ArithmeticFunction/Carmichael.lean`, `DirichletCharacter/Bounds.lean` — supply the *generic
    plumbing* the proof uses (`PadicInt.norm_add_eq_max_of_ne`, `norm_le_pow_iff_mem_span_pow`,
    `Nat.totient_prime_pow`, `pow_card_eq_one'`) — but these are generic lemmas, not this
    statement.

Concluded: **not in mathlib** (all available methods exhausted, plus the literature-standard
form). Decisively, the *carrier type* `PadicMeasure p X = C(X, ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]` is
absent from mathlib (grep empty), so neither this non-existence statement nor any
characterisation it could generalise to is expressible in mathlib today. mathlib's `Iwasawa`,
`Bernoulli`, `Moments`, and `MahlerBasis` are unrelated encodings or the function-side only.

---

### Call sites — `PadicLFunctions.noMeasure_interpolates_pPow`

Internal use count: **K = 0** (within the project, NOT counting the declaring file). The
repo-wide grep `grep -rn "noMeasure_interpolates_pPow" projects --include="*.lean"` returns
**only the declaration line itself** (`EisensteinFamily.lean:308`).
External-to-file / external-to-project callers: **0**.

| Caller file:line               | Usage pattern (one-line excerpt)                          |
|--------------------------------|-----------------------------------------------------------|
| (none)                         | — no caller anywhere in the repository                    |

Inline-derivation grep (was the equivalent re-derived elsewhere without using
`noMeasure_interpolates_pPow`?): **(none)** — no other site proves a non-existence-of-measure
statement by hand. The private helper `units_pow_totient_sq_sub_self_mem`
(`EisensteinFamily.lean:280`) is used *only* inside this theorem (and its own docstring).

What this tells us: **K = 0**, no external consumers, no inline re-derivation. This is a
**standalone motivating remark** — RJW's TeX 2379–2383 justification for why the family's
constant term is a pseudo-measure, formalised for the record. It is *not* dead code in the
pejorative sense (it documents a real mathematical reason behind the design of the rest of the
file), but it is also *not* load-bearing API: nothing downstream calls it. Per the Phase-6.0
signal table, `K = 0` with no inline re-derivation reads as "genuinely-new + currently-unused"
→ leans BORDERLINE (junk vs. genuine-but-unused), reinforced by the fact that the *object it is
stated over* (`PadicMeasure`) is not in mathlib.

### Composition check (Phase 6)

Can `noMeasure_interpolates_pPow` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: find a mathlib lemma "no measure has moments `aⁿ`" / "an unbounded sequence is not a
moment sequence" and specialise.
  - Mathlib decls used: (searched) `MeasureTheory.*`, `Iwasawa*`, `bernoulli*`, `mahler*`.
  - Result: **fails** — no such lemma exists, and it is not even *expressible*: the statement
    quantifies over `θ : PadicMeasure p ℤ_[p]ˣ = C(ℤ_[p]ˣ, ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]`, a type
    absent from mathlib. There is no mathlib object to specialise from.

Attempt 2: assemble it from the generic mathlib plumbing the proof uses.
  - Mathlib decls used: `ContinuousMap.norm_le`, `PadicInt.norm_le_pow_iff_mem_span_pow`,
    `PadicInt.norm_add_eq_max_of_ne`, `Nat.totient_prime_pow`, `pow_card_eq_one'`,
    `zpow_le_zpow_iff_right₀`.
  - Result: **NOT a composition** — this is precisely the ≈40-line proof. It is a *multi-step
    real argument* (congruence helper `units_pow_totient_sq_sub_self_mem`, a sup-norm bound, a
    transport through `θ` via the **project** lemma `PadicMeasure.norm_apply_le`, an ultrametric
    isosceles norm computation, then a contradiction), and it crucially uses the **project**
    objects `PadicMeasure`, `unitsPowCM`, and `norm_apply_le`. Per the Phase-6 heuristics table
    ("multiple `have`s with non-trivial reasoning between" / "requires `rw`/`omega` chains") this
    is a proof, not a ≤3-call composition. Stripped of the project objects there is no statement
    left to inline.

Conclusion: **NOT-COMPOSABLE from mathlib.** Mathlib neither contains the objects the statement
names (`PadicMeasure`, `unitsPowCM`), nor the non-existence fact, nor a parent it specialises
from. The proof's mathlib content is generic norm/totient plumbing; the substance (boundedness
rigidity over the project's continuous-dual measures) is project-local and cannot be inlined into
mathlib at all.

---

## Verdict: `PadicLFunctions.noMeasure_interpolates_pPow`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the underlying phenomenon (a p-adic *distribution* is a
  *measure* iff **bounded**; an unbounded candidate moment sequence is not a measure) is
  textbook-standard — Wikipedia "P-adic distribution" (verbatim definition), the Bowers/Conrad
  survey and the regularization literature ("the Bernoulli distribution is unbounded, so it is
  not a measure"), the Amice-transform characterisation (Colmez, Wiese notes). The *specific*
  declaration — `k ↦ p^k` is not a moment sequence on `ℤ_[p]ˣ` — is RJW's bespoke motivating
  remark (arXiv:2309.15692, TeX 2379–2383), not a universally-named theorem.
- Generality analysis (Phase 4): STRICTLY NARROWER than the literature *phenomenon*, but with
  **0** mathlib-worthy in-place regeneralisations of *this* lemma — the only larger target is a
  *characterisation theorem* (moments of measures ⟺ boundedness), a different and bigger object
  stated over the same non-mathlib type. Modern-idiom: none for a mathlib contribution.
- Mathlib search (Phase 5): **not in mathlib**, and the carrier type `PadicMeasure = C(X, ℤ_[p])
  →ₗ ℤ_[p]` is itself absent (grep empty). mathlib's `Iwasawa` (group-theory criterion),
  `Bernoulli`/`Moments` (probability), and `MahlerBasis` (function-side only) are unrelated
  encodings. The prior Lean-3 formalization of exactly this measure notion (Narayanan,
  arXiv:2302.14491) was kept in a *separate* repo, never upstreamed.
- Composition check (Phase 6): **NOT-COMPOSABLE** from mathlib — the statement names objects
  mathlib lacks; the proof is a ≈40-line real argument over project-local objects, not a ≤3-call
  inlining. Call sites: **K = 0** repo-wide.

**Rationale (why BORDERLINE, not a clean bucket):**

`noMeasure_interpolates_pPow` is a correct, faithful instance of a genuinely standard Iwasawa-
theory phenomenon — the boundedness rigidity that separates p-adic *distributions* from
*measures* — exhibited via a clean finitary congruence obstruction at level `p²`. It is *good
mathematics* and a nice formalisation. But it is stated over objects that exist **only in this
project**: the linear-functional notion of a p-adic measure (`PadicMeasure = C(X, ℤ_[p]) →ₗ
ℤ_[p]`, RJW Def. 3.6) and the monomial moment maps `unitsPowCM`. None of these is in mathlib;
the grep for the carrier type returns empty, and the one prior Lean formalization of the same
notion (Narayanan) deliberately stayed in a standalone repository. So the four "mechanical"
buckets all fail their gates: **NO-mathlib-has-it** is wrong (Phase 5 found no decl — and no
expressible statement — over these objects); **NO-composable-from-mathlib** is wrong (Phase 6 is
NOT-COMPOSABLE: you cannot inline a non-existence-of-`PadicMeasure` statement into mathlib, the
type does not exist there, and the proof is a real ≈40-line argument); **YES-add-as-is** /
**YES-but-generalise-first** are both premature, because shipping *this single-instance remark*
to mathlib is meaningless without first upstreaming the entire "p-adic measure = continuous
dual" framework it is stated over — and, ideally, in the *general* form of the underlying
phenomenon (a boundedness criterion / a characterisation of moment sequences of measures), not
this one `p^k` witness. The decisive questions — *should the RJW measure framework go to mathlib
at all, and in what form? and is the right mathlib object the general "moments ⟺ boundedness"
characterisation rather than this one instance?* — are exactly the mathematical-taste /
project-policy / scope calls the skill must not make alone. The call-sites signal (`K = 0`, no
consumers, no inline re-derivation) reinforces this: on its own the lemma is a standalone
motivating remark, which leans toward "keep project-local / document" rather than "upstream a
fragment".

**Numbered questions (≤5):**

1. Is the linear-functional p-adic-measure framework (`PadicMeasure p X = C(X, ℤ_[p]) →ₗ[ℤ_[p]]
   ℤ_[p]`, `norm_apply_le` boundedness, `unitsPowCM`, the `Λ(ℤ_p^×)` convolution algebra)
   something you intend to upstream to mathlib as a *new framework* (distinct from
   `MeasureTheory.Measure`)? If **no**, then `noMeasure_interpolates_pPow` stays project-local
   and this assessment ends as "keep" — there is nothing to PR. If **yes**, this remark becomes a
   small example/illustration that could ship *with* that framework.
2. If the framework is upstreamed: would mathlib want the **general** result of this genus — a
   boundedness criterion / a characterisation "a sequence `a : ℕ → ℤ_[p]` is the moment sequence
   of a measure on `ℤ_[p]ˣ` iff <bounded / Mahler-`c₀> condition>", together with the contrapositive
   "an unbounded candidate is not a measure" — rather than this single `p^k` instance? (Phase 3
   identifies that *general* characterisation as the literature-standard object; the `p^k` case is
   one illustrative witness.)
3. The source explicitly defers the general `𝒪_L`-valued measure case (RJW §5; `Measure/Basic.lean`
   docstring). Should any mathlib contribution wait for that generality, so the framework + its
   measure/distribution rigidity are added once in their general form, rather than the `𝒪 = ℤ_[p]`
   special case?
4. Note that a prior Lean formalization of *exactly* this "measure = bounded linear functional"
   notion (Narayanan, arXiv:2302.14491) exists in a separate repo and was **not** upstreamed. Is
   there a known reason mathlib has not adopted this framework (design disagreement with
   `MeasureTheory.Measure`, lack of a champion, etc.) that should inform whether to attempt it now?
5. Given `K = 0` and that this is a motivating remark rather than load-bearing API, is it
   acceptable to simply **keep** `noMeasure_interpolates_pPow` project-local as documentation of
   the §8 design choice (the constant term being a pseudo-measure), with no mathlib PR — which is
   the natural call if Q1 = no?

**Next action:** user answers questions 1–5; re-run `/mathlibable
PadicLFunctions.noMeasure_interpolates_pPow` to resolve the verdict. Likely outcomes:
- Q1 = no (framework stays project-local) → drop from mathlib consideration; **keep** as a
  project-local motivating remark. The theorem is correct and well-documented; nothing to PR.
- Q1 = yes, Q2 = ship the general characterisation → *this* lemma is not the mathlib contribution;
  the mathlib contribution is the framework + the general "moments ⟺ boundedness" theorem (a
  different, more abstract decl), with `p^k` perhaps as a docstring example. Likely
  `YES-but-generalise-first` aimed at that general statement, gated on Q3.
- Q1 = yes, Q3 = wait for `𝒪_L` generality → defer; revisit after the §5 development pass.

---

## Next step

User answers questions 1–5 above; re-run `/mathlibable
PadicLFunctions.noMeasure_interpolates_pPow` to resolve the verdict. (Or commit directly: the
most likely resolution — given the `K = 0` standalone-remark call profile, and the fact that the
`PadicMeasure` framework this lemma is stated over is not in mathlib and its one prior Lean
formalization stayed in a separate repo — is to **keep** `noMeasure_interpolates_pPow` in the
project as documentation of the Eisenstein-family design, and consider upstreaming only the
*generic* p-adic-measure framework together with the *general* "moments ⟺ boundedness"
characterisation, in its general `𝒪_L` form, as a separate and much larger effort.)
