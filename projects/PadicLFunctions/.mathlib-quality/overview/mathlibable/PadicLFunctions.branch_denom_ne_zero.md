# `/mathlibable` report — `PadicLFunctions.branch_denom_ne_zero`

Mode A — single declaration, full 10-phase workflow, exhaustive 9-channel literature search.

---

### Baseline (Phase 0)
- lake build:                **not re-run; reasoned from source** (per task build note — `.lake/build/lib` empty/stale; read the declaration and its full dependency chain directly).
- decl `PadicLFunctions.branch_denom_ne_zero`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ResidueZeta.lean:188`
- kind:                      theorem
- has sorry:                 no (the file `ResidueZeta.lean` has zero `sorry`/`admit`; the proof is complete)
- module docstring summary:  "The residue of ζ_p at s = 1 (RJW §7)" — proves RJW Theorem 7.1: branch `ζ_{p,i}` is continuous at `s = 1` for `i ≠ p−1`, and `ζ_{p,p−1}` has a simple pole there with residue `1 − p⁻¹`. `branch_denom_ne_zero` is the supporting fact that the branch quotient's denominator never vanishes.

---

### Statement (Phase 1)

`PadicLFunctions.branch_denom_ne_zero` is a theorem stating the following:

Let `p` be a prime and `u ∈ ℤ_p^×` a **topological generator** of `ℤ_p^×` (the hypothesis `hgen` says the image of `u` under `unitsToZModPow p n` generates `(ℤ/pⁿ)^×` for every `n`). Fix an exponent `i` with `0 < i < p−1`. Then for **every** `s ∈ ℤ_p`, the value of the branch character minus one is nonzero in `ℚ_p`:
```
(branchChar p i s u : ℤ_p) : ℚ_p) − 1 ≠ 0.
```
Here `branchChar p i s` is the project's continuous character `x ↦ ω(x)^i · ⟨x⟩^s` on `ℤ_p^×` (RJW TeX 1907–1910), where `ω = teichmuller` is the Teichmüller lift and `⟨x⟩ = angleUnit p x = ω(x)⁻¹·x ∈ 1 + pℤ_p`. Evaluated at the generator `u`, `branchChar p i s u = ω(u)^i · ⟨u⟩^s`.

The mathematical content is RJW's **Lemma 7.2(i)**, here *strengthened from `s = 1` to all `s`*: the "branch denominator" `ω(u)^i·⟨u⟩^{1−s} − 1` that appears under the quotient defining the branch `ζ_{p,i}(s)` never vanishes, because `‖ω(u)^i − 1‖ = 1` (the Teichmüller value of a generator is a primitive `(p−1)`-th root of unity, so `ω(u)^i ≢ 1 mod p` for `0 < i < p−1`) strictly dominates `‖⟨u⟩^s − 1‖ < 1` (`⟨u⟩ ∈ 1+pℤ_p` is topologically unipotent), and the **ultrametric "all triangles are isosceles" principle** then forces `‖ω(u)^i·⟨u⟩^s − 1‖ = 1 ≠ 0`.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the prime (section variable).
- `u : ℤ_[p]ˣ` — a unit, required to be a topological generator.

Hypotheses (Lean side):
- `hgen : ∀ n : ℕ, Subgroup.zpowers (PadicMeasure.unitsToZModPow p n u) = ⊤` — `u` is a topological generator of `ℤ_p^×` (its level-`n` reductions generate `(ℤ/pⁿ)^×`).
- `hi0 : 0 < i`, `hi : i < p − 1` — the exponent lies strictly between `0` and `p−1`.
- `s : ℤ_[p]` — an arbitrary `p`-adic "complex variable".

Conclusion (math): the branch-character value at the generator differs from `1`, hence the denominator of the branch quotient `ζ_{p,i}` is nonzero everywhere.

Conclusion (Lean): `(((branchChar p i s u : ℤ_[p])) : ℚ_[p]) - 1 ≠ 0`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: It is a supporting structural lemma (numbered "R7.2b" in the project's decomposition), feeding the main result `branch_continuousAt`/`tendsto_branch_denom_div` in the same file. It is not itself a `## Main result`, not named after a person, and introduces no new structure — it is a non-vanishing fact about the project's already-defined `branchChar`.

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for the report's framing only.)

### One-line check (Phase 2b)

Body line count: ~33 substantive lines (a genuine multi-step `by` proof: sets `ω`, `A`; computes `‖ω^i − 1‖ = 1`, `‖A − 1‖ < 1`, `‖ω^i‖ = 1`; applies the ultrametric isoceles lemma; descends from `ℤ_p` to `ℚ_p`).
One-liner verdict: **n/a — kind is theorem, and body is MULTI-LINE.** The one-liner exemption table is skipped.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "p-adic L-function branch character Teichmuller denominator nonvanishing ultrametric Washington"        | partial | Teichmüller character def; branch ζ_{p,i} structure; no packaged "denom ≠ 0" lemma | Wikipedia Teichmüller character; AWS/Harron notes; Grubb p-adic L notes |
|  2 | WebSearch (general form)          | "Teichmuller character omega(u)^i - 1 norm equals one primitive (p-1)th root of unity p-adic"           | yes  | `ℤ_p^× ≅ μ_{p-1} × (1+pℤ_p)` via `x ↦ (ω(x),⟨x⟩)`; `ω(a)` the unique `(p−1)`-root `≡ a mod p`; `ω(x)=lim x^{pⁿ}` | confirms the decomposition is exactly the project's `teichmuller`/`angleUnit` split |
|  3 | WebSearch (named-after / aliases) | "p-adic zeta function residue s=1 branch decomposition omega^i angle bracket denominator simple pole Jung Washington" | yes | `ζ_{p,i}(s) = ∫_{ℤ_p^×} ω(x)^i ⟨x⟩^{1−s} dζ_p`; `ζ_{p,p−1}` simple pole at `s=1`, residue `1−p⁻¹`; `p−1` branches by residue class | this is precisely the RJW Thm 7.1 setup the project formalises; arXiv 2309.15692 (intro to p-adic L), Williams LTCC notes |
|  4 | ChatGPT MCP                      | (intended: "standard form of the branch-denominator non-vanishing lemma, its generality, historical evolution") | **n/a** | — | **No ChatGPT/OpenAI MCP server is configured in this environment** (only Asana/Atlassian/… PM servers require auth). Compensated with extra WebSearch queries #1–3, #6, #9 at multiple generality levels. |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` and repo `refs/`                           | **n/a** | (directory absent) | No `references/` dir under this project's `.mathlib-quality/`; no `refs/PadicLFunctions/` symlink in the checkout. The file header itself cites "RJW §7, Lemma 7.2(i)" and "Washington" as the source. |
|  6 | nLab                             | "nLab p-adic L-function Kubota-Leopoldt branches Teichmuller decomposition zeta function"                | partial | Kubota–Leopoldt = p-adic analogue of ζ; `p−1` analytic branches, one per residue class mod `p−1`; ω = inverse Teichmüller Dirichlet character | nLab proper returned no dedicated entry for the non-vanishing lemma; general K–L structure confirmed via the linked notes |
|  7 | nCatLab (if categorical)         | —                                                                                                       | **n/a** | — | Not a categorical concept; it is an analytic/arithmetic non-vanishing statement about a specific p-adic character. |
|  8 | Stacks Project (if alg geom)     | —                                                                                                       | **n/a** | — | Not an algebraic-geometry concept; Stacks does not cover p-adic L-functions or Teichmüller characters. |
|  9 | MathOverflow / Math.StackExchange| "p-adic L-function branch nonvanishing denominator Teichmuller pole residue analytic"; "ultrametric all triangles are isosceles norm sub equals max nonarchimedean" | yes (isoceles) | confirms the ultrametric principle "if ρ(x,y) < ρ(x,z) then ρ(x,z)=ρ(y,z)"; notes mathlib `Topology/MetricSpace/Ultra/Basic` | no MO thread packages the *branch-denominator* statement; the *isoceles* engine is standard and already in mathlib |
| 10 | recent arXiv (last 5 years)      | (covered by #1/#3) "An introduction to p-adic L-functions" arXiv:2309.15692 (2023)                      | yes  | gives the branch decomposition and pole-at-`s=1` story; treats non-vanishing as a step, not a named lemma | the modern reference confirms the framing is standard but the specific lemma is internal to such treatments |

### Literature summary (Phase 3)

Concept identified as: the **non-vanishing of the branch-character denominator** in the Teichmüller-branch decomposition of the Kubota–Leopoldt p-adic zeta function — RJW (Washington-style) **Lemma 7.2(i)**, here generalised from `s = 1` to all `s ∈ ℤ_p`.
Sources agree on the standard form: **yes** for the *surrounding objects* (the decomposition `ζ_{p,i}(s)=∫ω^i⟨x⟩^{1−s}`, the Teichmüller split `ℤ_p^×≅μ_{p-1}×(1+pℤ_p)`, the `p−1` branches, the pole/residue at `s=1`), and **yes** for the *engine* (ultrametric isoceles). **No** source presents a *named, packaged* lemma "`ω(u)^i⟨u⟩^{1−s} − 1 ≠ 0` for all `s`" — it is an internal step.
Most general standard form: the underlying mathematical facts are two standard ingredients — (a) `ω(u)` is a primitive `(p−1)`-th root of unity for a generator `u`, so `‖ω(u)^i − 1‖ = 1` for `0<i<p−1`; (b) the ultrametric isoceles law `‖a·b − 1‖ = max(‖a·b − a‖, ‖a − 1‖)` when the two summand-norms differ. Their *combination into this exact `branchChar` non-vanishing statement* is project-specific.
Generality dimensions where the literature varies:
  - The variable: classical treatments often state the denominator fact only at the value needed (`s = 1`); this Lean form generalises to all `s ∈ ℤ_p`. The strengthening is essentially free given the proof (the ultrametric estimate is uniform in `s`).
  - The ambient ring: classical sources work in `ℤ_p`/`ℚ_p`; the *engine* (isoceles) holds in any `IsUltrametricDist` normed field. The *statement*, however, is irreducibly about `branchChar`, `teichmuller`, `angleUnit`, which are defined only over `ℤ_p`.
Disagreement with the literature: none. The Lean statement is a faithful, slightly-strengthened formalisation of RJW Lemma 7.2(i).

A non-empty literature search: the concept is real and standard *as an internal step*, but no external source elevates it to a standalone named lemma — a signal that it is project-specific bookkeeping built on standard pieces.

---

### Generality analysis — `PadicLFunctions.branch_denom_ne_zero`

Literature-standard form (from Phase 3): the two building blocks (`‖ω(u)^i − 1‖ = 1` for a generator; ultrametric isoceles) are maximally general in mathlib already; the *packaged statement* is inherently about the project's `branchChar`.

| # | Parameter / hypothesis                | Current Lean form          | Literature-standard form    | Weaker form exists? | Reason it can/can't be weakened   |
|---|---------------------------------------|----------------------------|------------------------------|---------------------|------------------------------------|
| 1 | `[Fact p.Prime]`                      | `p` prime                  | `p` prime                    | NO                  | Teichmüller / `(p−1)`-th roots require `p` prime; intrinsic. |
| 2 | `hgen` (topological generator)        | `u` generates `ℤ_p^×` at every level | RJW uses a fixed generator `u` | NO (needed)        | The proof needs `orderOf ω(u) = p−1` (primitive root) — this comes from `u` generating. Cannot drop. |
| 3 | `0 < i < p − 1`                       | strict interior            | `i ∉ (p−1)ℤ`, i.e. `i mod (p−1) ≠ 0` | marginal           | The statement is false at `i ≡ 0 (mod p−1)` (then `ω(u)^i = 1`). The range `0<i<p−1` is one period; the truly general form is "`(p−1) ∤ i`". Minor; see 4c row 7. |
| 4 | `s : ℤ_[p]`                           | arbitrary `s`              | classical states `s = 1` only | already MORE general | This Lean form is **stronger** than RJW (all `s`, not just `s=1`); good. |
| 5 | output ring `ℚ_[p]`                   | coercion to `ℚ_p`          | `ℤ_p`/`ℚ_p`                  | n/a                 | The `ℚ_p`-coercion is a convenience for the consumer; the `ℤ_p` form `hVsub` is proved en route. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (within the project's irreducibly-`ℤ_p` setting — it is already stated for all `s`, strengthening the source; the only candidate weakening, `0<i<p−1` → `(p−1)∤i`, is a one-period vs. all-residues cosmetic choice, not a literature-mandated generalisation).
Number of weakening opportunities found: 0 substantive (1 cosmetic, row 3).
Proposed restatement: none required.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                                                 | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|------------------------------------------------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                                                       | no       | — | `hgen` is a genuine property of a chosen `u`, not a structure; no typeclass to extract. |
|  2 | sequences/metric → filters/topology?                                                                                                     | no       | — | The proof is an exact norm computation, not a limit; no sequence to filter-ise. |
|  3 | construct an object → universal-property class?                                                                                          | no       | — | This is a non-vanishing proposition, not a construction. |
|  4 | set-with-closure-predicate → bundled substructure?                                                                                       | no       | — | No substructure involved. |
|  5 | vector-space/metric/field-specific → weaken typeclass hierarchy?                                                                          | no       | — | The *engine* is already maximally general in mathlib (`IsUltrametricDist`); the *statement* cannot leave `ℤ_p` because `branchChar`/`teichmuller` live there. |
|  6 | 1-categorical → higher-categorical?                                                                                                      | no       | — | Not categorical. |
|  7 | concrete index `ℕ/ℤ/ℝ` → arbitrary additive group/monoid?                                                                                | partial  | restate `0<i<p−1` as `(i : ZMod (p−1)) ≠ 0` | minor: would unify with `branchChar_natCast`'s `ZMod (p−1)` indexing; not a real organisational win and not a mathlib concern |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (the one partial, row 7, is a cosmetic re-indexing internal to the project, with no mathlib-downstream payoff). This is a finite p-adic norm computation about project-specific characters; there is no contemporary mathlib reformulation that improves its organisation.

---

### Diamond / defeq risk — Phase 4.5

**n/a — declaration kind is `theorem`.** Theorems introduce no definitional equalities or typeclass-search paths. Skipped.

---

### Mathlib search-status: `PadicLFunctions.branch_denom_ne_zero`

[A] Lean-Finder       (tool not reachable in this CLI environment)        n/a: Lean-Finder is a web Space; no MCP binding here. Compensated by [B]–[E] + the Phase-3 web sweep.
[B] Loogle            shape `... → branchChar _ _ _ _ - 1 ≠ 0`; `‖_ ^ _ - 1‖ = 1` over `ℤ_[p]`; ultrametric `norm_mul ... = max`    no hits for the packaged statement; the *engine* hit is `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm` (used in the proof)
[C] LeanSearch        "branch character p-adic L-function denominator nonzero"; "Teichmüller power minus one norm one"            no hits (mathlib has no p-adic L-function / Teichmüller layer)
[D] Grep mathlib src  `grep -rn "Kubota\|Leopoldt\|p-adic L-function\|teichmuller" .lake/packages/mathlib/Mathlib/`               **zero hits** — mathlib contains NO p-adic L-function machinery, NO Kubota–Leopoldt, NO Teichmüller character, NO branch decomposition. `PadicInt.teichmuller`, `angleUnit`, `onePAdicPow`, `branchChar` are ALL defined in `projects/PadicLFunctions/.../Interpolation/Branches.lean`, not mathlib.
[E] Name pattern      `branch`, `teichmuller`, `angleUnit`, `denom`, `_ne_zero` in mathlib                                        no hits for these specific objects; the only mathlib match is the ultrametric isoceles family in `Mathlib/Analysis/Normed/Group/Ultra.lean`

Searched for both:
  - the user's current form (the packaged `branchChar ... − 1 ≠ 0`) — not in mathlib;
  - the literature-standard ingredients — the ultrametric isoceles lemma **IS** in mathlib (`IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`, `Mathlib/Analysis/Normed/Group/Ultra.lean:96`, additive sibling of `norm_mul_eq_max_of_norm_ne_norm`), and the proof already uses it; the *p-adic L-function context* is entirely absent from mathlib.

Concluded: **not in mathlib** (all available methods exhausted, plus the literature-standard ingredients). The packaged statement does not exist; the only reusable piece (ultrametric isoceles) is already correctly imported and used inside the proof.

---

### Call sites — `PadicLFunctions.branch_denom_ne_zero`

Internal use count: **1** (within the project, not counting the declaring line `ResidueZeta.lean:188`)
External-to-file callers: **0 distinct files** (the single use is in the *same* file).

| Caller file:line               | Usage pattern (one-line excerpt)                          |
|--------------------------------|-----------------------------------------------------------|
| ResidueZeta.lean:422           | `branch_denom_ne_zero p hgen hi0 hi (1 - 1)` — feeds `hden_ne`, the "denominator nonzero at `s=1`" hypothesis inside the continuity proof of the non-pole branches (`i ≠ p−1`). |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `branch_denom_ne_zero`?):
  - (none) — `tendsto_branch_denom_div` (line 231, the `i = p−1` pole branch) does *not* re-derive non-vanishing; there the denominator *does* vanish at `s=1`, so the lemma correctly is not used there. No competing inline derivation exists.

What the pattern tells you: **K = 1 internal use, in the same file, no external callers, no inline re-derivation.** Per the call-sites table this leans toward "possibly the wrong abstraction / could be inlined" — but the abstraction is reasonable here because the lemma is *generalised over `s`* (the consumer only needs `s = 1−1 = 0`, yet the lemma is stated for all `s`) precisely to record the RJW strengthening; the `s`-uniformity is the mathematical point, not over-engineering. Within the project this is a legitimate intermediate result; for *mathlib*, K = 1 and zero external reach reinforce that it is project-internal scaffolding.

---

### Composition check (Phase 6)

Can `branch_denom_ne_zero` be derived from **mathlib** in ≤3 chained calls? (The relevant question is mathlib-composability, since the project's own `branchChar` etc. are not mathlib.)

Attempt 1: `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm _ ▸ ...`
  - Mathlib decls used: `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`, `norm_mul`, `PadicInt.norm_lt_one_iff_dvd`, `PadicInt.coe_eq_zero`.
  - Result: **fails as a ≤3-call composition.**
  - Notes: To even *state* the goal you need `branchChar`, `teichmuller`, `angleUnit`, `onePAdicPow` — none in mathlib. The proof additionally needs the project lemma `norm_teichmuller_pow_sub_one_eq_one` (itself resting on `teichmuller_isPrimitiveRoot`, i.e. that `ω(u)` is a primitive `(p−1)`-th root, requiring the generator hypothesis), `onePAdicPow_sub_one_mem`, `branchChar_apply`, plus a `ℤ_p → ℚ_p` descent. That is a genuine multi-`have` proof with non-trivial reasoning between steps (the heuristics table classifies "multiple `have`s with non-trivial reasoning" as **NO — this is a proof**).

Attempt 2: not applicable — there is no second angle; the statement is irreducibly about project-defined objects mathlib does not have.

Conclusion: **NOT-COMPOSABLE** from mathlib. (It *is* a short composition of *project* lemmas, but those project lemmas are themselves not in mathlib — so for the mathlib question the whole tower is absent.)

---

## Verdict: `PadicLFunctions.branch_denom_ne_zero`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the *surrounding objects* (branch decomposition `ζ_{p,i}=∫ω^i⟨x⟩^{1−s}`, Teichmüller split, pole/residue at `s=1`) and the *engine* (ultrametric isoceles) are standard; but **no source packages this as a named standalone lemma** — it is RJW Lemma 7.2(i), an internal step, here strengthened to all `s`.
- Generality analysis (Phase 4): MAXIMALLY GENERAL within the irreducibly-`ℤ_p` setting (already stated for all `s`, strengthening the source); no modern-idiom reformulation applies (Phase 4c all `no`/cosmetic).
- Mathlib search (Phase 5): **not in mathlib**, and crucially **mathlib has no p-adic L-function layer at all** — `branchChar`/`teichmuller`/`angleUnit`/`onePAdicPow` are all project-defined; only the ultrametric isoceles lemma it uses is mathlib.
- Composition check (Phase 6): NOT-COMPOSABLE from mathlib (it is a multi-step proof over objects mathlib lacks). Call sites: K = 1, same-file, no external reach.

**Rationale (1–2 paragraphs):**

This is not a "should mathlib have *this lemma*?" so much as "should mathlib have the *whole p-adic-L-function development* this lemma lives in?" — and that is the human judgment call. The statement is mathematically correct, faithfully formalises RJW Lemma 7.2(i) (in fact strengthens it from `s = 1` to all `s ∈ ℤ_p`), and is stated at the right generality for its purpose. But it is *irreducibly about project-specific objects* — `branchChar` (`x ↦ ω(x)^i⟨x⟩^s`), `teichmuller`, `angleUnit`, `onePAdicPow` — **none of which exist in mathlib**. A Phase-5 grep of all of mathlib for `Kubota`/`Leopoldt`/`p-adic L-function`/`teichmuller` returns zero. So the lemma cannot be a standalone mathlib contribution: it would have to ride in as part of a much larger upstreaming of the Teichmüller-character + branch-decomposition + p-adic-zeta machinery. Whether *that* whole tower belongs in mathlib (and in what canonical form — RJW's? Washington's? a Kubota–Leopoldt-first reorganisation?) is a strategic decision about a research-frontier development that the skill cannot ground in the evidence alone.

Two further signals push to BORDERLINE rather than a clean YES or NO. (a) It is **not NO-mathlib-has-it** (mathlib has nothing close) and **not NO-composable** (the proof is a genuine multi-`have` argument, not a ≤3-call mathlib composition); the only mathlib piece, `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`, is already correctly reused inside the proof and should *stay* reused. (b) But it is also **not cleanly YES-add-as-is**: the call-sites grep shows K = 1, same-file, no external consumers, and the literature treats this as an *internal step* of an L-function construction, never as a named theorem — so shipping just this leaf, divorced from the development, would be an oddly-specific orphan in mathlib. The right grain for a mathlib PR is the *family* (`branchChar` + its API: `branchChar_apply`, `branchChar_natCast`, `norm_onePAdicPow_sub_one`, the continuity and the non-vanishing), once the project's Teichmüller layer is itself proposed for upstreaming — and the project's own docstrings frame all of this as following RJW/Washington, i.e. as in-progress formalisation rather than settled mathlib API.

**Numbered questions for the user (≤5):**

1. **Is the whole p-adic-L-function development (Teichmüller character `teichmuller`, the `ω(x)·⟨x⟩` decomposition, `onePAdicPow`, `branchChar`, the Kubota–Leopoldt branches) intended for eventual mathlib upstreaming?** If *no* (it stays a project library), then `branch_denom_ne_zero` is project-internal scaffolding and drops out of mathlib consideration entirely. If *yes*, it ships **as part of that family**, not alone.
2. If yes to (1): **should the upstreamed Teichmüller layer follow the project's current RJW-flavoured API, or be reorganised** (e.g. `teichmuller` as a bundled `MonoidHom`/`DirichletCharacter` with the `ℤ_p^× ≃ μ_{p-1} × (1+pℤ_p)` equivalence as the headline object) before the non-vanishing lemmas are stated against it? This determines the canonical statement of `branch_denom_ne_zero`.
3. The lemma is **stated for all `s ∈ ℤ_p`** but its only consumer (line 422) uses `s = 0`. Is the `s`-uniform strengthening (RJW `s=1` → all `s`) something you want to **preserve as the mathlib form**, or would the consumer-driven `s`-specific form be the better API there?
4. Is the **generator hypothesis `hgen`** (`u` topologically generates `ℤ_p^×`) the form you want in mathlib, or would you prefer it phrased via an existing/added mathlib abstraction for "topological generator of `ℤ_p^×`" (none exists today) before this lemma is upstreamed?

**Next action:** the user answers the questions above; then re-run `/mathlibable PadicLFunctions.branch_denom_ne_zero` to resolve. Likely outcomes:
  - **(1) = no** → drop from mathlib consideration; keep as project-internal, no rename needed (it already lives behind `branchChar`).
  - **(1) = yes** → re-aim the assessment at the *family* PR: the verdict on the leaf becomes `YES-add-as-is` *bundled with* `branchChar` + its API + the Teichmüller layer (run `/cleanup` on `Interpolation/Branches.lean` + `ResidueZeta.lean` first, group the branch-character lemmas into one mathlib PR, after the Teichmüller `def` layer lands).

---

## Next step

The user answers the four numbered questions (most decisive: **is the project's Teichmüller / branch-character layer headed for mathlib at all, and in what canonical form?**). On `(1) = no`, drop from mathlib scope. On `(1) = yes`, re-run with the answers and treat `branch_denom_ne_zero` as part of a `branchChar`-family PR rather than a standalone contribution.
