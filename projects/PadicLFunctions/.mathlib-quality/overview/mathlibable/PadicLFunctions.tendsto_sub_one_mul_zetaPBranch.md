# `/mathlibable` report — `PadicLFunctions.tendsto_sub_one_mul_zetaPBranch`

Mode A (single declaration), full 10-phase workflow with the exhaustive 9-channel
literature search. ChatGPT MCP was unavailable in this environment (a `chatgpt-math`
server dir exists under `~/.claude/mcp-servers/` but no ChatGPT tool is exposed and
`codex` is not on PATH — recorded `n/a`); all other channels ran.

---

## Final verdict: `BORDERLINE-needs-human`

The theorem is **RJW Theorem 7.1(ii)** — the canonical, literature-named statement that
the Kubota–Leopoldt p-adic zeta branch `ζ_{p,p−1}` has a **simple pole at `s = 1` with
residue `1 − p⁻¹`**. It is true, proved sorry-free, genuinely missing from mathlib4, and
NOT composable from mathlib (so it is **not a NO**). Of the four `ResidueZeta.lean` results
assessed so far it is the **strongest YES candidate** — the residue value is universally
cited and this is the headline theorem the other three (`tendsto_branch_denom_div`,
`zetaNum_one`, `continuousAt_zetaPBranch`) feed into. But a clean YES is blocked by a single
human judgment: the theorem sits atop an entire p-adic-L-function tower
(`PadicMeasure.padicZeta` pseudo-measure, `zetaNum`, `branchChar`/`zetaPBranch`, `extLog` /
`padicLog` / `padicExp`, `exists_nat_topological_generator`, `onePAdicPow`, the units
Teichmüller character) that is **absent from mathlib4 in its entirety**. It cannot be PR'd
standalone; whether to upstream that tower (and in what order / shape) is a maintainer
decision the skill cannot make. This is the same gating question that governs its three
siblings, and they should travel together.

---

### Baseline (Phase 0)

- lake build:               **build NOT re-run** (stale/slow per task note) — reasoned from source; decl + all transitive dependencies read directly from `.lean`. Phase 0 fallback used.
- decl `PadicLFunctions.tendsto_sub_one_mul_zetaPBranch`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ResidueZeta.lean:1773`
- kind:                      theorem
- has sorry:                 **no** (body lines 1773–1836 contain no `sorry`/`admit`; the supporting lemmas it calls — `tendsto_branch_denom_div`, `continuous_zetaNum_branch_pairing`, `zetaNum_one`, `extLog_natCast_eq_pZpLog_angle`, `pZpLog_angleUnit_ne_zero` — are all sorry-free per the worklist + sibling reports)
- module docstring summary:  "The residue of ζ_p at s = 1 (RJW §7, TeX 2181–2360)" — proves **RJW Theorem 7.1**: (i) branch `ζ_{p,i}` continuous at `s=1` for `i≠p−1`; **(ii) `ζ_{p,p−1}` has a simple pole at `s=1` with residue `1 − p⁻¹`**. This theorem is part (ii) — the final, headline result of the file (last theorem before `end`).

---

### Statement (Phase 1)

`PadicLFunctions.tendsto_sub_one_mul_zetaPBranch` is a **theorem** stating the following.

> Let `p` be an odd prime. The exceptional branch `ζ_{p,p−1}` of the Kubota–Leopoldt
> p-adic zeta function has a **simple pole at `s = 1` with residue `1 − p⁻¹`**, expressed
> as the punctured topological limit
> `lim_{s → 1, s ≠ 1} (s − 1)·ζ_{p,p−1}(s) = 1 − p⁻¹`
> (the function of `s ∈ ℤ_p`, valued in `ℚ_p`).

This is the p-adic mirror of the classical fact that the Riemann zeta function `ζ(s)` has a
simple pole at `s = 1` with residue `1`. In the standard analytic-number-theory picture the
Kubota–Leopoldt p-adic zeta is *not* globally analytic but is assembled from `p − 1` analytic
functions `ζ_{p,1}, …, ζ_{p,p−1}` (one per residue class mod `p − 1`); all are analytic at
`s = 1` **except** `ζ_{p,p−1}`, whose simple pole — with residue `1 − p⁻¹` — is exactly the
behaviour of `ζ_p` at the trivial character. This theorem captures precisely that exceptional,
poled branch. It is RJW (the project's source = Rodrigues-Jacinto / C. Williams,
*An introduction to p-adic L-functions*) **Theorem 7.1(ii)** (`thm:residue`, TeX 2191–2192).

Variables / typeclasses involved (Lean side):
- `(p : ℕ) [hp : Fact p.Prime]` — the prime (section variable).
- `(hp2 : p ≠ 2)` — oddness; the topological-generator construction, the exp/log bridge
  (`pZpExp`/`pZpLog` are odd-`p` objects), and the sharp Teichmüller-norm step all genuinely
  need `p` odd, matching the literature's standing `p > 2` hypothesis for this development.

Hypotheses (Lean side): only `hp2 : p ≠ 2` (the branch index is fixed to the exceptional
`i = p − 1`; the punctured-neighbourhood condition `s ≠ 1` is in the filter).

Conclusion (math): `lim_{s→1, s≠1} (s−1)·ζ_{p,p−1}(s) = 1 − p⁻¹` — i.e. simple pole, residue `1 − p⁻¹`.

Conclusion (Lean):
```lean
Filter.Tendsto
  (fun s : ℤ_[p] => ((s : ℚ_[p]) - 1) * zetaPBranch p hp2 (p - 1) s)
  (nhdsWithin 1 {s | s ≠ 1})
  (nhds (1 - (p : ℚ_[p])⁻¹))
```
where (`Branches.lean:557`)
`zetaPBranch p hp2 i s = (⟨branchChar p i (1−s) u⟩_{ℚ_p} − 1)⁻¹ · ⟨zetaNum p m (branchChar p i (1−s))⟩_{ℚ_p}`
is RJW's "Eqtmp2" quotient: a denominator `⟨u⟩^{1−s}ω^i − 1` and a numerator pseudo-measure
pairing `zetaNum` against the branch character, evaluated at the canonical integer topological
generator `u` (index `m`) from `exists_nat_topological_generator`. The proof (lines 1778–1836)
assembles the residue from: denominator limit `(s−1)⁻¹·denom → −L` (`tendsto_branch_denom_div`,
with `L = log_p⟨u⟩ ≠ 0`), its inverse, the continuous numerator limit
(`continuous_zetaNum_branch_pairing`), the numerator value at `s=1`
(`zetaNum_one`: `num 1 = −(1−p⁻¹)·log_p(m)`), and the identification `log_p(m) = L`
(`extLog_natCast_eq_pZpLog_angle`), giving `(−L)⁻¹·num 1 = 1 − p⁻¹`.

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: it is (a) the **main result** of the `ResidueZeta` module — the file's module
docstring leads with "RJW Theorem 7.1" and this is its headline part (ii); it is the *last*
theorem in the file and every other worklist entry for the file is one of its supporting
lemmas; and (b) effectively a **named theorem** (the canonical "simple pole of the p-adic
zeta at `s=1`, residue `1 − p⁻¹`", RJW Thm 7.1(ii) / Washington), which is "basically
guaranteed to be in or near the literature". Both BIG triggers fire.

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Body line count: ~58 substantive lines (1778–1836: `classical`, the generator `obtain`/`set`s,
six numbered `have` steps assembling denominator/numerator limits and the residue value, then
the `Tendsto.mul` + `congr` + `ring` finish).
One-liner verdict: **n/a — kind is `theorem`, not a `def`.** Section skipped.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "Kubota-Leopoldt p-adic zeta function simple pole s=1 residue 1 − 1/p"                                  | **yes** | "`ζ_{p,p−1}` has a simple pole at `s=1` with residue `(1−p⁻¹)`" — **verbatim match to the theorem** | confirmed across RJW (arXiv 2309.15692), the Waikato/ResearchGate KL-zeroes papers, Grubb 205 notes; the analogy to `ζ(s)`'s residue `1` at `s=1` is universal |
|  2 | WebSearch (general / IMC form)   | "p-adic L-function residue at s=1 equals (1 − p⁻¹) Iwasawa main conjecture analytic"                    | yes  | the (untwisted) p-adic zeta has a simple pole at `s=1`; KL function = analytic side of the Mazur–Wiles main conjecture | Wikipedia "p-adic L-function"; Liu (IAS); UCSB Castella/Plater notes; the **ENT/MSP published** RJW (msp.org/ent/2025/4-1) |
|  3 | WebSearch (named-after / aliases / branches) | "p-adic zeta `p−1` analytic functions branches residue class mod p−1 not analytic pole trivial character Washington cyclotomic" | **yes** | **verbatim:** "the function `n ↦ ζ_p(n)` … comes from `p−1` analytic functions, one for each residue class mod `p−1`" and "**If `i ≠ p−1`, then `ζ_{p,i}` is analytic at `s=1`. The function `ζ_{p,p−1}` has a simple pole at `s=1` with residue `(1−p⁻¹)`.**" | C. Williams Warwick notes; RJW; Koblitz; Venkatesh 263C — the `p−1`-branch split with the poled exceptional branch is the canonical statement; **this is the exact RJW Thm 7.1(i)+(ii) split** |
|  4 | ChatGPT MCP                      | (intended: "standard form + generality + historical evolution of the p-adic-zeta residue at `s=1`")    | **n/a** | —                                | ChatGPT MCP not configured (`~/.claude/mcp-servers/chatgpt-math` dir present but no exposed tool; `which codex` → not found). Recorded n/a per protocol; compensated by 6 WebSearch queries across 3 generality levels + 2 WebFetch + the project's named RJW source. (Same situation recorded in the three sibling reports.) |
|  5 | Local references                 | `ls projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/`                   | **n/a** | (neither dir exists)             | both absent in this checkout — recorded n/a. The module docstring's inline citations (RJW §7, `thm:residue` TeX 2187–2194, Thm 7.1(ii) TeX 2191–2192) serve as the local literature anchor. |
|  6 | nLab                             | WebFetch `ncatlab.org/nlab/show/p-adic+L-function`; WebSearch "nLab p-adic L-function … pole residue"   | **n/a** | HTTP 404 — no such nLab page     | nLab has no dedicated p-adic-L-function / residue page (404). The residue/pole fact is analytic-NT folklore, not a categorical headline; not a categorical concept. |
|  7 | nCatLab (if categorical)         | —                                                                                                       | n/a  | —                                | n/a — not a categorical concept; it is a pointwise analytic limit (`Tendsto`) over `ℤ_p`. |
|  8 | Stacks Project (if alg geom)     | —                                                                                                       | n/a  | —                                | n/a — not an algebraic-geometry / scheme-theoretic concept. |
|  9 | MathOverflow / Math.StackExchange| folded into #1–#3; "p-adic zeta residue at `s=1` = `1 − 1/p`"; analytic-vs-pole branch split             | yes  | same residue `1 − p⁻¹`; same `p−1`-branch picture; the pole "at the trivial character" framing | community treats the residue `1 − p⁻¹` as the standard value (the `(1−p^{1−s})`-normalised analogue of `ζ`'s residue 1) |
| 10 | recent arXiv (last 5 years)      | "Mazur's construction Kubota–Leopoldt"; "Sum expressions for KL" (2201.08870); Lean-3 formalization (2302.14491) | yes  | residue `1 − p⁻¹` recurs unchanged in modern work; pseudo-measure `ζp` on `ℤ_p^×` with `∫xᵏ·ζp = (1−pᵏ⁻¹)ζ(1−k)` (Guitart, Mazur–Coleman) — **matches the project's `padicZeta`/`zetaNum` construction**; **Narayanan (arXiv 2302.14491) formalised KL in Lean 3 / mathlib3, NOT ported to mathlib4** | confirms (a) no modern reformulation supersedes the classical residue/pole statement, and (b) the p-adic-L machinery is still absent from mathlib4 |

The protocol passes:
- **WebSearch ran 6 distinct queries** (≥3 required) at three generality levels: specific
  residue form (#1), general/Iwasawa-main-conjecture (#2), and named-aliases/branch-decomposition
  (#3), plus #10 (formalization-status + construction) and two WebFetch verifications.
- **ChatGPT MCP: n/a with reason** (not configured) — compensated by extra WebSearch breadth + the project's named RJW source.
- **Local references: checked**, n/a (dir absent).
- **nLab: checked** (404 — no page).
- **Stacks / nCatLab / MathOverflow / arXiv: each checked or n/a with reason.**

(WebFetch of the source PDFs — RJW arXiv 2309.15692, the Warwick C. Williams notes, the
Guitart/LTCC notes, Wikipedia — returned binary/partial content and could not be parsed for
verbatim *theorem-number* text; the exact statement was nonetheless captured verbatim from the
WebSearch snippets of those same documents, which quote it word-for-word.)

### Literature summary (Phase 3)

Concept identified as: **the simple pole of the Kubota–Leopoldt p-adic zeta function at
`s = 1`, with residue `1 − p⁻¹`** — equivalently, the pole of the exceptional branch
`ζ_{p,p−1}(s)` at `s = 1`, the p-adic analogue of `ζ(s)`'s simple pole (residue `1`) at `s = 1`.

Sources agree on the standard form: **yes — strongly.** Every standard source (Washington's
*Introduction to Cyclotomic Fields*; RJW = Rodrigues-Jacinto/Williams, arXiv 2309.15692 and its
ENT/MSP 2025 publication; the Warwick C. Williams lecture notes; Koblitz; Venkatesh) gives the
*identical* picture and, in several cases, the *identical sentence*:
> "If `i ≠ p−1`, then `ζ_{p,i}` is analytic at `s=1`. The function `ζ_{p,p−1}` has a simple
> pole at `s=1` with residue `(1−p⁻¹)`."
This is a **verbatim match** to the theorem's content (and to RJW Thm 7.1(i)+(ii), of which this
is part (ii)). The pseudo-measure construction (`∃! ζ_p` on `ℤ_p^×` with `∫xᵏ·ζ_p = (1−pᵏ⁻¹)ζ(1−k)`)
that the project realises via `padicZeta`/`zetaNum`/`PadicMeasure` is likewise the canonical
Mazur–Coleman route.

Most general standard form: the *statement is already the standard form* — the residue of the
exceptional branch at `s = 1` is `1 − p⁻¹` exactly. The only "more general" objects are (a) the
**twisted** version (p-adic Dirichlet `L`-functions `L_p(s,χ)`, where the pole/non-pole dichotomy
is governed by whether `χ` is trivial) and (b) the same statement over an extension field / for
general number fields — neither is a *weakening* of this `ℚ`-over-`ℚ_p` residue statement; they
are different (broader) theorems.

Generality dimensions where the literature varies:
- **Twist**: untwisted `ζ_p` (this theorem) → `L_p(s,χ)` for a Dirichlet character `χ` (the pole
  sits at the trivial character; this is the `χ = 1` case). A genuinely broader theorem, not a
  reparametrisation of this one.
- **Normalisation of the residue**: `1 − p⁻¹` here (the `(1−p^{1−s})ζ` Euler-factor normalisation);
  some sources state the residue as `1` for a differently-normalised object. The project's
  `1 − p⁻¹` matches RJW exactly.
- **Regularity spelling**: "simple pole, residue `r`" (classical) ↔ "`lim_{s→1,s≠1}(s−1)f(s) = r`"
  (the Lean `Tendsto` form — the modern filter spelling of "simple pole with residue `r`").

Disagreement with the literature: **none on content.** The Lean statement is a faithful,
maximally-faithful rendering of the standard theorem. The only nuance is the spelling: the
literature says "simple pole with residue `1 − p⁻¹`"; the Lean form gives the punctured-limit
*characterisation* `lim_{s→1,s≠1}(s−1)·ζ_{p,p−1}(s) = 1 − p⁻¹`, which is the correct (and
modern) way to state a simple pole + residue when the ambient analytic framework (meromorphic
functions, residues) is not yet available for this object (it is not, in mathlib — see Phase 5).

---

### Generality analysis — `PadicLFunctions.tendsto_sub_one_mul_zetaPBranch`

Literature-standard form (from Phase 3): `ζ_{p,p−1}` has a **simple pole at `s = 1` with residue
`1 − p⁻¹`** — i.e. exactly the punctured-limit the theorem states. This is already the standard
form; there is no *weaker* literature form to match.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | conclusion `Tendsto … (nhds (1 − p⁻¹))` | punctured limit `lim_{s→1,s≠1}(s−1)·ζ_{p,p−1}(s) = 1 − p⁻¹` | "simple pole at `s=1`, residue `1 − p⁻¹`" | **NO — this *is* the standard form** | The `Tendsto` characterisation is the maximally-faithful spelling of the literature statement; it cannot be "weakened" without losing the residue value. It could be *re-packaged* into a `MeromorphicAt` + `residue = 1 − p⁻¹` statement once that API applies to this object — see Phase 4c — but that is a strengthening/repackaging, not a weakening, and the API does not exist for `ζ_{p,p−1}`. |
| 2 | `(hp2 : p ≠ 2)` | odd prime | odd prime (standard standing hypothesis) | **NO** | Matches the literature's `p > 2` convention for this development. The `p = 2` case has a structurally different unit group `1 + 4ℤ_2`; the project's `pZpLog`/`pZpExp` and integer topological generator are odd-`p` objects. Correct as-is. |
| 3 | branch index fixed to `p − 1` | the exceptional branch | the exceptional branch `i = p−1` | **NO** | `i = p−1` is the genuine mathematical locus of the pole (RJW Thm 7.1: the *other* branches `i ≠ p−1` are analytic at `s=1`, handled by the sibling `continuousAt_zetaPBranch`). Fixing `i = p−1` is correct, not a needless specialisation. |
| 4 | target field `ℚ_p` / variable `ℤ_p` | `ζ_{p,p−1} : ℤ_p → ℚ_p` | could be stated for `L_p(s,χ)` (twisted) or over an extension | yes — but these are *different/broader theorems*, not weakenings of this one | Widening to twisted `L_p(s,χ)` is a genuinely different (more general) result whose `χ=1` specialisation is this theorem; it is not a "weaken a hypothesis" move. The values are genuinely in `ℚ_p`. |

This is a literature-grounded pass: the target form comes from the Washington / RJW / C. Williams
standard statement, which gives the residue `1 − p⁻¹` *exactly*.

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (for the untwisted p-adic zeta — it *is* the
literature-standard statement; the `Tendsto`-limit spelling is the faithful, correct rendering of
"simple pole, residue `1 − p⁻¹`").
Number of weakening opportunities found: **0.** (The only "more general" directions — twisting to
`L_p(s,χ)`, or extension fields / number fields — are broader theorems, not weakenings of this
statement; per the verdict gate, "would be nice to also have the twisted version" is not a reason
to call this STRICTLY NARROWER.)
Proposed restatement (if STRICTLY NARROWER): **n/a** — it is maximally general.
Cost: n/a.

→ MAXIMALLY GENERAL ⇒ Phase 7 considers `YES-add-as-is` or the NO buckets, then also runs 4c.

### Modern-idiom check (Phase 4c) — the Bourbaki-2.0 question

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances? | **no** | — | Hypotheses are already minimal & typeclass-driven (`Fact p.Prime`, `p ≠ 2`); no bundled "let" preamble. |
|  2 | sequences/metric → filters/nets/topological? | **already done** | — | The statement is *already* a filter `Tendsto` with `nhdsWithin 1 {s ≠ 1}` — the idiomatic modern spelling of a punctured limit. No improvement available; this is the target form. |
|  3 | construct an object → universal-property class? | no | — | This is a limit statement about a given function, not a construction. |
|  4 | set-with-closure-predicate → bundled substructure? | no | — | No substructure here. |
|  5 | vector-space/metric/field-specific → weaken typeclass? | no | — | `ℤ_p`, `ℚ_p` are the genuine objects; intrinsically about these specific rings. |
|  6 | 1-categorical → higher-categorical? | no | — | n/a. |
|  7 | concrete index (ℕ,ℤ,ℝ) → arbitrary group/monoid? | no | — | `i = p−1` is the residue index of the *exceptional* branch; not spurious concreteness. |
|  8 | **`Tendsto (s−1)·f → r` → `MeromorphicAt f 1` with `residue f 1 = r` (the genuine modern-idiom lever)** | **YES (in principle)** | restate as: `ζ_{p,p−1}` is `MeromorphicAt 1` with a simple pole and `AnalyticAt`-residue `1 − p⁻¹`, with this `Tendsto` as the unfolded consequence | a `MeromorphicAt` + residue statement composes with mathlib's meromorphy/residue API (which exists archimedean: `Mathlib/Analysis/.../Meromorphic`, `Residue.lean`) — turning a one-off limit into a structured pole/residue fact. **BUT**: that API is built on `ℂ`-analytic / normed-field analytic infrastructure that does **not** apply to the p-adic `ζ_{p,p−1}` (there is no p-adic-analytic theory for `onePAdicPow`/`zetaPBranch` in mathlib, see Phase 5). So the modern idiom is *aspirational*, not currently realisable for this object. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes in principle, but not realisable today** — and it lives one layer
down (a p-adic meromorphy/residue theory), not in this signature. The genuine Bourbaki-2.0 target
would be `MeromorphicAt (zetaPBranch p hp2 (p−1)) 1` with `residue = 1 − p⁻¹` (composing with
mathlib's residue API), but mathlib has **no p-adic-analytic / p-adic-meromorphic framework** for
this object (Phase 5: no p-adic log/exp, no analytic theory on `addChar_of_value_at_one`), so the
`MeromorphicAt` form cannot be stated. The `Tendsto`-limit form the theorem uses is therefore the
*correct and idiomatic* spelling for a simple-pole-with-residue statement **in the absence of** that
framework — and it is already in the modern filter idiom (`nhdsWithin`/`Tendsto`). No "looks cooler
in category theory" trap is invoked: the `MeromorphicAt` repackaging is a real improvement *once the
underlying p-adic-analytic theory exists*, which is itself a (large) definitional development mathlib
lacks — i.e. it points at the same upstreaming programme, not at a restatement applicable to this
theorem in isolation.

---

### Diamond / defeq risk — `PadicLFunctions.tendsto_sub_one_mul_zetaPBranch`

**n/a — declaration kind is `theorem`.** Theorems introduce no definitional equalities or
typeclass-search paths; Phase 4.5 is skipped. (Risk verdict: n/a.)

---

### Mathlib search-status: `PadicLFunctions.tendsto_sub_one_mul_zetaPBranch`

Searched both the user's current form (the residue/pole `Tendsto`) AND the literature-standard
form (the simple pole of the KL p-adic zeta at `s=1`, residue `1 − p⁻¹`, and the underlying
*object* `ζ_{p,p−1}` / `padicZeta`), AND the modern-idiom form (`MeromorphicAt` + residue).

[A] **Lean-Finder** — "p-adic zeta function residue at s=1", "Kubota Leopoldt simple pole", "p-adic L-function pole 1 - 1/p" — **n/a: web UI/API not callable in this environment.** Substituted by the WebSearch "Lean/mathlib4 formalization" channel (#10), which establishes the mathlib4 gap directly (only a Lean 3 formalization, Narayanan arXiv 2302.14491, exists — unported).

[B] **Loogle** (substitute: grep for the type shape over the mathlib tree) — `Tendsto (fun s => (s - 1) * _) (nhdsWithin 1 _) (nhds _)`, any `Tendsto`/`residue`/`MeromorphicAt` attached to a p-adic zeta / `addChar_of_value_at_one` — **no hits.** The only p-adic power-map primitive in mathlib (`PadicInt.addChar_of_value_at_one`, `Mathlib/NumberTheory/Padics/AddChar.lean`) carries **only** construction + continuity + bijection API (`AddChar.tendsto_eval_one_sub_pow`, `continuous_addChar_of_value_at_one`, `coe_addChar_of_value_at_one`, `eq_addChar_of_value_at_one`, `continuousAddCharEquiv`) — **no residue, no pole, no difference-quotient `Tendsto`, no `MeromorphicAt`.**

[C] **LeanSearch** — "residue of p-adic zeta function at s=1", "Kubota-Leopoldt pole residue 1 - 1/p", "p-adic L-function simple pole" — **n/a: tool not callable.** Substituted by [D]/[E] + WebSearch; no mathlib4 equivalent surfaced (only the Lean 3 work).

[D] **Grep mathlib src** — `grep -rln -i "kubota|leopoldt|p-adic L-function|padicLFunction|p-adic zeta|padicZeta"` over `.lake/packages/mathlib/Mathlib/` → **0 hits.** `padicLog|padicExp` (excl. `padicVal`) → **0 hits** (mathlib has no p-adic logarithm/exponential at all). `iwasawa` → only `GroupTheory/GroupAction/Iwasawa.lean` (Iwasawa's lemma on group actions — unrelated). `teichmuller` → only Witt-vector / perfectoid (`RingTheory/Teichmuller.lean`, `WittVector/Teichmuller.lean`, `Perfectoid/…`), **not** the p-adic-units Teichmüller character used here. The archimedean `riemannZeta` residue machinery exists (`NumberTheory/LSeries/RiemannZeta.lean` etc.) but is `ℂ`-analytic and cannot be specialised to a p-adic statement.

[E] **Name pattern** — `grep` for `zetaPBranch`, `branchChar`, `zetaNum`, `padicZeta`, `onePAdicPow`, `pZpLog`, `extLog`, `ExtLogDomain`, `exists_nat_topological_generator`, `PadicMeasure` across the mathlib tree → **all project-local; none exist in mathlib4.** (`def zetaNum` at `KubotaLeopoldt/ZetaP.lean:74`; `padicZeta` is the project pseudo-measure used inside `zetaPBranch_interpolation` at `Branches.lean:587`; `extLog` at `ExtLog.lean:286`; all in the `PadicLFunctions`/`PadicMeasure` namespaces, never in `Mathlib`.)

Concluded: **not in mathlib (all five methods exhausted, plus the literature-standard form, the
modern `MeromorphicAt` form, and the underlying object).** mathlib4 has **zero** Kubota–Leopoldt /
p-adic-L-function / p-adic-zeta development. The single relevant primitive
(`PadicInt.addChar_of_value_at_one`, the Mahler-series continuous character `s ↦ y^s` on which the
project's `onePAdicPow` is built) carries **no analytic theory** — no derivative, no residue, no
pole, no meromorphy. A Lean **3** / mathlib3 formalization exists (Narayanan, arXiv 2302.14491) but
was **never ported to mathlib4**; this AINTLIB `PadicLFunctions` project is itself the fresh mathlib4
development. Consequently *every* prerequisite of this theorem — `zetaPBranch`, `branchChar`,
`zetaNum`, `padicZeta`, `extLog`/`padicLog`/`padicExp`, `onePAdicPow`,
`exists_nat_topological_generator`, the `PadicMeasure` pseudo-measure framework, the units
Teichmüller character — is missing upstream.

---

### Call sites — `PadicLFunctions.tendsto_sub_one_mul_zetaPBranch` (Phase 6.0)

Internal use count: **0** — `grep -rn "tendsto_sub_one_mul_zetaPBranch"` across the whole project
returns only the declaration itself at `ResidueZeta.lean:1773`. No other file or line references it.
External-to-file callers: **0 distinct files.**

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none)           | —             |

Inline-derivation grep (was the equivalent residue/pole statement re-derived elsewhere without
using this theorem?):
  - **(none)** — the `(s−1)·ζ_{p,p−1}(s) → 1 − p⁻¹` residue pattern appears only inside this theorem.
    It is the **terminal headline** of the file; nothing downstream consumes it (its supporting
    lemmas — `tendsto_branch_denom_div`, `continuous_zetaNum_branch_pairing`, `zetaNum_one`,
    `extLog_natCast_eq_pZpLog_angle`, `pZpLog_angleUnit_ne_zero` — all flow *into* it, not out).

**What the call-sites pattern tells us:** `K = 0` internal uses, **no** inline re-derivation. Per the
Phase-6.0.1 table this is the "**dead code? brand-new + unused so far?**" row → here unambiguously the
latter: it is a **named source result and the file's headline theorem** (RJW Thm 7.1(ii)), proved as
the *goal* of the entire `ResidueZeta` development, not as reusable plumbing. It is the kind of
top-of-the-DAG result that has no internal consumers *by construction* — it is the thing the whole
file exists to prove. This is the opposite signal from a wrapper/dead-helper: zero call sites here is
*expected and healthy* for a headline theorem. It does, however, mean the inclusion case rests on the
result's standing in the literature (very high — see Phase 3), not on internal API pull.

---

### Composition check (Phase 6)

Can `tendsto_sub_one_mul_zetaPBranch` be derived from **mathlib** in ≤3 chained calls?

Attempt 1 (from a mathlib p-adic-zeta residue lemma, specialised): **fails immediately** — Phase 5
shows mathlib has *no* p-adic zeta / KL object at all, hence no residue lemma to specialise.

Attempt 2 (final-assembly glue, treating the project lemmas as inputs):
`(hden.inv₀ …).mul hnumlim |>.congr …` after a `rw [hval]`.
  - Mathlib decls used in the *glue*: `Filter.Tendsto.inv₀` (`Mathlib/Topology/Algebra/GroupWithZero.lean`),
    `Filter.Tendsto.mul` (`Mathlib/Topology/Algebra/Monoid/Defs.lean`), `Filter.Tendsto.congr`,
    `ContinuousAt.mono_left`/`nhdsWithin_le_nhds`, plus `field_simp`/`ring` for the value `hval`.
  - Result: **the mathlib content is ONLY the generic limit-arithmetic glue** — but the three inputs
    are deep project-local theorems, none in mathlib:
    - `tendsto_branch_denom_div` (`ResidueZeta.lean:231`, itself `BORDERLINE`) — the denominator
      limit `(s−1)⁻¹·denom → −log_p⟨u⟩`, a genuine squeeze through the quadratic exp-tail bound.
    - `continuous_zetaNum_branch_pairing` (`ResidueZeta.lean:360`) — a `1`-Lipschitz `p^m`-congruence
      sup-norm bound on the pseudo-measure pairing.
    - `zetaNum_one` (`ResidueZeta.lean:1666`, `BORDERLINE`) — the total-mass identity
      `num 1 = −(1−p⁻¹)·log_p(m)`, proved by a `ℂ_p`-descent through `F̃_a`/`ρ_a`.
    - plus `extLog_natCast_eq_pZpLog_angle` and `pZpLog_angleUnit_ne_zero` (the `L ≠ 0` step).
  - Notes: stripping the mathlib glue leaves an entire multi-lemma analytic proof; the substance is
    *all* project-specific and itself absent from mathlib.

Attempt 3 (from mathlib's KL machinery): **vacuous** — Phase 5 shows mathlib4 has no p-adic-L
development to compose from.

Conclusion: **NOT-COMPOSABLE** (from mathlib). The theorem's final assembly is generic limit
arithmetic (≤3 mathlib calls), but its *inputs* are deep project-local results with no mathlib
counterpart. "Compose from mathlib primitives" is impossible: there are no mathlib primitives for
this object. (And even within the project it is not a ≤3-call composition — it is the capstone of a
~1800-line file.)

---

## Verdict: `PadicLFunctions.tendsto_sub_one_mul_zetaPBranch`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the statement — `ζ_{p,p−1}` has a **simple pole at `s=1` with
  residue `1 − p⁻¹`** — is the **canonical, literature-named** result (RJW = arXiv 2309.15692 /
  ENT-MSP 2025; Washington; C. Williams Warwick notes; Koblitz; Venkatesh), quoted **verbatim** in
  multiple sources. It *is* RJW Theorem 7.1(ii). A Lean-3/mathlib3 formalization of the surrounding
  KL machinery exists (Narayanan) but was **not** ported to mathlib4.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** — it is the standard form; the `Tendsto`-limit
  spelling is the faithful rendering of "simple pole, residue `1 − p⁻¹`"; 0 weakening opportunities
  (twisting to `L_p(s,χ)` is a *broader* theorem, not a weakening). Phase 4c: a `MeromorphicAt` +
  residue repackaging is the aspirational modern idiom but is **not realisable** — mathlib has no
  p-adic-analytic/meromorphic theory for this object.
- Mathlib search (Phase 5): **not in mathlib4, and neither is the underlying object or any
  prerequisite** — mathlib4 has *zero* KL / p-adic-L / p-adic-zeta machinery, no p-adic log/exp, no
  analytic theory on `addChar_of_value_at_one`; the archimedean `riemannZeta` residue API cannot
  specialise to the p-adic field.
- Composition check (Phase 6): **NOT-COMPOSABLE** from mathlib (no p-adic-L primitives exist
  upstream; the mathlib content is only generic limit-arithmetic glue over deep project-local
  theorems).
- Call sites (Phase 6.0): **K = 0**, no inline re-derivation — *expected* for the file's terminal
  headline theorem (it is the goal of the development, not reusable plumbing).

**Rationale (why BORDERLINE, not a clean YES or NO):**

This is the **strongest mathlib candidate of the four `ResidueZeta.lean` results assessed**: unlike
its supporting lemmas (`tendsto_branch_denom_div`, `zetaNum_one`, which are construction-internal
bookkeeping with no standalone literature name), this theorem is a *headline, universally-cited,
literature-named* statement — the p-adic analogue of `ζ`'s pole at `s=1`, with the canonical residue
`1 − p⁻¹` quoted verbatim across the standard sources. It is true, sorry-free, MAXIMALLY GENERAL
(Phase 4b), genuinely missing from mathlib4 (Phase 5), and NOT composable from mathlib (Phase 6). On
content alone it is exactly the kind of named theorem mathlib wants. So it is **not a NO** — neither
`NO-mathlib-has-it` (mathlib has nothing, not even a more general form to specialise from) nor
`NO-composable-from-mathlib` (there are no mathlib building blocks; the proof is a capstone argument,
not a 1–3 call composition).

But a clean `YES-add-as-is` is blocked by one decisive, non-content fact that the skill cannot resolve
on its own: **the theorem cannot be PR'd standalone — it sits at the very top of a p-adic-L-function
tower that is absent from mathlib4 in its entirety.** Its statement names `zetaPBranch` (→ `branchChar`,
`zetaNum`, `padicZeta` pseudo-measure, `onePAdicPow`, `exists_nat_topological_generator`), its target
value rests on `extLog`/`padicLog`/`padicExp` and the `PadicMeasure` framework, and its proof runs
through the quadratic exp-tail bound and a `ℂ_p`-descent — *every one* of these is project-local, with
**zero** mathlib counterpart (Phase 5 grep returns nothing for the whole stack). Upstreaming this one
theorem necessarily means upstreaming that entire multi-file development first (the p-adic exp/log/power
theory; the p-adic-measure / Amice–Mahler-transform layer; the `padicZeta` pseudo-measure and the
branch construction). Whether to undertake that BIG, multi-decl programme — and, if so, in what order
and in what mathlib-idiomatic shape (e.g. eventually as `MeromorphicAt` + `residue`, once a p-adic
meromorphy theory exists) — is precisely the strategic/maintainer judgment this skill defers to the
human. This is the *same* gating question that governs all three siblings; per the verdict gate, the
fact that a clean YES depends on an upstreaming decision the worker cannot make is the textbook
BORDERLINE situation, and the residue theorem is the natural **headline** of that upstreaming unit
(its supporting lemmas, including the two `BORDERLINE` siblings, become internal helpers of *its* proof).

Note (gate compliance): cost is **not** the reason for BORDERLINE here — the expense of upstreaming the
tower is real but, per the philosophy doc, EXPENSIVE is not a downgrade. The reason is the **prerequisite
absence + the strategic upstreaming decision** (a genuine human judgment), not "too expensive". And the
MAXIMALLY-GENERAL Phase-4b finding means that *if* Q1 is answered "yes, upstream", this resolves cleanly
to `YES-add-as-is` (ship the residue theorem as the headline of the KL development), with the
`MeromorphicAt`/residue repackaging a possible later strengthening once a p-adic meromorphy framework
lands — not to `YES-but-generalise-first` (there is no generalisation of *this* statement to perform;
the twisted `L_p(s,χ)` version is a separate, broader theorem).

**Numbered questions (≤5):**

1. **Is the Kubota–Leopoldt p-adic-L-function development in this `PadicLFunctions` project intended to
   be upstreamed to mathlib4** — i.e. are `padicZeta`, `zetaPBranch`, `zetaNum`, the `PadicMeasure`
   pseudo-measure layer, and the `padicExp`/`padicLog`/`extLog`/`onePAdicPow` analytic stack future
   mathlib PR targets? This is the gating question. If **no**, this theorem (and its three siblings) is
   a project-internal milestone, out of mathlib scope — stop here. If **yes**, proceed to Q2.

2. If yes to Q1: this residue theorem is the **literature-named headline** (RJW Thm 7.1(ii)). Should it
   be the designated *headline declaration* of the upstreamed KL "regularity" PR, with its supporting
   lemmas (`tendsto_branch_denom_div`, `continuous_zetaNum_branch_pairing`, `zetaNum_one`, the
   `extLog`/`pZpLog` steps) shipped as internal helpers of its proof rather than as standalone public
   results? (Recommended: yes — the literature names the residue, not the intermediate identities.)

3. If yes to Q1: what is the **upstreaming order**? The theorem cannot land before its prerequisites.
   The natural sequence is: (a) p-adic `exp`/`log`/power-map analytic theory (with `tendsto_branch_denom_div`'s
   `HasDerivAt`-style content); (b) the p-adic-measure / Amice–Mahler-transform + `padicZeta` pseudo-measure;
   (c) the branch construction `zetaPBranch`; (d) **this** residue theorem as the capstone. Confirm this
   ordering (it determines when to re-run `/mathlibable` on this decl).

4. When the analytic framework is available, should the final mathlib form be repackaged from the
   `Tendsto`-limit into a structured **`MeromorphicAt (zetaPBranch p hp2 (p−1)) 1` + `residue = 1 − p⁻¹`**
   statement (Phase 4c — composes with mathlib's meromorphy/residue API), or is the punctured-`Tendsto`
   form the right grain? (This needs a p-adic meromorphy theory that does not yet exist; it is a
   later-PR repackaging decision, not a blocker for the first landing.)

5. Should the mathlib API expose the **per-branch** functions `ζ_{p,i}` (as here) or the single
   pseudo-measure / `L_p(s,χ)`-style object that specialises to them — i.e. which is the canonical mathlib
   spelling, and is the *twisted* `L_p(s,χ)` pole-at-trivial-character theorem the broader target that
   this untwisted residue should be a corollary of?

**Next action:** the maintainer answers **Q1** first.
- If **no** → drop from mathlib consideration (keep as the headline project milestone of `ResidueZeta.lean`).
- If **yes** → sequence the *infrastructure first* (per Q3: the p-adic exp/log/power theory, then the
  p-adic-measure / `padicZeta` layer, then `zetaPBranch`), and **re-run `/mathlibable
  tendsto_sub_one_mul_zetaPBranch` once those prerequisites have landed** — at which point, given the
  MAXIMALLY-GENERAL Phase-4b finding, it resolves to **`YES-add-as-is`** (the literature-named residue
  theorem as the capstone of the KL development), with the `MeromorphicAt`/residue repackaging (Q4) as a
  possible follow-up PR. It should be assessed and shipped **together with** its three siblings (they are
  governed by the single upstreaming decision and become internal helpers of this theorem's proof).

---

## Next step

The maintainer answers the gating question (Q1): **is the project's Kubota–Leopoldt p-adic-L-function
tower being upstreamed to mathlib4?** If no → out of mathlib scope (project-internal headline milestone).
If yes → upstream the prerequisite infrastructure first (p-adic exp/log/power theory, then the
p-adic-measure / `padicZeta` layer, then `zetaPBranch`), then re-run `/mathlibable` on this theorem — it
then resolves to **`YES-add-as-is`** as the literature-named headline (RJW Thm 7.1(ii)) of the KL
development, ideally repackaged as `MeromorphicAt`+`residue` once a p-adic meromorphy framework exists,
and shipped as one unit with its three supporting siblings.
