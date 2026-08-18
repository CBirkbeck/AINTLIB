# `/mathlibable` report — `PadicLFunctions.MeasureR.norm_one_sub_pow_eq_one`

**Final verdict: `NO-composable-from-mathlib`** (sign-flip wrapper of the sibling
project lemma `IsPrimitiveRoot.norm_pow_sub_one_eq_one`; 2-call composition, zero
call sites). See the caveat in Phase 7: the *building block it composes from* is a
project lemma, not a mathlib one — that sibling is the genuine mathlib candidate,
not this wrapper.

---

### Baseline (Phase 0)
- lake build:               not re-run; reasoned from source (per task BUILD NOTE — read the decl + its dependency closure directly).
- decl `PadicLFunctions.MeasureR.norm_one_sub_pow_eq_one`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ValuesAtOne.lean:66`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  RJW §6.2 Thm 6.1(ii) — the p-adic value `L_p(θ,1)` (Leopoldt); this decl is the "arguments are norm-one units" sub-fact P6-p9.

---

### Statement (Phase 1)

`PadicLFunctions.MeasureR.norm_one_sub_pow_eq_one` is a theorem stating the following:

Let `K` be a complete ultrametric normed field over `ℚ_p` (`NormedField`, `NormedAlgebra ℚ_[p] K`,
`IsUltrametricDist`), let `D > 1` be a natural number **not** divisible by the prime `p`, let `ε ∈ K`
be a **primitive `D`-th root of unity**, and let `c` be a natural number with `D ∤ c`. Then the
ultrametric norm of `1 − ε^c` equals one:

```
‖1 − ε^c‖ = 1.
```

Mathematically: in a complete nonarchimedean field over `ℚ_p`, when `p ∤ D` the extension generated
by the `D`-th roots of unity is unramified, so every `1 − ε^c` with `ε^c ≠ 1` is a `p`-adic unit
(norm 1). This is the classical "`1 − ζ` is a unit when the residue characteristic does not divide
the order" fact, restricted to the difference `1 − ε^c`.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the residue prime.
- `K : Type*`, `[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]` — the coefficient field. (`[CompleteSpace K]` and `[CharZero K]` are `omit`-ted for this decl — not used.)
- `D : ℕ`, `[NeZero D]` — the order of the root.
- `ε : K` — the primitive `D`-th root.
- `c : ℕ` — the exponent.

Hypotheses (Lean side):
- `_hD1 : 1 < D` — **unused** (underscore-prefixed; the proof never references it). A redundant hypothesis carried for narrative symmetry with the conductor `D > 1`.
- `hD : ¬ (p : ℕ) ∣ D` — `p` does not divide the order (the unramifiedness condition).
- `hε : IsPrimitiveRoot ε D` — `ε` is a primitive `D`-th root.
- `hc : ¬ D ∣ c` — `ε^c ≠ 1`.

Conclusion (math): `1 − ε^c` is a `p`-adic unit, i.e. `|1 − ε^c|_p = 1`.

Conclusion (Lean): `‖1 - ε ^ c‖ = 1`.

**Proof body (the whole thing — 2 lines):**
```lean
  rw [← norm_neg, neg_sub]
  exact hε.norm_pow_sub_one_eq_one (p := p) hD hc
```
It flips `‖1 − ε^c‖ = ‖−(1 − ε^c)‖ = ‖ε^c − 1‖` (`norm_neg` + `neg_sub`) and then applies the
sibling lemma `IsPrimitiveRoot.norm_pow_sub_one_eq_one` (the `‖ε^c − 1‖ = 1` form). The unused
`_hD1` is not even threaded through.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A helper sub-fact (P6-p9), not a `## Main results` item; not named after a person/place; not a new structure. It is a one-statement-flip corollary of a sibling lemma in the same project.

(Literature width is EXHAUSTIVE regardless. SMALL is recorded for framing.)

### One-line check (Phase 2b)

Body line count: n/a — kind is `theorem`, not `def`. One-liner verdict: **n/a (theorem)**.
(Note for framing: the *proof* is 2 lines, but Phase 2b's one-liner gate applies only to `def`/`abbrev`/`structure`. Recorded as n/a.)

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "1 minus root of unity is a p-adic unit when prime does not divide order, ramification cyclotomic field" | yes  | `p ∤ n ⇒ Q_p(ζ_n)/Q_p` unramified `⇒ 1−ζ_n` a unit; `n=p^r ⇒` totally ramified, `1−ζ_{p^r}` a uniformizer | K. Conrad cyclotomic/p-adic notes, Erickson "Cyclotomic Fields"; standard dichotomy |
|  2 | WebSearch (general form / norm one) | `"1 - zeta" unit p-adic "p does not divide n" cyclotomic primitive root of unity norm one`            | yes  | `1−ζ_n` is a unit; when `p∤n` the factors `1−ζ^i` (`n∤i`) all have norm 1 | Columbia/Garrett cyclotomic notes; "1−ζ uniformizer iff totally ramified" |
|  3 | WebSearch (named-after / Washington) | `Washington cyclotomic fields lemma "1 - zeta" unit l does not divide n totally ramified at primes dividing n` | yes  | Washington, *Intro. to Cyclotomic Fields*: `ℓ` ramifies fully in `Q(ζ_{ℓ^e})`, all other primes unramified; `1−ζ_n` a unit when ≥2 primes divide `n` | Tom Lovering / Hida lecture notes cite the same lemma |
|  4 | ChatGPT MCP                      | (would ask: standard form + generality + historical evolution of "`1−ζ` is a `p`-adic unit when `p∤ord`") | n/a  | server not configured            | **n/a — no ChatGPT MCP server is configured in this environment** (`~/.claude` has no chatgpt MCP entry). Compensated by extra WebSearch breadth (#1–3) + the project's verbatim source citation (RJW TeX 1798) recorded in the summary below. |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/`                                            | n/a  | directory absent                 | **n/a — no `references/` dir and no `refs/` symlink** in this checkout. But the project source itself quotes the source: RJW TeX 1798, "`ε_D^c − 1 ∈ 𝒪_L^×` (since it has norm dividing `D`)". |
|  6 | nLab                             | "cyclotomic field unramified prime not dividing conductor 1 minus zeta unit valuation"                  | no   | nLab has no dedicated page on this elementary valuation fact | nLab's cyclotomic content is higher-level; the lemma is classical algebraic number theory, below nLab's abstraction band. Recorded as searched-and-absent, not skipped. |
|  7 | nCatLab (if categorical)         | —                                                                                                       | n/a  | not a categorical concept        | **n/a — a valuation/norm identity on a single field element; no categorical content.** |
|  8 | Stacks Project (if alg geom)     | (ramification of `Z[ζ_n]` at `p`)                                                                       | n/a  | not the right register           | **n/a — Stacks treats ramification scheme-theoretically; this concrete `|1−ζ^c|_p = 1` statement is classical ANT, not in Stacks' idiom.** The underlying unramifiedness is of course derivable from Stacks-style étale theory, but the norm-one statement itself is not a Stacks lemma. |
|  9 | MathOverflow / Math.StackExchange| "1 − ζ unit p-adic p does not divide n" (surfaced via #1–3 web sweep)                                    | yes  | MSE/MO threads restate the same dichotomy (uniformizer at `p∣n`, unit otherwise) | Consistent with #1–3; no variant statement found |
| 10 | recent arXiv (last 5 years)      | (via #1–3): arXiv:1109.2860 "norms of special elements of cyclotomic fields"; arXiv:1307.3459 Kummer/FLT | yes  | confirm classical `1−ζ` valuation facts; no *new* form | The fact is 19th–20th century; recent arXiv only reuses it |

The protocol passed: WebSearch ran **3 distinct queries at three generality levels** (specific `1−ζ` form, the norm-one/general form, and the named-after/Washington form); ChatGPT MCP recorded `n/a` with a concrete reason (no server) **and** compensated via the project's verbatim source quote; local refs recorded `n/a` (absent) with the source quote substituted; nLab checked (absent); nCatLab / Stacks / MO / arXiv each checked or `n/a` with reasons.

### Literature summary (Phase 3)

Concept identified as: **"`1 − ζ` is a `p`-adic unit when `p` does not divide the order of `ζ`"** — equivalently, the unramifiedness of `Q_p(ζ_D)/Q_p` for `p ∤ D`, restricting to the difference `1 − ε^c` with `D ∤ c`. Classical; treated in Washington, *Introduction to Cyclotomic Fields* (Ch. 2), Lang, *Cyclotomic Fields*, Neukirch *ANT* (ramification of cyclotomic extensions), and every set of p-adic/cyclotomic lecture notes.

Sources agree on the standard form: **yes**. The universal dichotomy: `1 − ζ_n` is a unit at `p` iff `p ∤ n` (when `p ∣ n`, `1 − ζ_{p^r}` carries positive valuation — a uniformizer in the totally ramified `p`-part).

Most general standard form: for `ζ` a primitive `D`-th root of unity in a nonarchimedean field over `ℚ_p` with `p ∤ D`, and any exponent `c` with `D ∤ c` (so `ε^c ≠ 1`), `|1 − ε^c| = 1`. The project's `IsPrimitiveRoot.norm_pow_sub_one_eq_one` states exactly this in the equivalent form `‖ε^c − 1‖ = 1`.

Generality dimensions where the literature varies:
- **Field**: from `Q(ζ)`/`Z[ζ]` (global, with valuation `v_p`) up to any complete ultrametric `ℚ_p`-algebra. The project takes the latter (maximal) generality — `[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]`. The literature standard at this norm is the same.
- **Statement register**: ideal-theoretic (`(1−ζ)` a unit ideal), valuation-theoretic (`v_p(1−ζ)=0`), or norm/absolute-value (`|1−ζ|_p = 1`). All three are the same fact; the project uses the norm register, which is the right one for a `NormedField`.
- **`_hD1 : 1 < D`** is *not* a literature dimension — the literature needs only `p ∤ D` and `D ∤ c`; `D > 1` is implied by `D ∤ c` with `c` allowed to be `0`/the existence of `ε`. The hypothesis is redundant (and indeed unused in the proof).

Disagreement with the literature: **none.** The statement is exactly the classical fact; the only deviation is the redundant `_hD1` hypothesis and the cosmetic `1 − ε^c` orientation (literature/mathlib idiom would write `ε^c − 1`).

---

### Generality analysis — `PadicLFunctions.MeasureR.norm_one_sub_pow_eq_one` (Phase 4)

Literature-standard form (from Phase 3): `‖ε^c − 1‖ = 1` for `ε` a primitive `D`-th root in a complete ultrametric `ℚ_p`-algebra, `p ∤ D`, `D ∤ c`. **The project already has this** as `IsPrimitiveRoot.norm_pow_sub_one_eq_one` (Coefficients.lean:211), stated over `[NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L]` with hypotheses exactly `(hζ : IsPrimitiveRoot ζ D) (hD : ¬ p ∣ D) (hc : ¬ D ∣ c)` — no `1 < D`.

| # | Parameter / hypothesis      | Current Lean form                         | Literature-standard form         | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------|-------------------------------------------|----------------------------------|---------------------|---------------------------------|
| 1 | `K` typeclasses             | complete ultrametric `ℚ_p`-normed field   | complete nonarch. `ℚ_p`-algebra  | already maximal (and `CompleteSpace`,`CharZero` are *omit*-ted as unused here) | The sibling `norm_pow_sub_one_eq_one` shows even `CompleteSpace` is droppable for this norm-one fact; this decl already omits it. Maximally general on the field. |
| 2 | `_hD1 : 1 < D`              | `1 < D` (UNUSED)                          | not required                     | **yes — remove it**  | The proof never uses it; the sibling lemma has no such hypothesis. Pure redundancy. |
| 3 | `hD : ¬ p ∣ D`             | `p ∤ D`                                    | `p ∤ D`                          | NO                  | This is the unramifiedness condition; essential (false otherwise). |
| 4 | `hε : IsPrimitiveRoot ε D` | primitive `D`-th root                     | primitive `D`-th root            | NO                  | Essential. |
| 5 | `hc : ¬ D ∣ c`            | `D ∤ c`                                    | `D ∤ c` (i.e. `ε^c ≠ 1`)        | NO                  | Essential. |
| 6 | conclusion orientation     | `‖1 − ε^c‖`                               | `‖ε^c − 1‖`                     | equivalent (sign flip) | `norm_neg`/`neg_sub`; the `ε^c − 1` orientation is the mathlib/literature idiom and already in the project. |

### Generality verdict (Phase 4b)

The current form is: **NOT MAXIMALLY GENERAL** — it carries one redundant hypothesis (`_hD1 : 1 < D`) and a non-idiomatic orientation, *and* it is strictly weaker/derivative relative to the sibling `IsPrimitiveRoot.norm_pow_sub_one_eq_one` which is the same fact, hypothesis-minimal, in the standard orientation.
Number of weakening opportunities found: 2 (drop `_hD1`; reorient `‖1−ε^c‖ → ‖ε^c−1‖`) — both are *exactly* the moves that turn this decl into the already-existing sibling.
Proposed restatement: there is nothing to restate — the maximally-general, idiom-correct version **already exists in the project** as `IsPrimitiveRoot.norm_pow_sub_one_eq_one`. This decl is its `1 − x` mirror.
Cost of restatement: CHEAP (it is a 2-line `norm_neg`/`neg_sub` rewrite — and that rewrite is literally this decl's proof body).

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                  | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|-------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "Let X be a foo" preambles → typeclasses/instances?                                        | no       | already fully typeclass-based (`IsUltrametricDist`, `NormedAlgebra`) | — |
|  2 | Sequences/metric → filters/topological?                                                    | no       | a single algebraic norm identity; no limit/filter content | — |
|  3 | Construct an object → universal-property class?                                            | no       | it is a `Prop`, not a construction | — |
|  4 | Set-with-closure-predicate → bundled substructure?                                         | no       | no substructure here | — |
|  5 | Vector-space/metric/field-specific → weaken typeclass hierarchy?                            | no (already general) | field/ultrametric is the right register for `‖·‖`; the sibling shows even `CompleteSpace` is droppable | — |
|  6 | 1-categorical → higher-categorical?                                                        | no       | none | — |
|  7 | Concrete index (ℕ,ℤ,ℝ) → arbitrary group/monoid?                                            | no       | the exponent `c : ℕ` and order `D : ℕ` are the natural register (roots of unity are indexed by ℕ) | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no.** One-line reason: the statement is already in the contemporary, maximally-typeclassed register; the only "modernisation" is to drop the redundant `_hD1` and use the `ε^c − 1` orientation — which is not a modernisation but a deduplication onto the existing sibling lemma.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem`. (No definitional equalities or typeclass-search paths introduced.)

---

### Mathlib search-status: `PadicLFunctions.MeasureR.norm_one_sub_pow_eq_one` (Phase 5)

```
[A] Lean-Finder       n/a — Lean-Finder MCP not available in this environment; substituted by [B][C][D][E].
[B] Loogle            ‖?z ^ ?c - 1‖ = 1   → parsed, 39 decls mention Norm.norm/HSub.hSub, 0 match the pattern.
                      IsPrimitiveRoot,Norm.norm,= 1  → (first attempt malformed; the clean pattern query returned no ultrametric hit)
[C] LeanSearch        "norm of a primitive root of unity minus one equals one p-adic unit"  → n/a: leansearch.net API returned HTTP 404 (endpoint unavailable this session). Compensated by [B][D][E].
[D] Grep mathlib src  ‖.. - 1‖ = 1 / ‖1 - ..‖ = 1 in Mathlib/Analysis/**; IsPrimitiveRoot in Mathlib/Analysis/**  → no hits.
                      IsPrimitiveRoot.norm_pow_sub_one_* in Mathlib/  → hits, but ALL are `Algebra.norm K (ζ^p^s − 1) = p^p^s` (field-norm, in NumberTheory/Cyclotomic/PrimitiveRoots.lean) — a DIFFERENT object (algebraic norm, not the ultrametric absolute value).
                      norm_sub_one_lt in Mathlib/  → only Unitary.norm_sub_one_lt_two_iff (C*-algebras, unrelated). The ultrametric `‖ζ−1‖<1` sibling is NOT in mathlib (project defines it itself at Coefficients.lean:151).
[E] Name pattern      grep `norm_pow_sub_one_eq_one`, `norm_one_sub_pow`, `norm_sub_one` over mathlib  → the only `‖·‖`-norm primitive-root facts are project-local; mathlib has only the `Algebra.norm` family.
```

Searched for both:
  - the user's current form `‖1 − ε^c‖ = 1` — no mathlib hit.
  - the literature-standard form `‖ε^c − 1‖ = 1` — no mathlib hit (mathlib's `IsPrimitiveRoot.norm_pow_sub_one_*` is the **algebraic field norm** `Algebra.norm K`, giving `p^{p^s}`, defined only in the `IsCyclotomicExtension`/`Irreducible (cyclotomic …)` setting — not the ultrametric absolute value on a `NormedField`, and not the `p∤D` unramified case).

Concluded: **not in mathlib** (Loogle pattern 0-match; mathlib grep finds only the algebraic-`Algebra.norm` cousins; the ultrametric `‖·‖` norm-one form is absent — the project itself supplies both this fact and its `< 1` sibling from scratch). **However**, the user's form IS derivable in ≤1 mathlib-style line *from the project's own sibling lemma* `IsPrimitiveRoot.norm_pow_sub_one_eq_one` — which is itself a project (non-mathlib) decl. The relevant *supporting* mathlib pieces (`IsPrimitiveRoot.prod_one_sub_pow_eq_order` in `RingTheory/RootsOfUnity/Lemmas.lean`, `Padic.norm_natCast_eq_one_iff`, `IsUltrametricDist.norm_add_le_max`) are the building blocks of the *sibling's* proof, not of this wrapper.

---

### Call sites — `PadicLFunctions.MeasureR.norm_one_sub_pow_eq_one` (Phase 6.0)

Internal use count: **0** (within the project, excluding the declaring line).
External-to-file callers: **0 distinct files**.

| Caller file:line                     | Usage pattern (one-line excerpt)                                              |
|--------------------------------------|------------------------------------------------------------------------------|
| ValuesAtOne.lean:102 (docstring)     | `(\`norm_one_sub_pow_eq_one\`); lifting along …` — **comment, not a call**     |
| ValuesAtOne.lean:761 (docstring)     | `… T612 \`norm_one_sub_pow_eq_one\`). The original ¬N∣c-guard …` — **comment** |
| ValuesAtOne.lean:1339 (comment)      | `… T612 \`norm_one_sub_pow_eq_one\` after stripping the` — **comment**         |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `norm_one_sub_pow_eq_one`?):
  - **Yes — pervasively.** Every actual norm-one use in the project calls the sibling `IsPrimitiveRoot.norm_pow_sub_one_eq_one` (the `ε^c − 1` form) directly, *not* this `1 − ε^c` wrapper:
    - `ValuesAtOne.lean:70` — `exact hε.norm_pow_sub_one_eq_one (p := p) hD hc` (inside this very file, the sibling, not the wrapper)
    - `ValuesAtOne.lean:122` — `exact hεD.norm_pow_sub_one_eq_one (p := p) hD hDc`
    - `Interpolation/NonTame.lean:50` — `simpa using hζK.norm_pow_sub_one_eq_one (p := p) hD hc`
    - `Interpolation/NonTame.lean:118` — `have h1 : ‖(ζ : K) ^ c - 1‖ = 1 := hζK.norm_pow_sub_one_eq_one (p := p) hD hc`
    - `ValuesAtOne.lean:1736` — the assembly threads `norm_pow_sub_one_eq_one_of_unit` (which itself calls the sibling, not this wrapper).

**Call-sites pattern → composability signal:** `K = 0` internal uses **and** the equivalent statement is obtained inline at ≥5 sites *via a sibling lemma that is not this one*. Per the Phase-6 pattern table this is the canonical "wrapper consumers bypass" signal → leans **NO-composable**. The `1 − ε^c` orientation this wrapper provides is simply never the orientation consumers want; they all want `ε^c − 1` and get it from the sibling.

### Composition check (Phase 6)

Can `norm_one_sub_pow_eq_one` be derived in ≤3 chained calls?

Attempt 1 (the literal proof body): `by rw [← norm_neg, neg_sub]; exact hε.norm_pow_sub_one_eq_one (p := p) hD hc`
  - Decls used: `norm_neg`, `neg_sub` (both mathlib), `IsPrimitiveRoot.norm_pow_sub_one_eq_one` (**project** sibling).
  - Result: **succeeds** — it is exactly the declared proof.
  - Notes: 1 rewrite (`norm_neg`+`neg_sub` is a single `rw` step normalising `‖1−x‖` to `‖x−1‖`) + 1 `exact`. Comfortably ≤3 calls. The orientation flip `‖1 − ε^c‖ = ‖ε^c − 1‖` is `norm_neg`/`neg_sub`, a pure mathlib idiom.

Conclusion: **COMPOSABLE** — a ≤2-call composition. The only nuance is that one of the two building blocks (`IsPrimitiveRoot.norm_pow_sub_one_eq_one`) is a *project* lemma, not a mathlib one, so the composition's substance lives in the sibling. The wrapper itself contributes nothing beyond the `1−x ↔ x−1` sign flip, which mathlib's `norm_neg`/`neg_sub` already provide.

---

## Verdict: `PadicLFunctions.MeasureR.norm_one_sub_pow_eq_one`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): classical fact ("`1−ζ` is a `p`-adic unit when `p∤ord`", Washington Ch. 2); the maximally-general norm-one form is the `ε^c − 1` orientation, which the project *already* has as `IsPrimitiveRoot.norm_pow_sub_one_eq_one`. No disagreement; this decl's only deltas are a redundant `_hD1` and a non-idiomatic `1 − ε^c` orientation.
- Generality analysis (Phase 4): NOT MAXIMALLY GENERAL — one unused hypothesis (`_hD1`) and a sign-flip away from the existing, hypothesis-minimal sibling; Phase 4c found no modern-idiom improvement.
- Mathlib search (Phase 5): not in mathlib in either orientation (mathlib's `IsPrimitiveRoot.norm_pow_sub_one_*` is the *algebraic* `Algebra.norm`, a different object); the ultrametric form is project-local.
- Composition check (Phase 6): **COMPOSABLE** — `rw [← norm_neg, neg_sub]; exact hε.norm_pow_sub_one_eq_one …` (≤2 calls); call sites `K = 0`, with all real consumers bypassing this wrapper for the sibling.

**Rationale:**

This declaration is not a mathlib candidate in its own right: it is a **sign-flip wrapper** (`‖1 − ε^c‖` instead of `‖ε^c − 1‖`) around the sibling project lemma `IsPrimitiveRoot.norm_pow_sub_one_eq_one`, carrying one hypothesis (`_hD1 : 1 < D`) that the proof never uses. Its entire body is `rw [← norm_neg, neg_sub]; exact hε.norm_pow_sub_one_eq_one (p := p) hD hc` — a single mathlib orientation rewrite plus a call to the sibling. It has **zero call sites**: every place in the project that needs a norm-one fact (ValuesAtOne.lean:70, :122, NonTame.lean:50, :118, and via `norm_pow_sub_one_eq_one_of_unit` at :1736) invokes the `ε^c − 1` sibling directly, never this `1 − ε^c` form. That is the textbook "wrapper consumers bypass" pattern.

The honest caveat the skill demands: the *building block this composes from* — `IsPrimitiveRoot.norm_pow_sub_one_eq_one` — is itself a **project** lemma, not a mathlib one (mathlib has only the algebraic-field-norm cousins in `NumberTheory/Cyclotomic/PrimitiveRoots.lean`, a genuinely different object). So this is not literally "compose from *mathlib* primitives": the substance is in the sibling. But for **this specific declaration**, the correct disposition is unambiguous — it adds nothing over the sibling except a sign flip that `norm_neg`/`neg_sub` already give, so it should not be shipped to mathlib and (within the project) is a redundant alias. The genuinely mathlib-worthy object in this neighbourhood is the sibling `IsPrimitiveRoot.norm_pow_sub_one_eq_one` (the ultrametric "`‖ζ^c − 1‖ = 1` for `p ∤ D`, `D ∤ c`" fact, which mathlib lacks), and assessing *that* is a separate `/mathlibable` run — likely `YES-add-as-is` or `YES-but-generalise-first`, since mathlib genuinely has no ultrametric-norm version, only the algebraic-norm family.

**WHY not (refactor-actionable):**
Mathlib has the orientation-flip building blocks (`norm_neg`, `neg_sub`); the substance (`‖ε^c − 1‖ = 1`) is supplied locally by the sibling lemma. No new mathlib lemma is justified for the `1 − ε^c` form — it is `norm_neg`/`neg_sub` away from the sibling, and consumers already use the sibling.

Mathlib building blocks (for the orientation flip): `norm_neg` (`Mathlib/Analysis/Normed/Group/Basic.lean`), `neg_sub` (`Mathlib/Algebra/Group/Basic.lean`).
Project building block (the substance): `IsPrimitiveRoot.norm_pow_sub_one_eq_one` (`projects/PadicLFunctions/PadicLFunctions/Coefficients.lean:211`).

Composition sketch (≤3 lines — and this is literally the current proof body):
```lean
example {D : ℕ} (hD : ¬ (p:ℕ) ∣ D) {ε : K} (hε : IsPrimitiveRoot ε D) {c : ℕ}
    (hc : ¬ D ∣ c) : ‖1 - ε ^ c‖ = 1 := by
  rw [← norm_neg, neg_sub]; exact hε.norm_pow_sub_one_eq_one (p := p) hD hc
```

Call sites in our project (from Phase 6.0): **K = 0**.
Refactor plan: since `K = 0`, there are no call sites to migrate. Within the project, **delete `PadicLFunctions.MeasureR.norm_one_sub_pow_eq_one`** (it is dead: 0 term-level uses, only 3 docstring mentions). Anywhere a `‖1 − ε^c‖ = 1` is ever needed, inline the two-line composition above (or, preferably, work in the `‖ε^c − 1‖` orientation and call the sibling directly, as every existing consumer already does). Update the 3 docstrings at ValuesAtOne.lean:102, :761, :1339 to reference the sibling `IsPrimitiveRoot.norm_pow_sub_one_eq_one` instead of this alias.
Next action: delete `norm_one_sub_pow_eq_one` from the project (no call sites to update); separately, run `/mathlibable PadicLFunctions.IsPrimitiveRoot.norm_pow_sub_one_eq_one` (the real mathlib candidate — the ultrametric norm-one cyclotomic fact mathlib is missing).

---

## Next step

Delete `PadicLFunctions.MeasureR.norm_one_sub_pow_eq_one` from the project — it has zero call sites and is a `norm_neg`/`neg_sub` sign-flip of the sibling `IsPrimitiveRoot.norm_pow_sub_one_eq_one`, which every real consumer already uses. Update the 3 docstring references to point at the sibling. Then assess the sibling itself with a separate `/mathlibable` run: the ultrametric `‖ζ^c − 1‖ = 1` (for `p ∤ D`, `D ∤ c`) fact is genuinely absent from mathlib (mathlib has only the algebraic-`Algebra.norm` family) and is the real upstreaming candidate.
