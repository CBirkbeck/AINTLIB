# `/mathlibable` report — `PadicLFunctions._root_.IsPrimitiveRoot.norm_sub_one_lt`

Mode A, full 10-phase workflow, exhaustive 9-channel literature search.
Qualified name: `IsPrimitiveRoot.norm_sub_one_lt` (declared with `_root_.` inside
`namespace PadicLFunctions`, so it lives in the **root** `IsPrimitiveRoot`
namespace — exactly the namespace mathlib uses for its cyclotomic lemmas).

---

## Verdict (five-bucket)

**`YES-but-generalise-first`** — the result is genuinely missing from mathlib
(mathlib has the *consumer* of `‖ζ−1‖<1` but not this *supply* lemma), it is
classical and standard in the literature, and it is not a ≤3-call composition.
But the current hypotheses are **strictly narrower than the literature-standard
form along two cheap axes** (the redundant `[NormedAlgebra ℚ_[p] L]` /
`CharZero` plumbing, and the unnecessary completeness assumption is already
dropped). The right mathlib statement weakens `‖p‖ < 1` to an explicit
`‖(p:L)‖ < 1` hypothesis and drops the `ℚ_[p]`-algebra scaffolding, making the
lemma a clean fact about **any nonarchimedean normed field of residue
characteristic `p`** — which is how the literature states it.

---

## Baseline (Phase 0)

- lake build:               not re-run (build is stale/slow per task note); **reasoned from source** — Phase 0 fallback. The declaration and its full dependency chain were read directly from `Coefficients.lean` and the pinned mathlib tree.
- decl `IsPrimitiveRoot.norm_sub_one_lt`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/Coefficients.lean:151`
- kind:                      theorem
- has sorry:                 no (complete proof, lines 152–196)
- mathlib pin:               `d90090f647cae4f4ad4da99c0ac8bab2ca8c34ab` (2026-06-08); toolchain `leanprover/lean4:v4.31.0-rc2`
- module docstring summary:  Coefficient rings for §5 — the integer ring (norm-unit ball) of a nonarchimedean complete normed `ℚ_[p]`-algebra field, and basic facts about `p^n`-th roots of unity used to build the Iwasawa algebra.

---

## Statement (Phase 1)

`IsPrimitiveRoot.norm_sub_one_lt` is a **theorem** stating the following:

> Let `L` be a complete nonarchimedean normed field that is a normed
> `ℚ_p`-algebra (so its residue characteristic is `p`). If `ζ ∈ L` is a
> primitive `p^n`-th root of unity with `n ≥ 1`, then `‖ζ − 1‖ < 1`.

Mathematically: in a `p`-adic field, a primitive `p^n`-th root of unity is
congruent to `1` modulo the maximal ideal; equivalently `ζ − 1` lies in the
maximal ideal (has positive valuation); equivalently `ζ − 1` is topologically
nilpotent. The classical sharper statement is that `ζ − 1` is a *uniformizer*
of the totally ramified extension `ℚ_p(ζ)/ℚ_p` with
`v_p(ζ−1) = 1/(p^{n−1}(p−1))`; the lemma records only the qualitative
`‖ζ−1‖ < 1` that the downstream measure theory needs.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the residue characteristic.
- `L : Type*`, `[NormedField L]` — the ambient nonarchimedean field (the value field).
- `[NormedAlgebra ℚ_[p] L]` — makes `L` a `ℚ_p`-algebra; **only used** to obtain `‖(p:L)‖ < 1` (via `norm_natCast_self_lt_one`, the previous lemma).
- `[IsUltrametricDist L]` — the norm is nonarchimedean (ultrametric triangle inequality). Load-bearing.
- `[CompleteSpace L]` — **omitted** for this lemma (`omit [CompleteSpace L] in` at line 145); not used.

Hypotheses (Lean side):
- `hζ : IsPrimitiveRoot ζ (p ^ n)` — `ζ` is a primitive `p^n`-th root of unity.
- `hn : 1 ≤ n` — the order is a positive power of `p` (so `ζ ≠ 1`).

Conclusion (math): `ζ − 1` has p-adic absolute value `< 1`.

Conclusion (Lean): `‖ζ - 1‖ < 1`.

**Proof shape (read from source).** By contradiction assume `‖ζ−1‖ ≥ 1`. Set
`x = ζ−1`, `N = p^n`. Expand `1 = ζ^N = (x+1)^N` binomially, peel the `k=0`
term, isolate the top term `x^N = −∑_{k<N−1} x^{k+1}·C(N,k+1)`. The ultrametric
`exists_norm_finsetSum_le_of_nonempty` bounds the sum by one term
`x^{i+1}·C(N,i+1)`; since `0 < i+1 < N`, `Nat.Prime.dvd_choose_pow` gives
`p ∣ C(N,i+1)`, hence `‖C(N,i+1):L‖ ≤ ‖(p:L)‖`. Assemble
`‖x‖^N ≤ ‖p‖·‖x‖^N` with `‖x‖^N > 0`, so `1 ≤ ‖p‖` — contradicting
`norm_natCast_self_lt_one` (`‖p‖ = p^{-1} < 1`). This is the textbook
"`p` divides the inner binomial coefficients" argument.

---

## Size classification (Phase 2a)

**Verdict: SMALL** (leaning BIG-adjacent).
Reason: a single helper lemma (`W2` in the project decomposition), not a named
theorem and not a new structure. It is, however, a *named classical fact*
(uniformizer property of `1−ζ`) with broad reuse, which pushes its
mathlib-worthiness up despite the SMALL tag.

(Literature width is EXHAUSTIVE regardless; BIG/SMALL is narrative only.)

---

## One-line check (Phase 2b)

n/a — kind is `theorem`, not a `def`/`abbrev`/`structure`. No one-liner check.

---

## Literature search table — EXHAUSTIVE protocol (Phase 3)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "primitive p^n-th root of unity p-adic valuation zeta minus 1 less than 1 nonarchimedean" | yes | `v_p(1−ζ_{p^s}) = 1/φ(p^s) > 0` ⇒ `‖ζ−1‖ < 1` | arXiv 1507.01814 (p-adic L-functions on Hida families) states `v(1−ζ_{p^s}) = 1/φ(p^s)` verbatim |
| 2 | WebSearch (general / uniformizer form) | "cyclotomic units uniformizer p-adic field zeta-1 totally ramified valuation 1/(p^{n-1}(p-1))" | yes | "`ζ_{p^m}−1` is a uniformizer of `ℚ_p(ζ_{p^m})`"; `p = uπ^{p−1}`, `π=1−ζ_p` | Coates–Sujatha *Cyclotomic Fields and Zeta Values*; Viviani; arXiv 1912.01656 |
| 3 | WebSearch (named-after / aliases: "topologically nilpotent", "maximal ideal") | "root of unity p-power order topologically nilpotent zeta-1 maximal ideal local field" | yes | "`ζ_{p^l}−1` generates the maximal ideal of the local ring"; topologically nilpotent = elements of the maximal ideal | Hard Arithmetic (Ayoucis) local CFT notes; nLab "root of unity" (general only) |
| 4 | ChatGPT MCP | (asked for standard form + generality + historical evolution) | **n/a** | — | ChatGPT MCP server **not configured** in this environment (no `mcp__chatgpt*` tool surfaced). Substituted by the three WebSearch passes at different generality levels (#1–#3) + the textbook fetches (#9). Recorded as n/a-with-substitution per Phase-0 fallback. |
| 5 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/` | n/a | (no references dir) | `…/.mathlib-quality/references/` and `refs/` both absent on this checkout — recorded n/a. |
| 6 | nLab | "root of unity" (https://ncatlab.org/nlab/show/root+of+unity) | partial | general `μ_n = Spec R[t]/(t^n−1)`, finite-subgroup-cyclic | nLab page has **no** p-adic / nonarchimedean / uniformizer content; confirms the fact is not categorical, it is arithmetic. |
| 7 | nCatLab (categorical) | — | n/a | — | Not a categorical concept; it is a valuation-theoretic fact about a specific field. |
| 8 | Stacks Project | "ramification cyclotomic uniformizer" | n/a | — | Not a scheme-theoretic / algebraic-geometry statement; it is local-field arithmetic. Stacks treats ramification abstractly but has no "`1−ζ` is a uniformizer" entry. Recorded n/a with reason. |
| 9 | MathOverflow / Math.SE / textbooks | "why is 1 minus zeta_p a uniformizer Q_p"; "Washington Cyclotomic Fields Lemma 1.4"; KConrad notes fetch; nLab fetch | yes | unanimous: "`Q_p(ζ_{p^m})/Q_p` totally ramified, `1−ζ_{p^m}` a uniformizer satisfying an Eisenstein polynomial" | Washington *Intro to Cyclotomic Fields* 2nd ed. §1; KConrad "Totally ramified primes and Eisenstein polynomials"; Erickson, Ciurca, Chan lecture notes — all agree |
| 10 | recent arXiv (last 5 yr) | "explicit uniformizers totally ramified extensions Q_p" | yes | arXiv 1912.01656 (2020): `(1−ζ_p)/(roots of p)` uniformizer, `v = 1/(p^n(p−1))` | Confirms the *sharp* valuation; the project lemma uses only the sign. |

**Protocol pass check.** WebSearch ran ≥3 distinct queries at different
generality levels (specific valuation #1, uniformizer/general #2, aliases
#3). ChatGPT MCP unavailable → substituted by extra WebSearch + textbook
fetches and recorded n/a-with-substitution. Local refs checked (absent). nLab
checked. Stacks / nCatLab / MathOverflow / arXiv each checked or recorded n/a
with reason. Protocol satisfied.

### Literature summary (Phase 3)

Concept identified as: **"`1 − ζ` is a uniformizer of the totally ramified
cyclotomic extension `ℚ_p(ζ_{p^n})/ℚ_p`"** (equivalently: a primitive `p^n`-th
root of unity is `≡ 1` mod the maximal ideal). Synonyms in the literature:
"`ζ−1` generates the prime above `p`", "`ζ−1` topologically nilpotent",
"`v_p(ζ−1) > 0`".

Sources agree on the standard form: **yes**, unanimously. Washington, Neukirch,
Serre (*Local Fields*), Coates–Sujatha, and every lecture-note treatment state
it identically. The *sharp* form gives the exact valuation
`v_p(ζ−1) = 1/(p^{n−1}(p−1))`.

Most general standard form: the qualitative statement `‖ζ−1‖ < 1` holds in
**any field complete (or not) with a nonarchimedean absolute value extending
the `p`-adic absolute value of `ℚ`** — i.e., residue characteristic `p`. No
completeness, no algebra structure, and no Galois/ramification hypotheses are
needed for the *inequality* (those are needed only for the exact-valuation /
"uniformizer" refinement). The single arithmetic input is `‖(p:L)‖ < 1`.

Generality dimensions where the literature varies:
- **What is asserted**: qualitative `v(ζ−1) > 0` (this lemma) ⊂ "is a uniformizer" ⊂ "`v_p(ζ−1) = 1/φ(p^n)`". Mathlib should have the qualitative inequality (broadest hypotheses) and, separately, the sharp valuation (needs ramification API).
- **Ambient field**: stated for `ℚ_p(ζ)` in textbooks, but the inequality holds for any nonarchimedean field of residue char `p` containing `ζ`. The project already targets this broader class — good — but ties it to `ℚ_p`-algebra structure it does not really need.

Disagreement with the literature: **none.** The Lean statement is a correct,
slightly-under-general specialisation of the standard fact.

---

## Generality analysis — `IsPrimitiveRoot.norm_sub_one_lt` (Phase 4)

Literature-standard form (from Phase 3): `‖ζ−1‖ < 1` for a primitive `p^n`-th
root of unity (`n≥1`) in **any nonarchimedean normed field with `‖(p:L)‖<1`**.

### 4a. Generality status table

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `[NormedAlgebra ℚ_[p] L]` | `L` is a normed `ℚ_p`-algebra | not needed for the inequality | **yes** | Used *only* to derive `‖(p:L)‖<1` via the prior lemma `norm_natCast_self_lt_one`. Replace by a direct hypothesis `(hp1 : ‖(p:L)‖ < 1)`. The `ℚ_p`-algebra scaffolding (and the implicit `CharZero`) then disappears. |
| 2 | `[CompleteSpace L]` | complete | not needed | already dropped | The source has `omit [CompleteSpace L] in` — good, the lemma is already stated without completeness. |
| 3 | `[IsUltrametricDist L]` | ultrametric norm | ultrametric (essential) | **NO** | The proof's core step is `exists_norm_finsetSum_le_of_nonempty` (the ultrametric "sum is dominated by one term"). Archimedean fields fail outright (a primitive `p^n` root in ℂ has `‖ζ−1‖` up to 2). Cannot weaken. |
| 4 | `{ζ : L}`, `hζ : IsPrimitiveRoot ζ (p^n)` | primitive `p^n`-th root | same | NO | This is the hypothesis cluster the literature uses. Primitivity is needed (a non-primitive `p^n`-root could be `1`). `p`-power order is essential — for a prime-to-`p` root `‖ζ−1‖ = 1` (this is the project's *complementary* lemma `norm_pow_sub_one_eq_one`, W3). |
| 5 | `(hn : 1 ≤ n)` | `n ≥ 1` | `n ≥ 1` (so `ζ ≠ 1`) | NO | At `n=0`, `ζ=1`, `‖ζ−1‖=0<1` still holds but the statement is vacuous/degenerate; the `n≥1` matches the literature's "`ζ` a genuine `p^n`-th root". Keep. |

### 4b. Generality verdict

The current form is: **STRICTLY NARROWER THAN STANDARD** (one substantive axis: row 1).
Number of weakening opportunities found: **1** (the `ℚ_p`-algebra → `‖(p:L)‖<1` swap; row 2 is already done).

Proposed restatement (literature-standard generality):

```lean
theorem IsPrimitiveRoot.norm_sub_one_lt
    {L : Type*} [NormedField L] [IsUltrametricDist L]
    {p : ℕ} [Fact p.Prime] (hp1 : ‖(p : L)‖ < 1)
    {ζ : L} {n : ℕ} (hζ : IsPrimitiveRoot ζ (p ^ n)) (hn : 1 ≤ n) :
    ‖ζ - 1‖ < 1 := by
  sorry  -- same binomial / dvd_choose_pow / ultrametric proof; replace the final
         -- `norm_natCast_self_lt_one` step by the hypothesis `hp1`
```

Cost of restatement: **CHEAP** — purely mechanical. The proof body is unchanged
except its last two lines: instead of deriving `‖p‖<1` from the `ℚ_p`-algebra,
take it as `hp1`. Every internal call site in the project currently supplies a
`ℚ_p`-algebra `L`, so each can pass `norm_natCast_self_lt_one` (or the existing
project lemma) explicitly — a one-token change per site.

(Note: `[Fact p.Prime]` is still needed for `dvd_choose_pow`. `p` could in
principle be any element with `‖p‖<1` and `p` prime in the residue field, but
the literature and mathlib both index this by the rational prime `p`, so
keeping `p : ℕ` `[Fact p.Prime]` is the idiomatic choice.)

### 4c. Modern-idiom check — Bourbaki 2.0 (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|---|----------|----------|------------------------|----------------------------------|
| 1 | Could "let `L` be a `ℚ_p`-algebra" preambles become typeclasses/instances? | partly — already a typeclass, but it's the *wrong* one | Drop `[NormedAlgebra ℚ_[p] L]`; add explicit `(hp1 : ‖(p:L)‖<1)` (an arithmetic hypothesis, not a structure). | Applies to any nonarchimedean field of residue char `p`, e.g. `ℂ_p`, finite extensions of `ℚ_p`, completions — none forced through `ℚ_p`-algebra plumbing. |
| 2 | Sequences/metric where filters/topological would generalise? | no | — | The conclusion `‖ζ−1‖<1` is already the metric form; the topological refactor is the *separate* "topologically nilpotent" statement (project's `tendsto_pow_sub_one`, W2'), which mathlib's `AddChar.lean` already consumes. |
| 3 | Construct an object where a universal-property class would characterise it? | no | — | It is an inequality, not a construction. |
| 4 | Set-with-closure-predicate where a bundled substructure would compose? | no | — | No substructure here (that is `integerRing`, a different decl). |
| 5 | Vector-space/metric/field-specific that mathlib's hierarchy weakens to modules/(semi)ring? | yes (mild) | The `NormedField` could in principle weaken to a normed division ring / normed ring with `‖·‖` strictly multiplicative, but primitivity of a root of unity needs a domain; `NormedField` is the right home. | Marginal; not worth chasing — `NormedField` is the standard home for valuation-theoretic root-of-unity facts. |
| 6 | 1-categorical with a higher-categorical generalisation? | no | — | Not categorical. |
| 7 | Concrete index (ℕ/ℤ/ℝ) that generalises to additive groups/monoids/ordered structures? | no | — | The index `p^n` is intrinsic (the order of the root); generalising the *order* is exactly the complementary `p∤D` lemma, a different theorem, not a generalisation of this one. |

**Modern-idiom verdict (4c):** Modern idiom available: **yes (mild, == the row-1
weakening).** The real improvement is row 1: replacing the `ℚ_p`-algebra
hypothesis with the bare `‖(p:L)‖<1` is the *Bourbaki-2.0* move — it states the
lemma at the level of generality where the proof actually lives (a
nonarchimedean field whose residue characteristic is `p`), rather than bolting
on `ℚ_p`-algebra structure that exists only to manufacture `‖p‖<1`.
- Cost: **CHEAP**.
- Mathlib downstream this enables: the lemma becomes directly usable for `ℂ_p`,
  for `IsLocalRing`/`Valued`-style nonarchimedean fields, and composes with
  `tendsto_pow_atTop_nhds_zero_iff_norm_lt_one` → `IsTopologicallyNilpotent`
  → `PadicInt.addChar_of_value_at_one` **without** requiring the target field to
  be presented as a `ℚ_p`-algebra.
- Real mathematical improvement (not just cosmetic): yes — it removes a spurious
  structural hypothesis, widening the lemma to its true domain of validity.

---

## Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem`. No definitional equalities or
typeclass-search paths introduced. Skipped.

---

## Mathlib search-status: `IsPrimitiveRoot.norm_sub_one_lt` (Phase 5)

Five-method search (`references/mathlib-search.md`). Searched BOTH the user's
form and the literature-standard (more general) form.

[A] Lean-Finder       — **n/a**: Lean-Finder MCP/HF space not reachable from this environment. Compensated by exhaustive grep (D) + Loogle web (B) + name-pattern (E).
[B] Loogle (web)      `IsPrimitiveRoot → ‖_ - 1‖ < 1` via `loogle.lean-lang.org/json` — **no hits** (endpoint returned a parse error on the bare query; the underlying `Mathlib` index has no `IsPrimitiveRoot`-indexed `‖·-1‖<1` lemma, confirmed by D/E below).
[C] LeanSearch        — **n/a**: LeanSearch MCP not configured. Natural-language intent ("primitive p-power root of unity has norm of zeta minus one less than one") covered by the WebSearch literature channels + source grep.
[D] Grep mathlib src  Terms: `norm_sub_one`, `‖.* - 1‖ < 1`, `sub_one_lt`, `IsPrimitiveRoot.*‖`, `rootsOfUnity.*norm`, `IsOfFinOrder.*norm`, `tendsto_pow_atTop_nhds_zero_of_norm_lt_one`, `dvd_choose_pow`, `prod_one_sub_pow_eq_order` — **decisive findings below**.
[E] Name pattern      `lean_local_search` unavailable; substituted grep for `theorem .*IsPrimitiveRoot` / `lemma .*IsPrimitiveRoot` in `Analysis/` and `NumberTheory/Padics/` — **no metric-norm root-of-unity lemma**.

**Key mathlib findings (the load-bearing part):**

1. `IsPrimitiveRoot.norm_sub_one_of_prime_ne_two`, `…_two`, `…_eq_prime_pow_of_ne_zero`,
   `IsCyclotomicExtension.norm_zeta_sub_one_of_isPrimePow`
   (`Mathlib/NumberTheory/Cyclotomic/PrimitiveRoots.lean:457,492,505,538`):
   these are about the **algebraic field norm** `Algebra.norm K (ζ−1) = p` (or
   `2`, or `n.minFac`), **NOT** the metric/p-adic absolute value `‖ζ−1‖`. Same
   namespace (`IsPrimitiveRoot`), confusingly-similar names, **different
   mathematical object** (Galois-theoretic norm vs. valuation). They do not
   imply `‖ζ−1‖<1` without a separate ramification argument.
2. `IsOfFinOrder.norm_eq_one` (`Mathlib/Analysis/Normed/Ring/Finite.lean:30`):
   a root of unity has `‖ζ‖ = 1`. Combined with the ultrametric inequality this
   gives only `‖ζ−1‖ ≤ max(‖ζ‖,1) = 1` — the **non-strict** bound. The strict
   `< 1` is exactly the content that this lemma adds and that mathlib lacks.
3. `Mathlib/NumberTheory/Padics/AddChar.lean` (David Loeffler, 2025): the
   **consumer** side. Its module docstring (line 21) explicitly references
   `‖κ 1 − 1‖ < 1`; `continuousAddCharEquiv_of_norm_mul` builds a continuous
   additive character of `ℤ_p` from any `r` with `‖r‖<1`. Mathlib has the
   machinery that *uses* `‖ζ−1‖<1` (for `r = ζ−1`) but **does not contain the
   root-of-unity supply lemma**. This is the precise gap.
4. Building blocks all present: `Nat.Prime.dvd_choose_pow`
   (`Data/Nat/Multiplicity.lean:260`), `exists_norm_finsetSum_le_of_nonempty`
   (`Analysis/Normed/Group/Ultra.lean:273`),
   `tendsto_pow_atTop_nhds_zero_of_norm_lt_one`
   (`Analysis/SpecificLimits/Normed.lean:221`).

**Concluded:** *not in mathlib* (all available methods exhausted, plus the
literature-standard form). Mathlib has the algebraic-norm analogue (different
object), the `≤1` ultrametric bound (too weak), and the downstream consumer
(`AddChar.lean`) — but **no `‖ζ−1‖<1` lemma for `p`-power roots of unity**.

---

## Call sites — `IsPrimitiveRoot.norm_sub_one_lt` (Phase 6.0)

Internal use count: **K = 9** distinct call sites (excluding the declaring file
and its module-docstring mention).
External-to-file callers: **6 distinct files** within the project.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| `PadicLFunctions/ValuesAtOne.lean:872`  | `(IsPrimitiveRoot (ξ ^ (j:ℕ)) (p ^ 1)).norm_sub_one_lt (p := p) le_rfl` |
| `PadicLFunctions/ValuesAtOne.lean:1374` | `… .norm_sub_one_lt (p := p) le_rfl` |
| `PadicLFunctions/ResidueZeta.lean:979`  | `… .norm_sub_one_lt (p := p) le_rfl` |
| `PadicLFunctions/ResidueZeta.lean:1338` | `… .norm_sub_one_lt (p := p) le_rfl` |
| `PadicLFunctions/ResidueZeta.lean:1498` | `… .norm_sub_one_lt (p := p) le_rfl` |
| `PadicLFunctions/MeasureR/FormalPsi.lean:1097` | `exact hprim.norm_sub_one_lt (p := p) le_rfl` |
| `PadicLFunctions/Coleman/Tower.lean:320` | `(zetaSys_primitiveRoot p n).norm_sub_one_lt hn` |
| `PadicLFunctions/Interpolation/Twist.lean:162` | `exact hprim.norm_sub_one_lt hj1` |
| `PadicLFunctions/Coefficients.lean:203` | `tendsto_pow_atTop_nhds_zero_of_norm_lt_one (hζ.norm_sub_one_lt hn)` (the W2' wrapper `tendsto_pow_sub_one`, in-file) |

Inline-derivation grep (was the equivalent re-derived elsewhere without using
this lemma?):
- **(none)** — every place needing `‖ζ−1‖<1` for a `p`-power root calls this
  lemma. `ResidueZeta.lean` re-derives `‖·−1‖<1` for *products* and for
  *prime-to-`p`* roots (lines 1266–1316), but those are genuinely different
  facts (the W3 family), not re-derivations of this one.

**Composability signal (per the Phase-6 table):** `K = 9` internal uses across
6 files, **no inline re-derivation** ⇒ "Real API; consumers depend on it" ⇒
**YES-\* bucket**. This is a heavily-reused load-bearing lemma, the strongest
possible call-site signal.

### Composition check (Phase 6)

Can `IsPrimitiveRoot.norm_sub_one_lt` be derived from mathlib in ≤3 chained calls?

Attempt 1: `IsOfFinOrder.norm_eq_one` + ultrametric `norm_sub_le_max` /
`norm_add_le_max`.
- Mathlib decls used: `IsPrimitiveRoot.isOfFinOrder`, `IsOfFinOrder.norm_eq_one`, `IsUltrametricDist.norm_add_le_max`.
- Result: **fails** — yields only `‖ζ−1‖ ≤ max(‖ζ‖, ‖1‖) = 1`, the **non-strict** bound. The strict `< 1` is unreachable this way (and is genuinely false without the `p`-power hypothesis).

Attempt 2: via the algebraic-norm lemma `IsPrimitiveRoot.norm_sub_one_of_prime_ne_two` (`Algebra.norm K (ζ−1) = p`) + "small algebraic norm ⇒ small p-adic norm".
- Mathlib decls used: `IsPrimitiveRoot.norm_sub_one_of_prime_ne_two` (+ a place-norm/ramification bridge).
- Result: **fails as a composition** — requires `[IsCyclotomicExtension]`, `Irreducible (cyclotomic …)`, the `p ≠ 2` split, AND a non-existent "algebraic norm `p` ⇒ `‖·‖<1`" bridge lemma. This is a multi-lemma argument with hypotheses the project does not have (the project works over an abstract nonarchimedean `L`, not a cyclotomic extension of `ℚ`), not a ≤3-call composition.

Attempt 3: the actual proof — binomial expansion + `dvd_choose_pow` +
`exists_norm_finsetSum_le_of_nonempty` + the contradiction assembly.
- This is ~40 lines with `by_contra`, a `calc`, `nlinarith`/`positivity` glue. By the Phase-6 heuristics ("multiple `have`s with non-trivial reasoning", "requires `calc`/`nlinarith`") this is a **proof, not a composition**.

Conclusion: **NOT-COMPOSABLE.** No ≤3 mathlib-call route exists; the only short
route (`IsOfFinOrder.norm_eq_one`) gives the wrong (non-strict) bound.

---

## Verdict: `IsPrimitiveRoot.norm_sub_one_lt`

**Category:** `YES-but-generalise-first`

**Evidence:**
- Literature search (Phase 3): classical and unanimous — "`1−ζ` is a uniformizer of `ℚ_p(ζ_{p^n})/ℚ_p`", `v_p(ζ−1) = 1/(p^{n−1}(p−1)) > 0` ⇒ `‖ζ−1‖<1` (Washington, Neukirch, Coates–Sujatha, KConrad, arXiv 1912.01656). The qualitative inequality holds for any nonarchimedean field of residue char `p`.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — one CHEAP weakening axis (drop `[NormedAlgebra ℚ_[p] L]`, take `‖(p:L)‖<1` as a hypothesis). Phase 4c confirms this is the real Bourbaki-2.0 move, not cosmetic.
- Mathlib search (Phase 5): **not in mathlib**. Mathlib has the *algebraic-norm* namesakes (different object), the `≤1` ultrametric bound (too weak via `IsOfFinOrder.norm_eq_one`), and the downstream *consumer* `PadicInt.AddChar` — but not this supply lemma.
- Composition check (Phase 6): **NOT-COMPOSABLE** (K=9 reuse, no inline re-derivation; no ≤3-call route).

**Rationale.**
The statement is genuinely missing from mathlib and is a textbook fact with
broad reuse. The decisive evidence is the asymmetry in `AddChar.lean`: David
Loeffler's 2025 file builds the bijection {continuous additive characters of
`ℤ_p`} ≃ {`r` : `‖r‖<1`} and even quotes `‖κ 1 − 1‖<1` in its docstring — yet
the canonical *source* of such an `r`, namely `r = ζ−1` for a primitive `p^n`
root of unity (the case that gives the standard nontrivial characters
`x ↦ ζ^x`), is not in mathlib. The project's own docstring names exactly this
downstream (`PadicInt.addChar_of_value_at_one`). So the gap is concrete and
named, not "searched and didn't find it". The lemma also composes forward with
`tendsto_pow_atTop_nhds_zero_iff_norm_lt_one` and `IsTopologicallyNilpotent`,
and the project already uses it 9 times across 6 files.

It lands in **YES-but-generalise-first** rather than YES-add-as-is because
Phase 4b found the current hypotheses STRICTLY NARROWER than the literature
form and Phase 4c confirmed a real (CHEAP) generalisation: the
`[NormedAlgebra ℚ_[p] L]` typeclass is present only to manufacture `‖(p:L)‖<1`
via the prior lemma `norm_natCast_self_lt_one`; replacing it by a bare
`(hp1 : ‖(p:L)‖<1)` hypothesis states the lemma at the level where its proof
actually lives — any ultrametric normed field of residue characteristic `p`
(covering `ℂ_p`, finite extensions of `ℚ_p`, and `Valued`-style fields without
forcing a `ℚ_p`-algebra presentation). Per the verdict gate, the fact that the
generalisation is CHEAP does not matter for bucket selection; STRICTLY NARROWER
⇒ this bucket.

**Reason for the generalisation:**
- LITERATURE-WEAKENING: Phase 4b — current `[NormedAlgebra ℚ_[p] L]` is strictly stronger than the literature requirement "nonarchimedean field with `‖p‖<1`".
- MODERN-IDIOM (Bourbaki 2.0): Phase 4c — replace structural plumbing with the bare arithmetic hypothesis the proof uses.

**Proposed restatement:**
```lean
theorem IsPrimitiveRoot.norm_sub_one_lt
    {L : Type*} [NormedField L] [IsUltrametricDist L]
    {p : ℕ} [Fact p.Prime] (hp1 : ‖(p : L)‖ < 1)
    {ζ : L} {n : ℕ} (hζ : IsPrimitiveRoot ζ (p ^ n)) (hn : 1 ≤ n) :
    ‖ζ - 1‖ < 1 := by
  sorry  -- existing proof verbatim, except the final
         -- `norm_natCast_self_lt_one` step is replaced by `hp1`
```
Estimated cost of regeneralisation: **CHEAP** (mechanical; only the last two
proof lines change, and each of the 9 call sites passes `‖p‖<1` explicitly —
e.g. via the project's `norm_natCast_self_lt_one`, a one-token change).
Note: EXPENSIVE would not downgrade the verdict; here it is CHEAP anyway.

**Mathlib downstream this enables (the generalised form):**
- Directly usable over `ℂ_p` and any `Valued` / nonarchimedean field of residue
  char `p`, not only `ℚ_p`-algebras.
- Feeds `tendsto_pow_atTop_nhds_zero_iff_norm_lt_one` →
  `IsTopologicallyNilpotent` → `PadicInt.addChar_of_value_at_one` /
  `continuousAddCharEquiv_of_norm_mul` to produce the standard additive
  characters `x ↦ ζ^x` of `ℤ_p` — closing the loop with the *existing* mathlib
  `AddChar.lean`.
- Pairs naturally with the project's complementary `‖ζ^c−1‖=1` lemma (prime-to-`p`
  order) to give the full "roots of unity vs. the maximal ideal" picture mathlib
  currently lacks.

**Naming caveat for the PR (important):** the project name
`IsPrimitiveRoot.norm_sub_one_lt` *collides in spirit* with mathlib's existing
`IsPrimitiveRoot.norm_sub_one_of_prime_ne_two` family, which use `norm` to mean
the **algebraic field norm** `Algebra.norm`, not `‖·‖`. To avoid confusion in
mathlib, prefer a name that disambiguates the metric norm, e.g.
`IsPrimitiveRoot.nnorm_sub_one_lt_one` is not right either; better
`IsPrimitiveRoot.norm_sub_one_lt_one` (note `_one` to read "‖ζ−1‖ < 1") or place
it under a valuation-flavoured name. Flag this for the mathlib reviewer.

**Next action:** run `/generalise IsPrimitiveRoot.norm_sub_one_lt` (it will
tension against both the literature-standard form from Phase 3 and the
modern-idiom form from Phase 4c — i.e. the `‖(p:L)‖<1`-hypothesis restatement),
update the 9 call sites to pass `‖p‖<1` explicitly, then run
`/cleanup Coefficients.lean IsPrimitiveRoot.norm_sub_one_lt` and `/pre-submit`
before opening a `feat(NumberTheory/Padics)` (or `feat(Analysis/Normed)`) PR —
ideally grouped with the topologically-nilpotent corollary `tendsto_pow_sub_one`
(W2') and, if generalised compatibly, the complementary `norm_pow_sub_one_eq_one`
(W3).

---

## Next step

Run `/generalise IsPrimitiveRoot.norm_sub_one_lt` to restate with the bare
`(hp1 : ‖(p:L)‖ < 1)` hypothesis (dropping `[NormedAlgebra ℚ_[p] L]`), tensioning
against the literature-standard "nonarchimedean field of residue char `p`" form;
update the 9 internal call sites to pass `‖p‖<1` explicitly; then `/cleanup` +
`/pre-submit` and open the mathlib PR (grouping the topologically-nilpotent
corollary with it). Address the `norm` (= `‖·‖` vs `Algebra.norm`) naming
collision with mathlib's `IsPrimitiveRoot.norm_sub_one_*` family in the PR.
