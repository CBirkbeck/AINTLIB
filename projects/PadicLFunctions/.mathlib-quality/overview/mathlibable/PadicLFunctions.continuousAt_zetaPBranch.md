# `/mathlibable` report — `PadicLFunctions.continuousAt_zetaPBranch`

**Final verdict: `BORDERLINE-needs-human`** (gated on whether the entire `zetaPBranch` /
Kubota–Leopoldt tower is being upstreamed to mathlib4 — it is currently absent, and this
theorem is only mathlib-worthy *as a corollary of that tower*).

---

### Baseline (Phase 0)

- lake build:               build NOT re-run (stale/slow per task note); reasoned from source. Decl + all dependencies read directly.
- decl `PadicLFunctions.continuousAt_zetaPBranch`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ResidueZeta.lean:401`
- kind:                      theorem
- has sorry:                 no (proof body lines 402–426 contain no `sorry`/`admit`)
- module docstring summary:  "The residue of ζ_p at s = 1 (RJW §7)" — proves RJW Thm 7.1: (i) branch ζ_{p,i} continuous at s=1 for i≠p−1, (ii) ζ_{p,p−1} has a simple pole at s=1 with residue 1−p⁻¹. This theorem is part (i).

---

### Statement (Phase 1)

`PadicLFunctions.continuousAt_zetaPBranch` is a **theorem** stating the following:

> Let `p` be an odd prime. For each residue index `i` with `0 < i < p − 1`, the `i`-th branch
> `ζ_{p,i}` of the Kubota–Leopoldt `p`-adic zeta function is continuous at the point `s = 1`
> (as a function of the `p`-adic variable `s ∈ ℤ_p`, valued in `ℚ_p`).

This is RJW (Rubin–Jones–Washington-style notes, the project's source) **Theorem 7.1(i)**. In the
standard analytic-number-theory picture, the Kubota–Leopoldt `p`-adic `L`-function decomposes into
`p − 1` separate functions `ζ_{p,1}, …, ζ_{p,p−1}` on `ℤ_p`, one per residue class mod `p − 1`; all
of them are `p`-adic analytic *except* `ζ_{p,p−1}`, which has a simple pole at `s = 1`. The theorem
captures the "analytic ⇒ in particular continuous at `s = 1`" half of this for the non-exceptional
branches. (The docstring notes the function is in fact continuous everywhere on ℤ_p, but the
theorem states only the source's pointwise claim at `s = 1`.)

Variables / typeclasses involved (Lean side):
- `(p : ℕ) [hp : Fact p.Prime]` — the prime (section variable).
- `(hp2 : p ≠ 2)` — oddness; needed because the topological generator construction and the sharp
  Teichmüller-norm argument fail at `p = 2`.

Hypotheses (Lean side):
- `{i : ℕ}` — the branch index (residue class mod `p − 1`).
- `(hi0 : 0 < i)` — excludes `i = 0`.
- `(hi : i < p − 1)` — excludes the exceptional branch `i = p − 1` (which has the pole).

Conclusion (math): the branch function `ζ_{p,i} : ℤ_p → ℚ_p` is continuous at `s = 1`.

Conclusion (Lean): `ContinuousAt (zetaPBranch p hp2 i) 1`.

Where `zetaPBranch p hp2 i s = (⟨branchChar p i (1−s) u⟩_{ℚ_p} − 1)⁻¹ · ⟨zetaNum p m (branchChar p i (1−s))⟩_{ℚ_p}`
(`Branches.lean:557`) — RJW's "Eqtmp2" quotient: a denominator `⟨u⟩^{1−s}ω^i − 1` and a numerator
that is a pseudo-measure pairing (`zetaNum`) against the branch character, both evaluated at the
canonical topological generator `u` (with index `m`) from `exists_nat_topological_generator`.

---

### Size classification (Phase 2a)

Verdict: **SMALL** (but adjacent to a BIG object).
Reason: It is *not* itself a new structure or a named "person/place" theorem — it is a regularity
(continuity) statement about an already-defined object `zetaPBranch`. However, the *object* it is
about (`zetaPBranch`, the Kubota–Leopoldt `p`-adic zeta function) is a BIG, named, project-main-result
object. The continuity theorem is one of the named results (RJW Thm 7.1) of the `ResidueZeta` module,
so it is a "supporting main result", not a throwaway helper.

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Body line count: ~24 substantive lines (lines 403–426: `classical`, `obtain`, two `set`s, a
multi-line `have hden_cont`, a `have hden_ne`, an `unfold`, and the final `.inv₀ … .mul …` assembly).
One-liner verdict: **n/a — kind is `theorem`, not `def`.** Section skipped.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                           | Query                                                                                              | Hit? | Standard form found | Notes |
|----|-----------------------------------|----------------------------------------------------------------------------------------------------|------|---------------------|-------|
| 1  | WebSearch (specific form)         | "Kubota-Leopoldt p-adic L-function continuity analytic in s p-adic variable"                       | yes  | `L_p(s,χ)` is *the unique continuous function* of `s ∈ ℤ_p`, analytic on a disc; decomposes into `p−1` branches by residue class mod `p−1` | HandWiki "p-adic L-function"; arXiv 2309.15692; Washington |
| 2  | WebSearch (general form)          | "p-adic zeta function continuous Iwasawa function ring power series Mahler expansion"               | yes  | Iwasawa algebra `O[[X]] ≅` continuous functions on ℤ_p via Mahler/Amice transform; `|aᵢ·i!|→0 ⇒ continuous` | de Shalit "Mahler bases"; JTNB; the general "continuity of p-adic interpolated functions" framework |
| 3  | WebSearch (named-after / aliases) | "p-adic L-function continuous branch residue class mod p-1 not analytic at i=p-1 pole"             | yes  | exactly: "`p−1` different analytic functions `ζ_{p,1},…,ζ_{p,p−1}` on `Z_p`"; `ζ_{p,p−1}` has the simple pole at `s=1` with residue 1 | Warwick (C. Williams) notes; arXiv 2309.15692 — **verbatim match to RJW Thm 7.1 split** |
| 4  | ChatGPT MCP                       | (would ask: standard form + generality + historical evolution of p-adic L-function continuity)     | n/a  | —                   | **MCP not configured in this session** (a `chatgpt-math` server dir exists under `~/.claude/mcp-servers/` but no ChatGPT tool is exposed to this agent). Recorded n/a; compensated by 8 other channels incl. 6 WebSearch queries. |
| 5  | Local references                  | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/`            | n/a  | —                   | neither directory exists in this checkout — recorded n/a per protocol |
| 6  | nLab                              | "p-adic L-function" continuity / Mahler basis                                                      | partial | nLab + Wikipedia "Mahler's theorem": continuous p-adic functions ↔ Mahler series; the p-adic analytic / continuity framework | nLab has the Mahler/Amice abstract continuity infrastructure but no `ζ_{p,i}`-branch-specific page |
| 7  | nCatLab (categorical)             | —                                                                                                   | n/a  | —                   | n/a — not a categorical concept; it is a pointwise analytic regularity statement |
| 8  | Stacks Project                    | —                                                                                                   | n/a  | —                   | n/a — not an algebraic-geometry / scheme-theoretic concept |
| 9  | MathOverflow / Math.StackExchange | folded into the WebSearch queries (#1–3); analytic-vs-continuous and the `p−1`-branch decomposition | yes  | same `p−1`-branch picture; "not p-adic analytic but comes from `p−1` analytic functions, one per residue class mod `p−1`" | confirms the *per-branch* statement is the standard formulation |
| 10 | recent arXiv (last 5 yrs)         | "p-adic L-function formalization Lean number theory zeta Iwasawa"                                   | yes  | **arXiv 2302.14491** (Narayanan): Kubota–Leopoldt p-adic L-functions formalized in **Lean 3 / mathlib 3** — "never been done before in any theorem prover"; **never ported to mathlib4** | Castillo ALGANT thesis + arXiv 2201.08870 (sum expressions) corroborate the classical object |

The protocol passes:
- WebSearch ran **6** distinct queries (≥3 required) at three generality levels: specific (#1), most-general/Mahler-abstract (#2), and named-aliases/branch-decomposition (#3), plus #10 formalization-status and two corroboration queries.
- ChatGPT MCP: recorded **n/a** with reason (not configured in this session) — compensated by the extra WebSearch breadth.
- Local references: checked, recorded n/a (dir absent).
- nLab: checked (Mahler/Amice continuity infrastructure present; no branch-specific page).
- Stacks / nCatLab / MathOverflow / arXiv: each checked or n/a-with-reason.

### Literature summary (Phase 3)

Concept identified as: **the `i`-th branch `ζ_{p,i}` of the Kubota–Leopoldt `p`-adic `L`-function / `p`-adic Riemann zeta function, and its analyticity (⇒ continuity) on `ℤ_p` away from the exceptional branch.**

Sources agree on the standard form: **yes.** Every source (Washington's *Introduction to Cyclotomic
Fields*, the Warwick and arXiv 2309.15692 intro notes, HandWiki) gives the identical picture: the
KL `p`-adic `L`-function is *the unique continuous* function of `s ∈ ℤ_p` interpolating the special
values; it is **not** globally `p`-adic analytic but is built from `p − 1` analytic functions
`ζ_{p,1}, …, ζ_{p,p−1}`, one per residue class mod `p − 1`; `ζ_{p,p−1}` has a simple pole at `s = 1`
(residue `1`, or `1 − p⁻¹` in the `(1−p^{−s})ζ` normalisation), and the *other* branches are analytic
(hence continuous) everywhere. **The theorem's statement (continuity of `ζ_{p,i}` at `s=1` for
`0 < i < p−1`) is exactly the non-exceptional half of this canonical decomposition.**

Most general standard form: each branch `ζ_{p,i}` is **`p`-adic analytic** on `ℤ_p` (a power series
converging on a disc), not merely continuous, and indeed continuous/analytic at *every* `s`, not only
`s = 1`. So the literature-standard regularity is strictly *stronger* (analytic, everywhere) than the
Lean statement (continuous, at one point).

Generality dimensions where the literature varies:
- **Regularity**: continuity (weakest) → continuity everywhere → `p`-adic analyticity (strongest, the standard claim).
- **Domain locality**: at `s = 1` (the Lean form) → on all of `ℤ_p`.
- **Coefficient field**: `ℚ_p` (Lean) → `ℂ_p` / extensions (general, used in the project's mass-computation route via `ℚ_p(μ_p)`).

Disagreement with the literature: **none on content.** The literature uses "analytic on ℤ_p"; the
Lean statement uses the strictly weaker "continuous at `s = 1`". The docstring openly acknowledges
this: *"indeed everywhere, but we state the source's claim."* So the Lean form is a deliberate
specialisation of the standard form, matching the source text (RJW) rather than the maximal regularity.

---

### Generality analysis — `PadicLFunctions.continuousAt_zetaPBranch`

Literature-standard form (from Phase 3): each branch `ζ_{p,i}` is **`p`-adic analytic on all of
`ℤ_p`** for `i ≠ p − 1`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | conclusion `ContinuousAt _ 1` | continuity at the single point `s = 1` | analytic (or at least continuous) **everywhere** on `ℤ_p` | conclusion can be **strengthened**, not weakened | The proof already shows global continuity: `hden_cont` and `continuous_zetaNum_branch_pairing` are `Continuous` (everywhere), and `branch_denom_ne_zero` is proved *for all `s`* (docstring: "strengthened from `s = 1` to all `s`"). Only `hden_ne` is instantiated at `s=1`, but the global non-vanishing is in hand. So `Continuous (zetaPBranch p hp2 i)` is essentially free. |
| 2 | `(hp2 : p ≠ 2)` | odd prime | odd prime (standard) | NO | Standard hypothesis; the `p=2` branch structure differs (the group `1+pℤ_p` is not pro-`p`-cyclic the same way) and the sharp Teichmüller-norm step needs `p≠2`. Matches the literature. |
| 3 | `(hi : i < p − 1)` | exclude exceptional branch | exclude `i = p−1` (standard) | NO | This is the genuine mathematical boundary — `i = p−1` is the pole branch (RJW Thm 7.1(ii) / `tendsto_sub_one_mul_zetaPBranch`). Cannot be weakened; it is correct. |
| 4 | target field `ℚ_p` | `ζ_{p,i} : ℤ_p → ℚ_p` | could be `ℂ_p` / any complete extension | yes (but not the standard target) | The values are genuinely in `ℚ_p`; widening the codomain is not the literature's move for the *function itself*. Not a weakening of this statement. |

This is a literature-grounded generality pass (not a mere typeclass walk): the target form comes from
the Washington/arXiv standard decomposition, which says **analytic everywhere**.

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (continuity *at a point* vs. analyticity
*everywhere*).
Number of strengthening opportunities found: 1 (conclusion: point → global; continuous → analytic).
Proposed restatement (the cheap, immediately-supported half — global continuity):

```lean
theorem continuous_zetaPBranch (hp2 : p ≠ 2) {i : ℕ} (hi0 : 0 < i) (hi : i < p - 1) :
    Continuous (zetaPBranch p hp2 i) := by
  -- hden_cont : Continuous (denominator)         -- already proved (everywhere)
  -- hden_global_ne : ∀ s, denominator s ≠ 0      -- branch_denom_ne_zero is already ∀ s
  -- continuous_zetaNum_branch_pairing            -- already Continuous (everywhere)
  sorry  -- mechanical: replace .continuousAt/.inv₀ at a point with the global Continuous.inv₀ + .mul
```

Cost of restatement to **global continuity**: **CHEAP — mechanical.** Every ingredient is already a
global `Continuous`/`∀ s` statement; only the final assembly currently specialises to `s=1`.

Cost of restatement to **`p`-adic analyticity** (the *full* literature standard): **EXPENSIVE** — needs
the power-series / locally-analytic API for `onePAdicPow` and the pairing, which the project has not
built and mathlib4 does not have. (Per the philosophy doc, EXPENSIVE is not a downgrade — but it does
mean "analytic" is not a cheap restatement here.)

→ STRICTLY NARROWER ⇒ Phase 7 weighs `YES-but-generalise-first` prominently. Tempered below by the
fact that the whole *object* is missing from mathlib4 (Phase 5), which dominates.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preambles → typeclasses/instances? | no | — | The hypotheses are already typeclass-driven (`Fact p.Prime`); no bundled "let" preamble to dissolve. |
| 2 | sequences/metric → filters/topological? | **yes (partly)** | State as `Continuous`/`ContinuousAt` (filter-based — already done) and ideally `AnalyticAt`/`HasFPowerSeriesAt` | The proof already uses `ContinuousAt`/`LipschitzWith` (filter/topological idiom), not sequences — already modern. The genuine modern target is `AnalyticOnNhd`/`AnalyticAt`, but that needs the missing power-series API. |
| 3 | construct object → universal-property class? | no | — | Continuity is a property of a given function, not a construction. |
| 4 | set-with-closure-predicate → bundled substructure? | no | — | No substructure here. |
| 5 | vector-space/metric/field-specific → weaken typeclass? | no | — | `ℤ_p`, `ℚ_p` are the genuine objects; the result is intrinsically about these specific rings. The *internal* lemmas (`continuous_zetaNum_branch_pairing`, `norm_onePAdicPow_sub_one_le`) are already stated over general `[NormedAlgebra ℚ_[p] L] [IsUltrametricDist L]` where possible. |
| 6 | 1-categorical → higher-categorical? | no | — | n/a. |
| 7 | concrete index (ℕ,ℤ,ℝ) → arbitrary group/monoid? | no | — | `i` is genuinely a residue index mod `p−1`; `s` ranges over `ℤ_p`. No spurious concreteness. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes, but only the "everywhere + analytic" strengthening** (rows 2), which
coincides with the Phase-4b generality target — it is **not** a *different* modern reformulation, just
"prove more". The statement is *already* in the modern filter/`ContinuousAt` idiom.
- Proposed mathlib-idiomatic restatement: `Continuous (zetaPBranch …)` now (CHEAP), `AnalyticOnNhd … (zetaPBranch …)` later (EXPENSIVE).
- Real mathematical improvement: the global/analytic form is what every downstream user wants (it is
  the literature statement) — but this is the **same** strengthening already captured in Phase 4b, not
  an independent Bourbaki-2.0 reorganisation. No "looks cooler in category theory" trap is being
  invoked.

---

### Diamond / defeq risk — `PadicLFunctions.continuousAt_zetaPBranch`

**n/a — declaration kind is `theorem`.** Theorems introduce no definitional equalities or
typeclass-search paths; Phase 4.5 is skipped. (Risk verdict: n/a.)

---

### Mathlib search-status: `PadicLFunctions.continuousAt_zetaPBranch`

[A] Lean-Finder       (web UI / API)                         n/a: programmatic endpoint returned 404 to WebFetch; substituted by the WebSearch "Lean/mathlib4 formalization" queries (#10), which establish the mathlib4 gap directly.
[B] Loogle            `ContinuousAt (fun _ => _⁻¹ * _) _`     no hits relevant — only generic `ContinuousAt.inv₀` / `ContinuousAt.mul` building blocks (see Phase 6); nothing about p-adic L-functions.
[C] LeanSearch        "continuity of p-adic L-function branch" / "Kubota Leopoldt continuous" via web   no hits in mathlib4 — surfaced only the Lean **3** formalization (arXiv 2302.14491), not mathlib4 content.
[D] Grep mathlib src  `grep -rln -i "p-adic l-function|p-adic zeta|kubota|leopoldt|iwasawa|padicZeta|kubotaLeopoldt|zetaNum|branchChar|zetaPBranch" .lake/packages/mathlib/Mathlib`   **no hits** for any p-adic-L-function machinery. The only `iwasawa` hits are `GroupTheory/.../Iwasawa.lean` (Iwasawa's lemma on group actions / simplicity — unrelated). The only relevant `teichmuller` hits are Witt-vector/perfectoid (`RingTheory/Teichmuller.lean`, `WittVector/Teichmuller.lean`), **not** the p-adic-units Teichmüller character `teichmuller p x` used here.
[E] Name pattern      grep for `zetaPBranch`, `branchChar`, `zetaNum`, `padicZeta`, `onePAdicPow`, `exists_nat_topological_generator` across mathlib4   **all project-local; none exist in mathlib4.**

Searched for both:
  - the user's current form (`ContinuousAt (zetaPBranch …) 1`) — absent;
  - the literature-standard form (analyticity of `ζ_{p,i}` on `ℤ_p`, and indeed the *object* `ζ_{p,i}` itself) — **the object is absent from mathlib4 entirely.**

Concluded: **not in mathlib (all methods exhausted, plus the literature-standard form and the
underlying object).** mathlib4 has **no** Kubota–Leopoldt / `p`-adic `L`-function / `p`-adic-zeta
development at all. A Lean **3** formalization exists (Narayanan, arXiv 2302.14491) but was never
ported to mathlib4; this AINTLIB `PadicLFunctions` project is itself the fresh mathlib4 development of
this area. Consequently *every* prerequisite of this theorem — `zetaPBranch`, `branchChar`, `zetaNum`,
`padicZeta`, `onePAdicPow`, `exists_nat_topological_generator`, the `PadicMeasure` pseudo-measure
machinery — is missing upstream.

---

### Call sites — `PadicLFunctions.continuousAt_zetaPBranch`

Internal use count: **0** (`grep -rn "continuousAt_zetaPBranch"` across the whole project returns only
the declaration itself at `ResidueZeta.lean:401`; no other file or line references it).
External-to-file callers: **0 distinct files.**

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none)           | —             |

Inline-derivation grep (was the equivalent re-derived elsewhere?):
  - **(none)** — `tendsto_sub_one_mul_zetaPBranch` (`ResidueZeta.lean:1773`, the Thm 7.1(ii) pole
    counterpart) is the sibling result for `i = p−1`; it does not re-derive this continuity statement.
    The continuity result is genuinely a leaf so far.

**What the call-sites pattern tells us:** `K = 0` internal uses, **no** inline re-derivation
elsewhere. Per the Phase-6.0.1 table this is the "**dead code? brand-new + unused so far?**" row →
**genuinely-new but currently-unconsumed ⇒ BORDERLINE**. This is exactly what one expects of a
just-proved RJW-Thm-7.1(i) leaf in an active dev project: it is a *named source result* (a milestone),
proved for its own sake / to mirror the paper, not yet plumbed into a downstream consumer. It is not
junk (it is a named theorem matching the source's Thm 7.1), but it also has no current API pull.

---

### Composition check (Phase 6)

Can `continuousAt_zetaPBranch` be derived from **mathlib** in ≤3 chained calls? **No.**

Attempt 1 (final assembly only): `(hden_cont.continuousAt.inv₀ hden_ne).mul (continuous_….continuousAt)`
  - Mathlib decls used: `ContinuousAt.inv₀` (`Mathlib/Topology/Algebra/GroupWithZero.lean:120`),
    `ContinuousAt.mul` (`Mathlib/Topology/Algebra/Monoid/Defs.lean:101`), `Continuous.continuousAt`.
  - Result: **succeeds for the last 2 lines ONLY** — but the inputs `hden_cont`, `hden_ne`, and
    `continuous_zetaNum_branch_pairing` are **not** mathlib; they are heavy project-local theorems:
    - `hden_cont` (continuity of the denominator) rests on `PadicInt.continuous_onePAdicPow` and the
      `branchChar` continuity — project-local, ~10 lines.
    - `hden_ne` = `branch_denom_ne_zero` (`ResidueZeta.lean:188`) — a genuine ~30-line ultrametric
      *isosceles* argument (`‖ω^i − 1‖ = 1` beats `‖⟨u⟩^{1−s}−1‖ < 1`), depending on
      `norm_teichmuller_pow_sub_one_eq_one`.
    - `continuous_zetaNum_branch_pairing` (`ResidueZeta.lean:360`) — a ~35-line `1`-Lipschitz proof via
      a `p^m`-congruence sup-norm bound on the pseudo-measure pairing.
  - Notes: the mathlib content is only the trivial 2-call `.inv₀ … .mul …` glue; everything of
    substance is project-specific and itself absent from mathlib.

Attempt 2 (from mathlib's KL machinery): **vacuous** — Phase 5 shows mathlib4 has *no* p-adic
L-function development to compose from.

Conclusion: **NOT-COMPOSABLE** (from mathlib). The result is a thin generic-continuity wrapper over
three deep project-local theorems; the wrapper is mathlib-trivial, but its inputs are not in mathlib at
all. So "compose from mathlib primitives" is impossible: there are no mathlib primitives for this
object.

---

## Verdict: `PadicLFunctions.continuousAt_zetaPBranch`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the `p−1`-branch decomposition `ζ_{p,1},…,ζ_{p,p−1}` with the
  non-exceptional branches analytic and `ζ_{p,p−1}` poled at `s=1` is the **canonical standard form**
  (Washington; arXiv 2309.15692; Warwick notes). The theorem is exactly the non-exceptional, continuity-at-a-point half.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — literature says *analytic
  everywhere*; the global-continuity strengthening is CHEAP and already supported by the existing
  proof ingredients, the analytic strengthening is EXPENSIVE.
- Mathlib search (Phase 5): **not in mathlib4, and neither is the underlying object** — mathlib4 has
  *zero* Kubota–Leopoldt / p-adic-L-function machinery (a Lean 3 formalization exists, unported).
- Composition check (Phase 6): **NOT-COMPOSABLE** from mathlib (no p-adic-L primitives exist upstream;
  the mathlib content is only a 2-call `.inv₀ … .mul …` glue over deep project-local theorems).
- Call sites (Phase 6.0): **K = 0**, no inline re-derivation → genuinely-new-but-unconsumed
  (BORDERLINE row).

**Rationale (why BORDERLINE, not a YES/NO):**

Three independent signals collide and none resolves to a clean bucket on its own:

1. **The object is missing upstream, but so is everything it rests on.** This theorem is *only*
   mathlib-worthy as a corollary of `zetaPBranch` (the KL `p`-adic zeta function) being in mathlib —
   and `zetaPBranch`, together with its entire supporting tower (`branchChar`, `zetaNum`, `padicZeta`,
   the `PadicMeasure` pseudo-measure framework, `exists_nat_topological_generator`, `onePAdicPow`,
   the units-Teichmüller character), is **absent from mathlib4**. So this is not "add a self-contained
   lemma"; it is "the tail end of a large multi-file upstreaming effort". Whether *this* leaf is worth
   assessing for mathlib at all depends on a project/maintainer decision to upstream the KL development
   — a judgment the skill cannot make. (Mathlib's own preference, and the project's `CLAUDE.md` model,
   is to PR the *foundational* objects first; a continuity corollary ships *with or after* its object,
   never before.)

2. **It is strictly narrower than the standard form, and the cheap strengthening is free.** The
   literature statement is "`ζ_{p,i}` is analytic on `ℤ_p`"; this theorem is "continuous at `s=1`".
   The proof already proves *global* continuity (`hden_cont`, `continuous_zetaNum_branch_pairing` are
   `Continuous`; `branch_denom_ne_zero` is `∀ s`), so `Continuous (zetaPBranch …)` is a CHEAP mechanical
   restatement. The docstring itself flags this ("indeed everywhere, but we state the source's claim").
   That pushes toward `YES-but-generalise-first` — but only *conditional on* signal (1) being resolved
   in favour of upstreaming, which the worker cannot assume. If the KL tower is **not** being upstreamed,
   then for mathlib purposes this is a NO-by-irrelevance (it has no upstream object to attach to).

3. **K = 0, unconsumed.** No internal caller, no inline re-derivation. It is a faithful named milestone
   (RJW Thm 7.1(i)) proved to track the paper, not (yet) load-bearing API. That is fully consistent
   with an active producer branch but means there is no composability pull arguing for inclusion *now*.

The skill never silently picks between buckets when the choice hinges on a judgment it cannot ground.
Here the bucket is genuinely contingent: **if** the KL/`p`-adic-L development is being upstreamed to
mathlib4, this theorem is `YES-but-generalise-first` (ship it as global `Continuous … (zetaPBranch …)`,
ideally `AnalyticOnNhd` eventually, *bundled with `zetaPBranch` and its tower*, never standalone); **if
not**, it is out of mathlib scope as a project-internal milestone. That fork is a human call.

**Numbered questions (≤5):**

1. **Is the Kubota–Leopoldt `p`-adic `L`-function development in this `PadicLFunctions` project
   intended to be upstreamed to mathlib4** (i.e. is `zetaPBranch` and its whole supporting tower a
   future mathlib PR target)? If **no**, this theorem is project-internal and out of mathlib scope —
   stop here. If **yes**, proceed to Q2.

2. Given mathlib's "most general form" rule and that the existing proof already yields it cheaply: do
   you want this shipped as the **global** `Continuous (zetaPBranch p hp2 i)` (CHEAP mechanical
   restatement) rather than the point-wise `ContinuousAt … 1`? (Recommended: yes.)

3. Is it worth also targeting the **full literature standard `AnalyticOnNhd`/`AnalyticAt`** form
   (EXPENSIVE — needs locally-analytic power-series API for `onePAdicPow` and the pairing that mathlib4
   lacks), or is global continuity the right grain for the first PR? (This is the generality-vs-cost
   tradeoff that, per the verdict gate, must be a human decision, not a self-resolving downgrade.)

4. The KL development presumably uses a *bundled `ζ_p`-as-a-function* (or pseudo-measure) object. When
   upstreaming, should the mathlib API expose the **per-branch** functions `ζ_{p,i}` (as here) or a
   single `L_p(s,χ)`-style object that specialises to the branches — i.e. which is the canonical mathlib
   spelling? (Affects whether this branch-continuity lemma is even the right statement to upstream.)

5. Should this continuity result be **PR-grouped with `zetaPBranch` and `tendsto_sub_one_mul_zetaPBranch`
   (the Thm 7.1(ii) pole)** as one "regularity of the KL branches" unit, rather than as an isolated
   lemma?

**Next action:** user answers Q1 first. If "not upstreaming" → drop from mathlib consideration (keep as
project milestone). If "upstreaming" → re-run `/mathlibable` after `zetaPBranch` itself has a verdict,
treating *this* as a `YES-but-generalise-first` (restate as global `Continuous`, bundle with the object
and its tower); then run `/generalise continuousAt_zetaPBranch` to confirm the global-continuity (and
possibly `AnalyticAt`) target before any PR.

---

## Next step

User answers Q1 (is the KL `p`-adic-L development being upstreamed to mathlib4?). If no → out of scope.
If yes → re-run `/mathlibable` once `zetaPBranch` has its own verdict; this theorem then resolves to
`YES-but-generalise-first` (ship as global `Continuous (zetaPBranch …)`, bundled with `zetaPBranch` +
its supporting tower), with `/generalise continuousAt_zetaPBranch` as the pre-PR step.
