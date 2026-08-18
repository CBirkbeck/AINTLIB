# `/mathlibable` report — `PadicLFunctions.exists_pPow_pow_inExpBall`

**Final verdict: `NO-composable-from-mathlib` is REJECTED; the verdict is `YES-but-generalise-first`.**

(See Phase 7 for the full reasoning. Headline: mathlib has no p-adic exp/log
nor any "exponential ball" at all, the proof is a genuine ~50-line geometric
contraction argument that does NOT compose from mathlib primitives in ≤3 calls,
so the NO buckets are excluded. The result is real mathlib-grade content, but it
is phrased against the project-local `def InExpBall` and a bundled
`NormedAlgebra ℚ_[p]` ambient, which should be lifted to the standard
`p^{-1/(p-1)}` convergence ball before any PR — hence `YES-but-generalise-first`.)

---

### Baseline (Phase 0)
- lake build:               build not re-run (stale/slow per task instruction); reasoned from source.
- decl `PadicLFunctions.exists_pPow_pow_inExpBall`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ExtLog.lean:129`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  The extended (Iwasawa-branch) p-adic logarithm `extLog` (RJW §6, decomposition W6a); extends `padicLog` to rational-valuation elements via `x^m = p^k·y` with `y` in the exponential ball.

---

### Statement (Phase 1)

`exists_pPow_pow_inExpBall` is a **theorem** stating the following:

Let `L` be a complete ultrametric normed field that is a normed `ℚ_[p]`-algebra
(`p` prime). If `w ∈ L` is a **one-unit**, i.e. `‖w − 1‖ < 1` (the open unit
ball around `1`), then **some `p`-power iterate `w^(p^j)` lands in the open
exponential ball**: there exists `j : ℕ` with `‖w^(p^j) − 1‖^(p−1) < p⁻¹`.

In standard p-adic-analysis notation: the open exponential ball is
`B = { x : ‖x‖ < p^{−1/(p−1)} }` (the domain of convergence of the p-adic
exponential), and the claim is that for any one-unit `u` there is `n` with
`u^{p^n} ∈ 1 + B`, equivalently `|u^{p^n} − 1| < p^{−1/(p−1)}`. (The Lean form
states the equivalent, rpow-free, inequality `‖·‖^{p−1} < p⁻¹` — see the `def
InExpBall` below.) This is the lemma that drives the *extension of the p-adic
logarithm from the small convergence ball to all one-units*: raising a one-unit
to a high enough `p`-power contracts it into the region where `padicLog`
converges and is well-behaved.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the residue characteristic / prime.
- `{L : Type*}`, `[NormedField L]`, `[NormedAlgebra ℚ_[p] L]`,
  `[IsUltrametricDist L]`, `[CompleteSpace L]` — the ambient field. Note: the
  declaration is preceded by `omit [CompleteSpace L]`, so completeness is *not*
  used; the `NormedAlgebra ℚ_[p] L` instance is used only to pin `‖(p : L)‖ = p⁻¹`
  (via `norm_natCast_p`).

Hypotheses (Lean side):
- `(hw : ‖w − 1‖ < 1)` — `w` is a one-unit (lies in the open unit ball around 1).

Conclusion (math): some `p`-power iterate of the one-unit lies in the exponential
ball `1 + B`.

Conclusion (Lean): `∃ j : ℕ, InExpBall p (w ^ p ^ j − 1)`, where
`InExpBall p x := ‖x‖ ^ (p − 1) < (p : ℝ)⁻¹`
(`PadicExp.lean:65`).

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper lemma (labelled "W6a-a4" in the decomposition), one step in the
construction of the extended logarithm `extLog`. It is not a named theorem and
not a stated "Main result" of the project; it is an engine lemma feeding
`extLogDomain_of_integral_norm_one` and the `padicLog_mul_of_norm_lt_one`
extension. (Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is
recorded only for framing.)

### One-line check (Phase 2b)

Body line count: ~50 substantive lines (a full induction + a `Tendsto` geometric-
decay argument + extraction).
One-liner verdict: **n/a** — kind is `theorem`, not `def`. Check skipped.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
|  1 | WebSearch (specific form) | "p-adic logarithm convergence one-units principal units raising to p-th power lands in domain of convergence" | yes | log_p converges on `\|z−1\|_p<1`; isometry between `\|x\|<p^{−1/(p−1)}` (additive) and `1+y, \|y\|<p^{−1/(p−1)}` (mult.); raising to p brings elements into more controlled regions | umontreal Appendix16, arXiv 1904.09850, Wikipedia "p-adic exponential function" |
|  2 | WebSearch (general / radius form) | "p-adic exponential logarithm radius of convergence \|x\|<p^{−1/(p−1)} one-units filtration" | yes | exp_p converges exactly on `\|x\|_p < p^{−1/(p−1)}` (from `limsup \|1/n!\|^{1/n}=p^{1/(p−1)}`); log_p on `\|x−1\|_p<1`; the two are inverse on their domains | planetmath, MIT 18.785 PS10, math.mit.edu/~dav/exp.pdf, World Scientific (Escassut) |
|  3 | WebSearch (named-after / aliases) | "Washington cyclotomic fields … every principal unit some p-power lies in convergence domain log_p / Neukirch one-units U^(n) frobenius" | partial | Washington *Introduction to Cyclotomic Fields* §5.1 and the U_n principal-units filtration in Iwasawa theory; no *named* theorem — it is a standard intermediate lemma | Washington (Google Books), Hida 207a notes, Erickson cyclotomic notes |
|  4 | WebSearch (extension form) | "'p-adic logarithm' extend 'every one-unit' 'raising to' p power 'domain of convergence' exponential lemma" | yes | log_p extends to all of C_p^× by `log(zw)=log z+log w`, `log p = 0`; exp/log inverse on `1+p'·Ga`, radius `R_exp=p^{−1/(p−1)}<1` | confirms the extension mechanism this lemma feeds |
|  5 | ChatGPT MCP | (intended) "standard form + generality + historical evolution of: a one-unit's p-power iterate entering the exp convergence ball" | n/a | MCP server not installed in this environment (`setup-chatgpt` not run); recorded n/a per skill fallback. Compensated by 4 WebSearch queries at distinct generality levels + Wikipedia/notes WebFetch. |
|  6 | Local references | `.mathlib-quality/references/` for "p-adic log / exp ball" | n/a | directory absent (`projects/PadicLFunctions/.mathlib-quality/references/` does not exist; `refs/` not present) — recorded n/a. The module docstring itself cites Washington §5.1 and RJW Thm 6.1(ii). |
|  7 | nLab | "local field", "p-adic exponential" | no (dedicated) | nLab `local+field` is a general overview; no dedicated entry for the p-power-into-convergence-ball lemma. The exp/log convergence radii are folklore there. | ncatlab.org/nlab/show/local+field |
|  8 | nCatLab (categorical) | n/a | n/a | Not a categorical concept — it is a concrete metric/contraction estimate in a non-archimedean field. n/a with reason. |
|  9 | Stacks Project | "p-adic logarithm", "one-units" | n/a | Not an algebraic-geometry / scheme-theoretic concept; Stacks does not cover p-adic analytic exp/log convergence. n/a with reason. |
| 10 | MathOverflow / Math.SE | "(1+x)^p − 1 norm bound p-adic", "one-unit p-power convergence radius" | yes (folklore) | The bound `\|(1+x)^p − 1\| ≤ max(\|x\|^p, p^{−1}\|x\|)` and "p-power maps contract one-units toward 1" are standard folklore answers; no canonical single citation. | recurring in local-fields course notes (Warwick, Nottingham, Harvard theses) |
| 11 | recent arXiv (last 5 yrs) | "image of p-adic logarithm on principal units" | yes (context) | arXiv:1904.09850, arXiv:1907.06437 study the *image* of log_p on principal units U_K — they take exactly this contraction/extension setup as a known starting point | confirms the lemma is assumed-known background, not itself the research object |

The protocol passes: WebSearch ran 4 distinct queries at different generality
levels (specific / radius-general / named-after / extension); ChatGPT MCP recorded
n/a with reason (not installed); local refs recorded n/a with reason (absent);
nLab checked; nCatLab / Stacks / MathOverflow / arXiv each checked or n/a-with-reason.

### Literature summary (Phase 3)

Concept identified as: **the p-power contraction of one-units into the
exponential (convergence) ball** — the mechanism underlying both the
exp/log isometry `B ≅ 1+B` (with `B = {‖x‖ < p^{−1/(p−1)}}`) and the
extension of `log_p` from the convergence ball to all one-units.

Sources agree on the standard form: **yes.** The exp converges exactly on
`‖x‖ < p^{−1/(p−1)}`; the log on `‖x−1‖ < 1`; for any one-unit `u`, `u^{p^n}`
eventually enters the exp ball, and this is how `log_p` is extended to all
one-units with `log_p(p)=0`. This is uniform across Washington §5.1, Koblitz
*p-adic Numbers…*, Neukirch *ANT* II.5, Cassels *Local Fields*, and the
modern course notes / arXiv background.

Most general standard form: for a **complete non-archimedean (ultrametric)
field `K` of residue characteristic `p`** (more generally any complete
ultrametric field over `ℚ_p`), every one-unit `u` (`|u−1| < 1`) satisfies
`u^{p^n} → 1`, and for `n ≫ 0`, `|u^{p^n} − 1| < p^{−1/(p−1)}`. The driving
estimate is `|(1+x)^p − 1| ≤ max(|x|^p, p^{-1}|x|)` for `|x| < 1`, giving
geometric decay with ratio `max(|x|^{p−1}, p^{-1}) < 1`.

Generality dimensions where the literature varies:
  - **Ambient field**: stated for `ℚ_p`, for `C_p`, for finite/algebraic
    extensions `K/ℚ_p`, and for general complete ultrametric fields over `ℚ_p`.
    The *most general* is a complete ultrametric normed field over `ℚ_p` — which
    is essentially the Lean ambient, except the Lean form additionally bundles
    `NormedAlgebra ℚ_[p] L` and (unnecessarily, since it is `omit`-ed)
    `CompleteSpace L`.
  - **Target ball spelled**: literature writes the open ball `‖x‖ < p^{−1/(p−1)}`
    (using `rpow`). The Lean form uses the algebraically-equivalent, rpow-free
    `‖x‖^{p−1} < p⁻¹`, packaged as `def InExpBall`. This is a *formulation*
    choice, not a generality difference.

Disagreement with the literature: **none on content.** The Lean statement is a
faithful special encoding of the standard lemma; the only gaps are (a) it is
phrased against a project-local `def InExpBall` rather than the standard
convergence-ball predicate, and (b) it carries `NormedAlgebra ℚ_[p] L` where the
mathematics needs only the ultrametric structure plus `‖(p:L)‖ ≤ p⁻¹` (or
`< 1`).

---

### Generality analysis — `exists_pPow_pow_inExpBall`

Literature-standard form (from Phase 3): for a complete ultrametric field over
`ℚ_p`, every one-unit `u` has `u^{p^n}` in the exp ball `‖x‖ < p^{−1/(p−1)}`
for `n ≫ 0`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `[NormedAlgebra ℚ_[p] L]` | normed `ℚ_p`-algebra | only needs `‖(p:L)‖ < 1` (in fact `= p⁻¹` or `≤ p⁻¹`) in an ultrametric normed (semi)ring | **yes** | The proof uses the algebra structure *only* through `norm_natCast_p : ‖(p:L)‖ = p⁻¹` and `IsUltrametricDist.norm_natCast_le_one`. It could be stated for any `[NormedRing L] [IsUltrametricDist L]` with a hypothesis `‖(p:L)‖ ≤ p⁻¹` (or for a residue-char-`p` non-archimedean field). The full `NormedAlgebra ℚ_[p]` is stronger than required. |
| 2 | `[CompleteSpace L]` | complete | not needed for this lemma | **yes (already)** | `omit [CompleteSpace L]` is present — completeness is genuinely unused here. (It is needed elsewhere for `padicLog` to converge, not for this contraction.) Mechanical: drop from the signature when isolated. |
| 3 | `[IsUltrametricDist L]` | ultrametric | ultrametric (essential) | **NO** | The whole argument is the strong triangle inequality (`norm_add_le_max`, `norm_sum_le_of_forall_le`) plus `p ∣ (p choose i)`. Archimedean fields have no such contraction. Essential. |
| 4 | conclusion via `def InExpBall` | `‖·‖^{p−1} < p⁻¹` | open ball `‖·‖ < p^{−1/(p−1)}` | reformulation | Same set; the rpow-free encoding is a project convenience. For mathlib the standard `rpow` ball (or a shared `Padic`/non-arch exp-domain predicate) is preferable so it composes with a future p-adic-exp API. |
| 5 | `w` one-unit (`‖w−1‖<1`) | open unit ball | open unit ball (essential) | NO | This is exactly the principal-units hypothesis; cannot be weakened (a non-one-unit need never enter the ball). |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD**
Number of weakening opportunities found: **2** (rows 1 and 2; row 4 is a
reformulation).

Proposed restatement (the maximally-general literature target, sketched):

```lean
-- ambient: a non-archimedean normed field/ring over ℚ_p with ‖(p:L)‖ ≤ p⁻¹,
-- or simply a complete ultrametric field of residue characteristic p.
theorem exists_pPow_pow_inExpBall
    {L : Type*} [NormedField L] [IsUltrametricDist L]
    (hpL : ‖(p : L)‖ ≤ (p : ℝ)⁻¹)        -- replaces [NormedAlgebra ℚ_[p] L]
    {w : L} (hw : ‖w - 1‖ < 1) :
    ∃ j : ℕ, ‖w ^ p ^ j - 1‖ ^ (p - 1) < (p : ℝ)⁻¹ := ...
```

Cost of restatement: **CHEAP–MODERATE.** Dropping `CompleteSpace` is mechanical.
Replacing `NormedAlgebra ℚ_[p] L` by a `‖(p:L)‖ ≤ p⁻¹` hypothesis is mechanical
*for this lemma's two upstream uses* (`norm_natCast_p`, `norm_natCast_le_one`),
but requires a parallel change to the supporting lemmas `mul_mem_expBall`,
`pow_mem_expBall`, `norm_pow_p_sub_one_le` (they live in the same file and share
the ambient). The replacement of `def InExpBall` by the standard convergence-ball
predicate is part of a larger "p-adic exp/log to mathlib" effort (see Phase 4c).

(Cost note: EXPENSIVE is not a downgrade, and this is only CHEAP–MODERATE.)

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|---------------------------------|
|  1 | "let L be a normed ℚ_p-algebra" preamble → typeclass/instance hypotheses instead of bundled? | **yes** | Replace `[NormedAlgebra ℚ_[p] L]` with the genuinely-used `[IsUltrametricDist L]` + `‖(p:L)‖ ≤ p⁻¹`; this is the minimal typeclass surface. | Applies to *any* non-archimedean field of residue char `p` (e.g. `ℤ_[p]`, `ℂ_[p]`, finite extensions), not just `ℚ_p`-algebras. |
|  2 | sequences/metric where filters/topological notions generalise more cleanly? | **partly** | The conclusion `∃ j, …` is the `.exists` of an eventual statement. The modern mathlib idiom is `∀ᶠ j in atTop, InExpBall p (w^(p^j)−1)`, or even `Tendsto (fun j => w^(p^j)) atTop (𝓝[ExpBall] 1)` — and the *cleanest* idiom is to reuse `IsTopologicallyNilpotent (w − 1)`-style API once a non-archimedean exp-ball neighborhood basis exists. | An `∀ᶠ`/`Tendsto` form composes with mathlib's filter API (`Filter.Eventually`, `nhds`), and would let downstream `obtain` any large enough `j`, not just *some* `j`. |
|  3 | constructs an object where a universal-property class would characterise it? | no | — | This is an existence/contraction estimate, not an object construction. |
|  4 | set-with-closure-predicate where a bundled-substructure type would compose? | no | — | `InExpBall`/one-units are open balls (not a substructure to bundle here). The relevant bundling (one-units group `1 + 𝔪`) is a *separate* future def, not this lemma. |
|  5 | vector-space/metric/field-specific result mathlib's hierarchy would weaken to modules / (semi)ring? | **yes** | Same as row 1 — weaken `NormedField`/`NormedAlgebra ℚ_[p]` to `NormedRing` + ultrametric + `‖(p:L)‖<1` where the proof allows. | The natural mathlib home is `Mathlib/Analysis/Normed/.../Ultra` or a new `Mathlib/NumberTheory/Padics/Exp.lean`, stated as generally as the ultrametric proof supports. |
|  6 | 1-categorical statement with higher-categorical generalisation mathlib moves toward? | no | — | No categorical content. |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive groups/monoids/ordered structures? | no | — | The index `p` and exponent `p^j` are intrinsic to the residue characteristic; not an artificial concretisation. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** (rows 1, 2, 5).
  - Proposed mathlib-idiomatic restatement: the **typeclass-weakened** form of
    Phase 4b (drop `NormedAlgebra ℚ_[p]`, drop `CompleteSpace`, add
    `‖(p:L)‖ ≤ p⁻¹` over `[NormedField L] [IsUltrametricDist L]`), with the
    conclusion stated against a **shared p-adic exponential-ball predicate**
    (the standard `‖x‖ < p^{−1/(p−1)}` ball) rather than the project-local
    `def InExpBall`, and ideally as `∀ᶠ j in atTop, …`.
  - Cost: **MODERATE** (the predicate unification is the larger part; the
    typeclass weakening is mechanical for this lemma + its 3 sibling lemmas).
  - Mathlib downstream this enables: (i) the lemma becomes available for
    `ℂ_[p]`, `ℤ_[p]`, and finite extensions `K/ℚ_p` uniformly; (ii) an `∀ᶠ`
    form composes with `Filter`/`nhds` API; (iii) stated against a canonical
    exp-ball predicate, it slots directly under a future mathlib p-adic
    exp/log API (which does not yet exist — see Phase 5) as the lemma that
    *extends `log_p` to all one-units*.
  - Real mathematical improvement (not just "looks cooler"): the result is
    really a statement about *complete ultrametric fields of residue
    characteristic `p`*; tying it to `NormedAlgebra ℚ_[p] L` and a bespoke
    `InExpBall` def understates its scope and blocks reuse.

Because Phase 4c finds a real modern-idiom improvement, Phase 7 is steered to
`YES-but-generalise-first` (reasons: LITERATURE-WEAKENING **and** MODERN-IDIOM).

---

### Mathlib search-status: `exists_pPow_pow_inExpBall`

[A] Lean-Finder       — n/a: Lean-Finder MCP not installed in this environment. Compensated by grep + structural reasoning over the local mathlib checkout `.lake/packages/mathlib`.
[B] Loogle            type pattern `‖_ ^ _ ^ _ - 1‖ < _` / `∃ _, ‖_ - 1‖ < _` — n/a (Loogle MCP not installed); grep proxy run instead (see [D]). No analogous decl found.
[C] LeanSearch        nl: "some p-power of a one-unit lands in the p-adic exponential convergence ball" — n/a (LeanSearch MCP not installed); WebSearch + local grep used instead.
[D] Grep mathlib src  `padicLog`, `padicExp`, `expp`, `InExpBall`, `p^{-1/(p-1)}`, exp radius of convergence, one-units p-power, `IsTopologicallyNilpotent`, `(1+x)^p` binomial norm bound, `dvd_choose_self` over `Mathlib/NumberTheory/Padics/**` and `Mathlib/Analysis/Normed/**` | **decisive**: mathlib has **no p-adic exponential, no p-adic logarithm, no exponential/convergence ball** at all (`grep -rln "padicLog\|padicExp\|InExpBall" Mathlib` → empty; `Mathlib/NumberTheory/Padics/` contains no exp/log file). |
[E] Name pattern      grep for `*pPow*`, `*pow*ExpBall*`, `*one_unit*pow*`, `exists_pow*ball*` in mathlib | no hits.

Searched for both:
  - the user's current form (`∃ j, InExpBall p (w^(p^j) − 1)`) — not in mathlib (no `InExpBall`, no p-adic exp at all);
  - the literature-standard form (`u^{p^n}` enters `‖x‖ < p^{−1/(p−1)}`) — not in mathlib (no convergence-ball concept; no p-adic exp/log API exists to host it).

Closest mathlib building block found, and why it does NOT suffice:
  - `IsTopologicallyNilpotent.exists_pow_mem_of_mem_nhds`
    (`Mathlib/Topology/Algebra/TopologicallyNilpotent.lean:78`): if `a^n → 0`
    then for every nbhd `v` of `0`, some `a^n ∈ v`. **Not applicable.** Our `w`
    is a *one-unit*; `t = w − 1` is **not** topologically nilpotent — `t^n` does
    NOT tend to `0` in general (e.g. `‖t‖` may be constant `< 1` with `‖t^n‖ =
    ‖t‖^n` not entering the *much smaller* exp ball, and more to the point the
    map that contracts is the **`p`-power Frobenius subsequence** `w ↦ w^p`, not
    ordinary powers). The contraction `w^{p^j} → 1` is governed by
    `‖(1+t)^p − 1‖ ≤ max(‖t‖^p, p⁻¹‖t‖)` — a `p`-divisibility-of-binomial-
    coefficients estimate, not an `IsTopologicallyNilpotent` instance.
  - `Nat.Prime.dvd_choose_self`, `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`,
    `IsUltrametricDist.norm_natCast_le_one`, `tendsto_pow_atTop_nhds_zero_of_lt_one`
    — these are the genuine mathlib primitives the proof *uses internally*, but
    assembling them into this statement is a real multi-step proof (see Phase 6),
    not a composition.

Concluded: **not in mathlib** (all available methods exhausted, plus the
literature-standard form). Mathlib has neither the result nor even the vocabulary
(no p-adic exp/log, no exponential ball) to state it.

---

### Call sites — `exists_pPow_pow_inExpBall`

Internal use count: **4** (within `PadicLFunctions`, NOT counting the declaring
file `ExtLog.lean`).
External-to-file callers: **2 distinct files** — but in practice **1 file**
(`ValuesAtOne.lean`, in the `MeasureR` sub-namespace, multiple sites) plus the
intra-file consumer `extLogDomain_of_integral_norm_one` in `ExtLog.lean` itself.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| ValuesAtOne.lean:553 | `obtain ⟨jx, hjx⟩ := exists_pPow_pow_inExpBall (p := p) hx` |
| ValuesAtOne.lean:554 | `obtain ⟨jy, hjy⟩ := exists_pPow_pow_inExpBall (p := p) hy` |
| ValuesAtOne.lean:592 | `obtain ⟨j, hj⟩ := exists_pPow_pow_inExpBall (p := p) hx` |
| ValuesAtOne.lean:1049 | `obtain ⟨j, hj⟩ := exists_pPow_pow_inExpBall (p := p) hx` |
| ExtLog.lean:451 (declaring file) | `obtain ⟨j, hj⟩ := exists_pPow_pow_inExpBall p hlt` (inside `extLogDomain_of_integral_norm_one`) |

Inline-derivation grep (was the equivalent re-derived elsewhere without calling
`exists_pPow_pow_inExpBall`?):
  - **(none found).** No site re-proves "some `p`-power enters the exp ball"
    inline; every consumer goes through this lemma. (`ValuesAtOne.lean` defines
    its own `padicLog_pow_pPow_of_norm_lt_one`, but that is the *log-power-law*
    `log(z^{p^N}) = p^N·log z`, a different statement; it does not re-derive the
    contraction.)

**Composability signal:** ≥3 internal uses across a downstream file, no inline
re-derivation → this is **real, depended-upon API** (the K≥3 row of the
call-sites table → YES-* lean). It is exactly the lemma that defines the
extended-log *domain*.

---

### Composition check (Phase 6)

Can `exists_pPow_pow_inExpBall` be derived from mathlib in ≤3 chained calls?

Attempt 1: `IsTopologicallyNilpotent.exists_pow_mem_of_mem_nhds`.
  - Mathlib decls used: `IsTopologicallyNilpotent`, `.exists_pow_mem_of_mem_nhds`.
  - Result: **fails.** Requires `(w − 1)` topologically nilpotent (`(w−1)^n → 0`),
    which is FALSE for a generic one-unit; and it would give *some ordinary
    power* `(w−1)^n ∈ v`, not `w^{p^j} − 1` in the exp ball. The statement is
    about the `p`-power Frobenius subsequence of `w`, not powers of `w − 1`.
  - Notes: structurally the wrong lemma; see Phase 5.

Attempt 2: assemble from the genuine ingredients.
  - Mathlib decls used: `Nat.Prime.dvd_choose_self` (→ `‖(1+t)^p−1‖ ≤ max(‖t‖^p,
    p⁻¹‖t‖)`, itself the project lemma `norm_pow_p_sub_one_le`),
    `tendsto_pow_atTop_nhds_zero_of_lt_one`, `Metric.tendsto_atTop`,
    `pow_le_pow_left₀`, `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`.
  - Result: **fails as a composition.** This is the actual ~50-line proof: a
    `Nat.rec` induction establishing the geometric decay
    `‖w^{p^j} − 1‖ ≤ t0^j · ‖w − 1‖` with `t0 = max(‖w−1‖^{p−1}, p⁻¹) < 1`,
    followed by a `Tendsto … (𝓝 0)` argument and an `ε = p⁻¹` extraction. It
    chains many `have`s with non-trivial reasoning between them — per the Phase 6
    heuristics table ("multiple `have`s with non-trivial reasoning" / "requires
    `by rw[...]`…") this is **a proof, not a composition**.
  - Notes: even the *single-step* bound `norm_pow_p_sub_one_le`
    (`ExtLog.lean:96`) is itself a ~25-line lemma; this theorem iterates it.

Conclusion: **NOT-COMPOSABLE.** Phase 7 therefore considers the YES verdicts
(and excludes both NO buckets). There is no ≤3-call mathlib derivation; indeed
mathlib lacks the target concept entirely.

---

## Verdict: `exists_pPow_pow_inExpBall`

**Category:** `YES-but-generalise-first`

**Evidence:**
- Literature search (Phase 3): the lemma is the standard p-power contraction of
  one-units into the p-adic exponential/convergence ball (Washington §5.1,
  Koblitz, Neukirch II.5, Cassels; radii `exp: ‖x‖<p^{−1/(p−1)}`, `log: ‖x−1‖<1`
  confirmed across ≥4 channels). Standard form is over a complete ultrametric
  field of residue characteristic `p`; no person's name attaches (it is a
  foundational lemma, assumed-known even in recent arXiv work on `im(log)`).
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — `NormedAlgebra
  ℚ_[p] L` is stronger than the genuinely-used `ultrametric + ‖(p:L)‖ ≤ p⁻¹`,
  and `CompleteSpace` is already `omit`-ed (unused). Phase 4c additionally finds
  a real MODERN-IDIOM improvement (typeclass weakening + a shared exp-ball
  predicate + an `∀ᶠ` form).
- Mathlib search (Phase 5): **not in mathlib** — mathlib has no p-adic exp, no
  p-adic log, and no exponential/convergence-ball concept; the closest primitive
  (`IsTopologicallyNilpotent.exists_pow_mem_of_mem_nhds`) does not apply.
- Composition check (Phase 6): **NOT-COMPOSABLE** — a genuine ~50-line geometric-
  decay proof, not a ≤3-call composition.

**Rationale (1–2 paragraphs):**

This is genuine, mathlib-grade mathematical content: it is the foundational
lemma by which the p-adic logarithm is extended from its small convergence ball
to *all* one-units (and dually, the lemma underlying the exp/log isometry
`B ≅ 1 + B`). Mathlib today has **none** of this machinery — there is no
`padicExp`, no `padicLog`, and no notion of the exponential ball
`‖x‖ < p^{−1/(p−1)}` anywhere in `Mathlib/NumberTheory/Padics/` or the normed-
field analysis tree. So the verdict cannot be either NO bucket: NO-mathlib-has-it
is impossible (mathlib lacks even the vocabulary), and NO-composable is excluded
because the one superficially-related primitive
(`IsTopologicallyNilpotent.exists_pow_mem_of_mem_nhds`) is structurally the wrong
tool (it needs `(w−1)^n → 0`, false for one-units; the contraction is via the
`p`-power Frobenius subsequence, driven by `p ∣ \binom{p}{i}`), and the real
proof is a ~50-line induction-plus-`Tendsto` argument. The 4 downstream call
sites with no inline re-derivation confirm it is depended-upon API, not a
throwaway wrapper.

It is **not** `YES-add-as-is`, however, because Phase 4b found the statement
strictly narrower than the literature standard (it bundles `NormedAlgebra ℚ_[p] L`
where only ultrametricity plus `‖(p:L)‖ ≤ p⁻¹` is used, and carries an unused
`CompleteSpace`), and Phase 4c found a real organisational improvement: the
result should be stated for a complete ultrametric field of residue characteristic
`p`, against a *shared* exponential-ball predicate rather than the project-local
`def InExpBall`, ideally in the modern `∀ᶠ j in atTop` form. Crucially, the
right move is not to upstream this single lemma in isolation but to upstream it
**as part of a p-adic-exponential/logarithm API** — the convergence-ball
predicate, `padicExp`/`padicLog` and their basic laws, then this contraction
lemma as the bridge that extends `log_p` to one-units. Hence: generalise (and
package) first.

**WHY-generalise-first detail:**

Reason for the generalisation: **BOTH**
  - LITERATURE-WEAKENING: Phase 4b — the user's `[NormedAlgebra ℚ_[p] L]` is
    strictly stronger than the proof requires; the literature states this for
    general complete ultrametric fields of residue characteristic `p`.
  - MODERN-IDIOM (Bourbaki 2.0): Phase 4c — replace the bundled algebra
    hypothesis with the minimal typeclass surface, state the conclusion against
    a canonical exp-ball predicate (so it composes with a future p-adic exp/log
    API), and prefer the `∀ᶠ`/`Tendsto` formulation.

Proposed restatement:
```lean
-- stated against a shared non-archimedean exponential-ball predicate
-- (the standard `‖x‖ < p^{-1/(p-1)}` ball), over the minimal ambient.
theorem exists_pPow_pow_inExpBall
    {L : Type*} [NormedField L] [IsUltrametricDist L]
    (hpL : ‖(p : L)‖ ≤ (p : ℝ)⁻¹)
    {w : L} (hw : ‖w - 1‖ < 1) :
    ∀ᶠ j in Filter.atTop, ‖w ^ p ^ j - 1‖ ^ (p - 1) < (p : ℝ)⁻¹ := by
  sorry  -- the current ~50-line proof adapts; `‖(p:L)‖=p⁻¹` uses replaced by `hpL`,
         -- `∃` strengthened to `∀ᶠ` (the decay bound already holds for all large j).
```
Estimated cost of regeneralisation: **MODERATE.** The decay argument is
unchanged; the work is (a) threading `hpL` through the 3 sibling lemmas
(`mul_mem_expBall`, `pow_mem_expBall`, `norm_pow_p_sub_one_le`) that share the
ambient, and (b) introducing/aligning a shared exp-ball predicate. (EXPENSIVE
would not downgrade the verdict regardless; this is only MODERATE.)
Note: EXPENSIVE does not downgrade the verdict — mathlib's value is the right form.

Mathlib downstream this enables (MODERN-IDIOM):
  - uniform availability over `ℚ_[p]`, `ℤ_[p]`, `ℂ_[p]`, and finite extensions
    `K/ℚ_p` (any complete ultrametric field of residue char `p`);
  - composition with mathlib's `Filter`/`nhds` API via the `∀ᶠ` form;
  - the lemma slots directly under a future `Mathlib/NumberTheory/Padics/Exp.lean`
    p-adic exp/log API as the bridge extending `log_p` to all one-units — which
    is the documented gap (mathlib has p-adic numbers, `PadicVal`, Mahler bases,
    but **no p-adic exp/log**).

Next action: run `/generalise PadicLFunctions.exists_pPow_pow_inExpBall` (it will
tension against both the literature-standard form from Phase 3 and the
modern-idiom form from Phase 4c). Then — before any PR — scope the upstreaming as
a **p-adic exp/log API package** (the exp-ball predicate + `padicExp`/`padicLog`
basics + this contraction lemma), not a lone-lemma PR. Proposed mathlib home:
`Mathlib/NumberTheory/Padics/Exp.lean` (new file). PR grouping: ship together
with the supporting `mul_mem_expBall`, `pow_mem_expBall`, `norm_pow_p_sub_one_le`,
`norm_lt_one_of_inExpBall`, and the `InExpBall`→standard-ball predicate, plus
`padicLog_pow` — they are one coherent API surface.

---

## Next step

Run `/generalise PadicLFunctions.exists_pPow_pow_inExpBall` to lift the statement
to a complete ultrametric field of residue characteristic `p` (replacing
`[NormedAlgebra ℚ_[p] L]` + unused `[CompleteSpace L]` with `[IsUltrametricDist L]`
+ `‖(p:L)‖ ≤ p⁻¹`) and to a shared exponential-ball predicate in `∀ᶠ` form. Then
plan the upstreaming as a p-adic-exp/log **API package** for a new
`Mathlib/NumberTheory/Padics/Exp.lean`, not an isolated-lemma PR, since mathlib
currently has no p-adic exponential or logarithm at all.
