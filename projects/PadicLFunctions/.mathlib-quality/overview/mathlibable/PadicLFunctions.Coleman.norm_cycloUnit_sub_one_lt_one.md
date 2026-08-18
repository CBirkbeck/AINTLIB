# `/mathlibable` report — `PadicLFunctions.Coleman.norm_cycloUnit_sub_one_lt_one`

Mode A, full 10-phase workflow, exhaustive 9-channel literature search.
Qualified name: `PadicLFunctions.Coleman.norm_cycloUnit_sub_one_lt_one`
(declared inside `namespace PadicLFunctions` → `namespace Coleman`).

---

## Verdict (five-bucket)

**`NO-composable-from-mathlib`** — the *generic* facts the proof rests on
(ultrametric triangle inequality, `‖Σ‖ ≤ max`, `‖(p:·)‖ < 1`, `‖(n:·)‖ ≤ 1`)
are all in mathlib's `IsUltrametricDist` / `Padic` API, and the *statement* is a
specialisation of mathlib's already-existing abstract notion of a **principal
unit** (`ValuationSubring.principalUnitGroup`, `v(x−1) < 1`) to the
project-local object `cycloUnit p a n` in `ℂ_[p]`. No new mathlib lemma is
justified: the content is the Iwasawa-theory bookkeeping fact "`c_n(a)` is a
*principal* local unit when `a ≡ 1 (mod p)`", proved by a short split
`c−1 = (c−a) + (a−1)` over mathlib ultrametric primitives. It is, however, **not
a 0-line drop-in** (no mathlib lemma names this `ℂ_[p]` cyclotomic-unit object),
so it is NO-**composable** rather than NO-**mathlib-has-it**.

A secondary consideration (recorded, not chosen): the proof is genuinely
multi-step (≈5 `have`s, two distinct sub-arguments) rather than a tidy ≤3-call
chain, which pulls toward "keep it as a project lemma". But the right reading is
that it is *project-local glue assembled from mathlib primitives* — see the
BORDERLINE discussion at the end of Phase 7 for why the verdict still resolves
cleanly to NO-composable and no question to the user is needed.

---

## Baseline (Phase 0)

- lake build:               **not re-run** (build is stale/slow per task note); **reasoned from source** — Phase 0 fallback. The declaration, its private helpers, and the upstream defs (`cycloUnit`, `zetaSys`, `pi`, `norm_pi_lt_one`) were read directly from the project files and the pinned mathlib tree.
- decl `PadicLFunctions.Coleman.norm_cycloUnit_sub_one_lt_one`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/Iwasawa/CyclotomicUnits.lean:376`
- kind:                      theorem
- has sorry:                 no (complete proof, lines 378–396)
- mathlib pin:               `d90090f` (per `lakefile.toml`); toolchain `leanprover/lean4:v4.32.0-rc1`
- module docstring summary:  Cyclotomic units — the global modules `𝒟_n` and their local closures `𝒞` (RJW §11.3); all objects realised inside `ℂ_[p]`. The milestone is that the Coleman-map inputs `c_n(a)` live in `𝒞_{∞,1} ≤ 𝒰_{∞,1}`.

---

## Statement (Phase 1)

`PadicLFunctions.Coleman.norm_cycloUnit_sub_one_lt_one` is a **theorem** stating:

> Let `p` be prime and `n ≥ 1`. Let `ξ = ξ_{p^n}` be the chosen primitive
> `p^n`-th root of unity in `ℂ_p`, and let `c_n(a) = (ξ^a − 1)/(ξ − 1) =
> 1 + ξ + ⋯ + ξ^{a−1}` be the `a`-th cyclotomic unit. If `a ≡ 1 (mod p)`, then
> `‖c_n(a) − 1‖_p < 1`.

Mathematically: when `a ≡ 1 (mod p)`, the cyclotomic unit `c_n(a)` is a
**principal (one-)unit** of the local cyclotomic field `K_n = ℚ_p(ξ_{p^n})` —
i.e. `c_n(a) ≡ 1 (mod 𝔭_n)`, equivalently `c_n(a) ∈ 𝒰_{n,1}`, the kernel of
`𝒪_{K_n}^× → 𝒪_{K_n}^× / 𝔭_n`. This is the refinement of the textbook
congruence `c_n(a) ≡ a (mod λ)` (where `λ = ξ − 1`): the generic statement only
gives `c_n(a) ≡ a`, and one needs `a ≡ 1 (mod p)` to upgrade to `c_n(a) ≡ 1`.

Variables / typeclasses (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the residue characteristic; `ℂ_[p]` is the completed algebraic closure `ℂ_p`.
- `a : ℕ` — the exponent / index of the cyclotomic unit.
- `n : ℕ` — the level (`ξ_{p^n}` is a primitive `p^n`-th root).

Hypotheses (Lean side):
- `_ha : ¬ (p : ℕ) ∣ a` — `a` coprime to `p` (so `c_n(a)` is a unit). **Marked `_ha` — unused in this proof** (the norm bound does not need coprimality; it is carried only for signature uniformity with the sibling lemmas).
- `hn : 1 ≤ n` — positive level (so `ξ ≠ 1`, `pi ≠ 0`, `‖pi‖ < 1`).
- `ha1 : a ≡ 1 [MOD p]` — **the load-bearing hypothesis**; it is exactly what makes `‖(a:ℂ_[p]) − 1‖ < 1` (since `p ∣ a − 1`).

Conclusion (math): `c_n(a) − 1` has `p`-adic absolute value `< 1` (i.e. `c_n(a)` is a principal local unit).

Conclusion (Lean): `‖cycloUnit p a n - 1‖ < 1`.

**Proof shape (read from source, lines 378–396).** Write
`c − 1 = (c − a) + (a − 1)` and bound each summand by the ultrametric:

1. `c_n(a) − a = Σ_{i<a} (ξ^i − 1)` (via `cycloUnit_eq_geomSum` +
   `Finset.sum_sub_distrib`). Each `ξ^i − 1` has norm `≤ ‖ξ − 1‖ = ‖π_n‖ < 1`
   (sibling helper `norm_pow_sub_one_le'`, using `‖ξ‖ = 1`), so the
   ultrametric `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg` gives
   `‖c − a‖ < 1` (bounded by `‖π_n‖`, then `norm_pi_lt_one`).
2. `‖(a:ℂ_[p]) − 1‖ < 1`: since `a ≡ 1 (mod p)`, `p ∣ a − 1`, so
   `a − 1 = p·k` and `‖a − 1‖ = ‖p‖·‖k‖ ≤ p^{-1}·1 < 1` (helper
   `norm_natCast_sub_one_lt_one_of_modEq`, using `Padic.norm_p` and
   `IsUltrametricDist.norm_natCast_le_one`). **This is the only step that uses
   `ha1`.**
3. Combine with `IsUltrametricDist.norm_add_le_max` + `max_lt`.

---

## Preliminary checks (Phase 2)

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: It is a helper lemma feeding one milestone (`cyclo_mem_cycloTower1`), not
itself a `## Main results` entry, not a `def`/`class`, and not named after a
person/place. It is the "`c_n(a)` is a principal unit" estimate used to land the
Coleman inputs in `𝒰_{n,1}`.

(Literature width is EXHAUSTIVE regardless; BIG/SMALL only frames the report.)

### One-line check (Phase 2b)

n/a — kind is `theorem`, not a `def`/`abbrev`/`structure`. (Body is a ~18-line
multi-step proof, definitely not a one-liner.)

---

## PHASE 3 — Literature search (EXHAUSTIVE)

### Literature search table — 9/10-channel protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | cyclotomic unit principal unit congruent 1 mod p p-adic `(ζ^a−1)/(ζ−1)` | yes | `(1−ζ^k)/(1−ζ) = Σ ζ^i`; `ζ^k ≡ 1 (mod λ)`, `λ = 1−ζ` | Sharifi *cycl.pdf*, Erickson/Ciurca notes, Coates–Sujatha — all treat it as a one-line classical identity |
| 2 | WebSearch (general/Washington form) | cyclotomic units Washington congruence 1 mod p local units | yes | cyclotomic units = subgroup of finite index; congruences `η_i ≡ 1 mod π^{2m_i}` studied | Washington, *Introduction to Cyclotomic Fields*, ch. 8 (Springer GTM 83); Wikipedia "Cyclotomic unit" |
| 3 | WebSearch (named-after / aliases) | `1 + ζ + ⋯ + ζ^{a−1}` congruent `a` modulo `(ζ−1)` principal unit | yes | `c = Σ_{i<a} ζ^i ≡ a (mod λ)`; integer-sum congruence | confirms the *generic* `c ≡ a`, not the `c ≡ 1` refinement — the latter needs `a ≡ 1 (mod p)` |
| 4 | WebSearch (p-adic valuation angle) | geometric sum primitive `p^n`-th root, p-adic valuation positive, uniformizer `(1−ζ)` | yes | `ℚ_p(ζ_{p^m})/ℚ_p` totally ramified; `ζ_{p^m}−1` a uniformizer; `v_p(1−ζ_{p^s}) = 1/φ(p^s) > 0` | K. Conrad / J. Thorne notes (dpmms.cam, kconrad.math); Feo *p-adic fields* ch. 7 — `‖ξ−1‖ < 1` is the qualitative shadow |
| 5 | WebSearch (Iwasawa/Coleman context) | Rubin/Coleman cyclotomic units principal units norm-compatible system | yes | Euler system of cyclotomic units; norm-compatible `(u_n)` ↦ Coleman power series | Coates–Sujatha *Cyclotomic Fields and Zeta Values*; Hida *Elementary Iwasawa Theory*; Sharifi AWS notes — `c_n(a)` is exactly this kind of bookkeeping element |
| 6 | ChatGPT MCP | (intended: "standard form + generality + historical evolution of the cyclotomic-unit principal-unit congruence") | **n/a — server unavailable** | — | `plugin:mathlib-quality:chatgpt-math` MCP failed to connect (`claude mcp list` → ✘ Failed to connect). Compensated by running **5** WebSearch queries (vs. the required 3) at distinct generality levels + 2 WebFetch + arXiv source read. |
| 7 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/` | n/a | (no references dir) | both `.mathlib-quality/references/` and the local `refs/` store are absent on this machine — recorded n/a |
| 8 | nLab / Encyclopedia of Math | cyclotomic unit / cyclotomic field; principal unit; one-units filtration | yes (peripheral) | nLab "cyclotomic field" + EoM "cyclotomic field" cover the field & units; the one-unit filtration `U_n = Ker(o^× → (o/p^n)^×)` appears in local-field notes | the *abstract* notion (principal/one-unit) is standard; the *specific* `c_n(a)`-is-principal statement is not on nLab |
| 9 | Stacks Project | — | **n/a** | — | not an algebraic-geometry / scheme-theoretic statement; it is a `p`-adic congruence in a local cyclotomic field. Stacks has no cyclotomic-unit material. |
| 10 | arXiv (source + recent) | arXiv:2309.15692 (RJW source); "primary units in cyclotomic fields" (arXiv:0911.2566); "bases for modules of cyclotomic units" (arXiv:2407.02002) | yes | RJW = Rodrigues Jacinto–Williams, *An introduction to p-adic L-functions* (expository); §10–12 construct the Coleman map via cyclotomic units | **the source is expository**; the project docstring records that RJW *glosses* the `a ≡ 1 (mod p)` point ("the §12 arguments use the principal-unit part") |

Protocol pass check:
- WebSearch ran **5** distinct queries (≥3) at specific / Washington-general / aliases / p-adic-valuation / Iwasawa-context levels. ✓
- ChatGPT MCP: **unavailable** (server down) — explicitly recorded with reason and over-compensated with 2 extra WebSearch queries + WebFetch + arXiv read. ✓ (best achievable)
- Local references: checked, n/a (absent). ✓
- nLab: checked. ✓
- Stacks: checked, n/a with reason. ✓
- nCatLab/MathOverflow/arXiv: MathOverflow query ran (folded into row 1/aliases, surfaced Wikipedia + Coates–Sujatha + Erickson); arXiv source pinned (row 10). ✓

### Literature summary (Phase 3)

Concept identified as: **cyclotomic units as principal (one-)units of the local
cyclotomic field** — the element `c_n(a) = (ξ^a−1)/(ξ−1) = Σ_{i<a} ξ^i`, and the
congruence `c_n(a) ≡ a (mod λ)` (`λ = ξ−1`), specialised to `c_n(a) ≡ 1` under
`a ≡ 1 (mod p)`.

Sources agree on the standard form: **yes** for the underlying pieces, all of
which are textbook-classical:
  - the geometric-sum identity `(1−ζ^a)/(1−ζ) = Σ ζ^i` and `ζ^k ≡ 1 (mod λ)`
    (Sharifi, Erickson, Coates–Sujatha, Wikipedia);
  - `ζ_{p^n}−1` a uniformizer of the totally ramified `ℚ_p(ζ_{p^n})/ℚ_p` with
    `v_p(1−ζ_{p^s}) = 1/φ(p^s) > 0`, i.e. `‖ξ−1‖_p < 1` (K. Conrad, Thorne, Feo);
  - cyclotomic units / one-unit filtration in Iwasawa theory (Washington,
    Coates–Sujatha, Hida, Rubin).

Most general standard form: the qualitative content is "in a `p`-adic field, a
sum of elements each `≡ 1 (mod 𝔭)`, plus an integer `≡ 1 (mod p)`, is itself
`≡ 1 (mod 𝔭)`" — i.e. the **principal-unit subgroup is closed under the relevant
sums**, an instance of the one-unit filtration being a subgroup.

Generality dimensions where the literature varies:
  - **the ambient field**: stated over `ℚ_p(ζ_{p^n})` (the literature's local
    field) — the project works in the larger `ℂ_p`, which is *less* canonical but
    harmless (norm is the unique extension).
  - **the congruence**: literature default is `c_n(a) ≡ a (mod λ)`; the
    `c_n(a) ≡ 1` form is the special case `a ≡ 1 (mod p)` and is exactly the
    bookkeeping RJW glosses.

Disagreement with the literature: **none mathematically**. The lemma is a
correct, narrow specialisation. The only "gap" is that the source (RJW, an
*expository* survey) does not even state the `a ≡ 1 (mod p)` refinement
explicitly — it is genuine project-added bookkeeping, which is a strong signal it
is too specialised / non-canonical to be a named mathlib lemma in this form.

---

## PHASE 4 — Generality analysis

### Generality status table — `norm_cycloUnit_sub_one_lt_one`

Literature-standard form (from Phase 3): "a sum of one-units, plus an integer
`≡ 1 (mod p)`, is a one-unit", phrased abstractly via the principal-unit
subgroup `v(x−1) < 1`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|---|---|---|---|---|
| 1 | ambient field `ℂ_[p]` (implicit) | the full `ℂ_p` | `ℚ_p(ξ_{p^n})` (the local cyclotomic field) | — | The object is genuinely realised in `ℂ_p` in this project (replan R11.7). The statement would be *more* canonical over the local field `K_n`, but that is a project architecture choice, not a weakening of this lemma's hypotheses. |
| 2 | `cycloUnit p a n` (the subject) | the specific `(ξ^a−1)/(ξ−1)` | the abstract notion "principal unit" `v(x−1) < 1` | yes (abstract) | The *abstract* statement is `x ∈ principalUnitGroup ↔ v(x−1) < 1`, which mathlib already has (`ValuationSubring.mem_principalUnitGroup_iff`). The user's lemma is the *instance* "`c_n(a)` lies in it (when `a ≡ 1 mod p`)" — not a more-general fact waiting to be stated. |
| 3 | `_ha : ¬ p ∣ a` | coprimality | (not needed here) | yes — **drop it** | The proof never uses `_ha` (note the underscore). It is dead weight carried for signature parallelism. A mathlib version would drop it. |
| 4 | `ha1 : a ≡ 1 [MOD p]` | the congruence | the congruence (load-bearing) | NO | This is exactly what forces `‖a−1‖ < 1`. Without it `‖c−1‖ = 1` (the docstring's own note: `c_n(a) ≡ a`, not `1`). It cannot be weakened. |
| 5 | `hn : 1 ≤ n` | positive level | `ξ ≠ 1` (so `n ≥ 1` for `p^n`-roots) | NO | needed for `ξ − 1 ≠ 0`, `‖π_n‖ < 1`. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL up to the dead `_ha` hypothesis** — i.e.
the mathematical hypotheses (`ha1`, `hn`) are exactly the necessary ones; the only
slack is the unused coprimality `_ha`, which is a trivial mechanical drop, not a
genuine generalisation of content.

Number of weakening opportunities found: **1 trivial** (delete unused `_ha`).

Proposed restatement: drop `_ha`. This does **not** turn the lemma into a missing
general statement worth upstreaming — the genuinely general fact (principal-unit
membership ⇔ `v(x−1) < 1`) is already in mathlib (Phase 5). So the verdict is not
`YES-but-generalise-first`.

Cost of restatement: CHEAP (delete one binder + fix the one call site's argument
list). But cost is irrelevant: there is no *missing* general/modern target to aim
at.

### Modern-idiom check (Phase 4c) — Bourbaki 2.0

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|---------------------------------|
| 1 | "let `c_n(a)` be a foo" → typeclass/instance? | no | — | The subject is a concrete element, not a structure; nothing to bundle. |
| 2 | sequences/metric → filters/topology? | no | — | This is a single static norm inequality, no limit/convergence. |
| 3 | construct an object → universal-property class? | partially — but mathlib already did it | use `ValuationSubring.principalUnitGroup` / the one-unit filtration as the bundled object | The "right" mathlib idiom for "`c−1` is in the maximal ideal" is *membership in the principal-unit group*; **mathlib already has that abstraction** (`mem_principalUnitGroup_iff`). The contribution would be the *instance*, which is project-specific. |
| 4 | set-with-closure-predicate → bundled substructure? | no (already bundled in the project's `localUnitsOne`) | — | The project already phrases `𝒰_{n,1}` as a `Subgroup`; this lemma is the membership witness. |
| 5 | field/metric-specific → weaken typeclass? | no | — | `ℂ_p` (`IsUltrametricDist` normed field) is already the right generality; the proof uses only ultrametric primitives, which are stated at full `IsUltrametricDist` generality in mathlib. |
| 6 | 1-categorical → higher-categorical? | no | — | not categorical. |
| 7 | concrete index `ℕ`/`ℤ`/`ℝ` → general monoid/group? | no | — | `a, n : ℕ` are the natural indices for `p^n`-roots and the `a`-th cyclotomic unit; no algebraic-structure generalisation applies. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (as a *missing* contribution). The contemporary
mathlib idiom for the conclusion — "`x` is a principal/one-unit" — **already
exists** as `ValuationSubring.principalUnitGroup` (`mem_principalUnitGroup_iff :
x ∈ A.principalUnitGroup ↔ A.valuation ((x:K) − 1) < 1`). The project even has
its own bundled `localUnitsOne` subgroup. So there is no Bourbaki-2.0 reformulation
that this lemma supplies to mathlib; the abstraction is upstream already, and this
lemma is the *application* of it to one concrete cyclotomic-unit object.

One-line reason this is not a modernisation move: the only "modern" object in
sight (the one-unit / principal-unit subgroup) is already in mathlib; the lemma
merely witnesses membership for a project-local element.

---

## PHASE 4.5 — Diamond / defeq risk

n/a — declaration kind is **theorem** (introduces no definitional equalities or
typeclass-search paths).

---

## PHASE 5 — Mathlib search (five-method)

### Mathlib search-status: `norm_cycloUnit_sub_one_lt_one`

[A] Lean-Finder       (server-style NL queries, run as WebSearch over mathlib + grep proxy) — *no hit* for a lemma equating a cyclotomic-unit/geometric-sum's `‖·−1‖` to `< 1`.
[B] Loogle (type-pattern, grep proxy over mathlib src for `‖ ?x - 1 ‖ < 1` and `IsPrimitiveRoot … ‖ … - 1‖`) — *no hit*: the only `‖x − 1‖ < 1` lemmas are `Unitary.norm_sub_one_lt_two_iff` (C*-algebras, `< 2`, unrelated) and the `Padics/AddChar.lean` comment (no lemma). No cyclotomic-unit norm lemma.
[C] LeanSearch (NL "cyclotomic unit is a principal unit / congruent to 1 mod the maximal ideal p-adically", run as WebSearch over leansearch-style phrasing + mathlib grep) — *no hit*.
[D] Grep mathlib src — terms: `cyclo` in `Mathlib/NumberTheory/`, `principalUnit`, `norm_sub_one_lt`, `geom_sum_isUnit`. Hits found but **none matching**:
  - `Mathlib/RingTheory/RootsOfUnity/CyclotomicUnits.lean` — Best–Brasca: `associated_sub_one_pow_sub_one_of_coprime`, `geom_sum_isUnit`, `pow_sub_one_eq_geom_sum_mul_geom_sum_inv_mul_pow_sub_one`, etc. **All multiplicative/`Associated`/`IsUnit` facts; NO norm or p-adic-congruence statement.**
  - `Mathlib/RingTheory/Valuation/ValuationSubring.lean:634–657` — `principalUnitGroup`, `mem_principalUnitGroup_iff` (`v(x−1) < 1`). **The abstract one-unit notion, no cyclotomic specialisation.**
  - `Mathlib/Analysis/Normed/Ring/Ultra.lean`, `Group/Ultra.lean`, `Field/Ultra.lean` — `norm_natCast_le_one`, `norm_intCast_le_one`, `norm_add_le_max`, `norm_sum_le_of_forall_le_of_nonneg` (the *generic* building blocks the proof uses).
  - `Mathlib/NumberTheory/Padics/PadicIntegers.lean:234` — `Padic.norm_p` (`‖p‖ = p⁻¹`).
[E] Name pattern (`lean_local_search` proxy: grep for `cycloUnit`, `norm_cyclo`, `*_sub_one_lt_one` across mathlib) — *no hit* in mathlib (the names are all project-local).

Searched for both:
  - the user's current form (`‖cycloUnit p a n − 1‖ < 1` in `ℂ_[p]`) — not in mathlib;
  - the literature-standard / abstract form ("`c_n(a)` is a principal unit", i.e. `v(c−1) < 1`) — mathlib has the **abstraction** (`mem_principalUnitGroup_iff`) but **not** the cyclotomic-unit instance.

Concluded: **found building blocks** (`IsUltrametricDist.norm_add_le_max`,
`IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`,
`IsUltrametricDist.norm_natCast_le_one`, `Padic.norm_p`,
`ValuationSubring.mem_principalUnitGroup_iff`, plus the project-local
`cycloUnit_eq_geomSum` and `norm_pi_lt_one`); **the packaged statement about this
`ℂ_[p]` cyclotomic-unit object is not in mathlib** (all 5 methods exhausted, both
forms searched).

---

## PHASE 6 — Composition check (+ call-sites)

### Call sites — `norm_cycloUnit_sub_one_lt_one`

Internal use count: **K = 1** (within the project, excluding the declaring file's
own body — and even that one use is *in the same file*).
External-to-file callers: **0 distinct files** (the sole caller is in the same file).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `Iwasawa/CyclotomicUnits.lean:493` | `exact norm_cycloUnit_sub_one_lt_one p ha hn ha1` (inside `cyclo_mem_cycloTower1`, discharging the `𝒰_{n,1}`-membership half) |

Inline-derivation grep (was the equivalent re-derived elsewhere without using this lemma?):
  - (none) — no other site recomputes `‖c_n(a) − 1‖ < 1`. The sibling
    `norm_zetaSys_pow_sub_one_lt_one` (line 335) proves the related `‖ξ^i − 1‖ < 1`
    but for the bare root power, a different (weaker) statement; it is *used by*
    this lemma's helpers, not a re-derivation of it.

What the call-sites pattern says: **K = 1 internal use, no external callers, no
inline re-derivation.** Per the Phase-6 signal table, "K = 1 internal use only →
possibly the wrong abstraction; could be inlined; lean toward NO-composable."
This is the single load-bearing principal-unit estimate behind the
`cyclo_mem_cycloTower1` milestone — it has exactly one consumer.

### Composition check (Phase 6)

Can `norm_cycloUnit_sub_one_lt_one` be derived from mathlib in ≤3 chained calls?

Attempt 1 (direct mathlib one-liner): there is no mathlib lemma `c ↦ ‖c − 1‖ < 1`
for cyclotomic units, so no single call works.
  - Mathlib decls used: none applicable.
  - Result: **fails** — there is no packaged lemma to call.

Attempt 2 (the actual proof, counted as a composition): the proof is
  - `have hca : c − a = Σ (ξ^i − 1)` (rewrite via `cycloUnit_eq_geomSum`, `Finset.sum_sub_distrib`, …);
  - `have hsum : ‖Σ (ξ^i − 1)‖ < 1` (`IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg` + per-term `norm_pow_sub_one_le'` + `norm_pi_lt_one`);
  - `have hsplit : c − 1 = (c − a) + (a − 1)` (`ring`);
  - combine via `IsUltrametricDist.norm_add_le_max` + `max_lt`, with the second branch `norm_natCast_sub_one_lt_one_of_modEq` (itself `Padic.norm_p` + `norm_natCast_le_one`).
  - Mathlib decls used: 4–5 distinct, plus **2 project-private helpers**
    (`norm_pow_sub_one_le'`, `norm_natCast_sub_one_lt_one_of_modEq`) and 1
    project rewrite (`cycloUnit_eq_geomSum`).
  - Result: **NOT a ≤3-call composition** — it is a genuine multi-step proof
    (≈5 `have`s, two distinct sub-arguments, two intermediate helpers).

Conclusion: **NOT-COMPOSABLE as a tidy ≤3-call mathlib chain** — *but* every
ingredient is either a mathlib primitive or a thin project-local fact, and the
*statement* is a specialisation of mathlib's existing principal-unit abstraction.

The Phase-6 heuristic table: this is the row
"`have h := …; have h' := …; exact …` (multiple `have`s with non-trivial reasoning
between) → NO — this is a proof". So as a *literal composition* it is NOT-COMPOSABLE.
The NO-composable **verdict** below is justified on the broader ground (mathlib has
the abstraction + all primitives; the lemma is a project-local application not worth
an upstream lemma), with the refactor being "keep it project-local, optionally
re-express the conclusion through `principalUnitGroup`", *not* "inline a 3-call
mathlib chain at the call site".

---

## PHASE 7 — Verdict

## Verdict: `PadicLFunctions.Coleman.norm_cycloUnit_sub_one_lt_one`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the underlying facts (`(1−ζ^a)/(1−ζ) = Σζ^i`,
  `ζ^k ≡ 1 mod λ`, `ξ_{p^n}−1` a uniformizer with positive valuation, cyclotomic
  units as one-units) are uniformly textbook-classical (Washington, Coates–Sujatha,
  Sharifi, K. Conrad, Hida). The `a ≡ 1 (mod p)` refinement is *not even stated*
  in the expository source (RJW), only glossed — i.e. project-specific bookkeeping.
- Generality analysis (Phase 4): MAXIMALLY GENERAL up to one dead `_ha` hypothesis;
  no *missing* general/modern target — the general object (principal-unit group) is
  already upstream. So neither YES bucket fires (4b: not strictly narrower than a
  *missing* standard form; 4c: no missing modern idiom).
- Mathlib search (Phase 5): not in mathlib in either form; **building blocks present**
  (`IsUltrametricDist.norm_add_le_max`, `…norm_sum_le_of_forall_le_of_nonneg`,
  `…norm_natCast_le_one`, `Padic.norm_p`) and the **abstraction present**
  (`ValuationSubring.mem_principalUnitGroup_iff`).
- Composition check (Phase 6): NOT a tidy ≤3-call chain (genuine multi-step proof),
  K = 1 internal consumer, no external callers, no inline re-derivation.

**Rationale.**
This theorem is a project-local *application* of mathlib infrastructure, not a
missing piece of it. Mathematically it says "`c_n(a)` is a principal (one-)unit
when `a ≡ 1 (mod p)`" — a statement mathlib already supports at the abstract level
(`ValuationSubring.principalUnitGroup`, `mem_principalUnitGroup_iff : x ∈
principalUnitGroup ↔ v(x−1) < 1`) and whose every analytic ingredient is a mathlib
`IsUltrametricDist`/`Padic` primitive. The only genuinely missing thing is the
*instance* "this specific `ℂ_[p]` cyclotomic-unit object satisfies it" — and that
instance is (a) tied to a project-local definition `cycloUnit p a n` realised in the
project's chosen ambient `ℂ_p`, (b) proved via two project-private helpers, and
(c) carries an `a ≡ 1 (mod p)` refinement the expository source does not even
state. Those are three independent signals of "too project-specific / non-canonical
to upstream as a named lemma".

It lands in **NO-composable-from-mathlib** rather than NO-mathlib-has-it because no
single mathlib lemma names this object — it is not a 0-line `exact mathlib_lemma`
drop-in. It is not NO-mathlib-has-it's tidy "follows in ≤1 line" case; it is the
"mathlib has the *building blocks* (and the abstraction), assemble them" case. The
assembly is not literally ≤3 calls (Phase 6 honestly records it as a multi-step
proof), but the correct *action* is not a YES-style upstream PR: it is to keep the
fact project-local, optionally re-expressing the conclusion through mathlib's
`principalUnitGroup` so the project's own `localUnitsOne`/one-unit API and mathlib's
agree.

**NO-composable-from-mathlib — refactor-actionable detail.**

WHY not (upstream): The statement is a specialisation of mathlib's existing
principal-unit abstraction to a project-local object, proved from mathlib's
ultrametric primitives. There is no missing general lemma here: the general fact
(`x` principal ⇔ `v(x−1) < 1`) is `ValuationSubring.mem_principalUnitGroup_iff`,
and "a finite ultrametric sum of small elements is small" is
`IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`. Upstreaming "`cycloUnit p a
n` is principal when `a ≡ 1 mod p`" would be upstreaming a project bookkeeping
instance about a project definition — not mathlib-grade.

Mathlib building blocks (all with full paths):
  - `IsUltrametricDist.norm_add_le_max` — `.lake/packages/mathlib/Mathlib/Topology/Algebra/Valued/NormedValued.lean:53` (and re-exported for `ℂ_[p]` at `.lake/packages/mathlib/Mathlib/NumberTheory/Padics/Complex.lean:203`)
  - `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg` — `.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Ultra.lean` (the additive `to_additive` of `norm_prod_le_of_forall_le_of_nonempty`, ~line 246)
  - `IsUltrametricDist.norm_natCast_le_one` / `norm_intCast_le_one` — `.lake/packages/mathlib/Mathlib/Analysis/Normed/Ring/Ultra.lean:67,77`
  - `Padic.norm_p` — `.lake/packages/mathlib/Mathlib/NumberTheory/Padics/PadicIntegers.lean:234` (`‖(p:·)‖ = p⁻¹`)
  - `ValuationSubring.mem_principalUnitGroup_iff` — `.lake/packages/mathlib/Mathlib/RingTheory/Valuation/ValuationSubring.lean:657` (the abstract one-unit characterisation `v(x−1) < 1`)
  - (project-local, reused) `cycloUnit_eq_geomSum`, `norm_pi_lt_one`, and the two private helpers `norm_pow_sub_one_le'`, `norm_natCast_sub_one_lt_one_of_modEq`.

Composition sketch — **honest note**: this is NOT a ≤3-line inline; the proof is the
existing ~18-line multi-step argument. The "composition" is conceptual: the lemma =
(ultrametric sum bound) + (`p ∣ a−1` integer bound) + (`norm_add_le_max`). The
refactor is therefore *not* "inline at the call site" but "keep, and align with
mathlib's principal-unit abstraction":

```lean
-- Conceptual shape (already what the proof does); the right mathlib-aligned conclusion is
-- membership in the one-unit / principal-unit group, e.g. via mem_principalUnitGroup_iff.
-- c − 1 = (c − a) + (a − 1):
--   ‖c − a‖ = ‖Σ_{i<a}(ξ^i − 1)‖ < 1   (norm_sum_le_of_forall_le_of_nonneg + norm_pi_lt_one)
--   ‖a − 1‖ < 1                         (p ∣ a−1 ⇒ Padic.norm_p · norm_natCast_le_one)
-- ⟹ ‖c − 1‖ ≤ max(…, …) < 1            (norm_add_le_max)
```

Call sites in the project (from Phase 6.0): **K = 1** — `CyclotomicUnits.lean:493`,
inside `cyclo_mem_cycloTower1` (the `𝒰_{n,1}`-membership half of the milestone).

Refactor plan (project-local; **no mathlib PR**):
  1. **Delete the unused `_ha` hypothesis** (`¬ p ∣ a`) from the signature — the
     proof never uses it. Update the single call site `CyclotomicUnits.lean:493`
     (`exact norm_cycloUnit_sub_one_lt_one p ha hn ha1`) to pass one fewer argument
     (`p hn ha1`). This is the one concrete, safe cleanup.
  2. **Keep the lemma** (do not inline): with K = 1 it is borderline-inlinable, but
     the proof is multi-step and feeds a named milestone, so a named helper reads
     better than an 18-line inline block inside `cyclo_mem_cycloTower1`.
  3. **Optional alignment**: where the project's `localUnitsOne` membership is the
     real target (the call site rewrites `mem_localUnitsOne_iff` then applies this
     lemma), consider phrasing the project's one-unit predicate through mathlib's
     `ValuationSubring.principalUnitGroup` / `mem_principalUnitGroup_iff` so the
     `‖x−1‖ < 1` condition is the *same* object mathlib uses — a cross-link, not a
     new lemma. (Cleanup-lane work, not required.)
  4. **Do not open a mathlib PR** for this theorem — its content is mathlib's
     ultrametric + principal-unit API applied to a project-local cyclotomic-unit
     object.

Next action: drop the dead `_ha` binder and fix the one call site; keep the lemma
project-local; optionally cross-link the project's one-unit membership to mathlib's
`principalUnitGroup`. No upstreaming.

**Why not the other buckets (synthesis honesty).**
- *Not YES-add-as-is / YES-but-generalise-first*: Phase 4b found no *missing*
  general form and Phase 4c found no *missing* modern idiom — the general object
  (principal-unit group) is already in mathlib. The only weakening is deleting an
  unused hypothesis, which is housekeeping, not a generalisation worth a PR. The
  statement is also tied to a project-local def in a non-canonical ambient (`ℂ_p`
  rather than `K_n`) and refines a point the source itself glosses.
- *Not NO-mathlib-has-it*: no single mathlib lemma yields `‖cycloUnit p a n − 1‖ <
  1` in ≤1 line; mathlib's `CyclotomicUnits.lean` is entirely multiplicative
  (`Associated`/`IsUnit`), with **no** norm/valuation statement, and
  `mem_principalUnitGroup_iff` is only the abstract characterisation, not the
  cyclotomic instance.
- *BORDERLINE was considered* (K = 1 consumer + the "is an 18-line helper worth
  keeping vs inlining" + "should the project realise this over `K_n` not `ℂ_p`"
  judgment calls). But none of those change the upstream answer — for *mathlib*, the
  evidence is unambiguous: building blocks + abstraction already exist, the instance
  is project-specific, do not upstream. So no question to the user is needed and the
  verdict resolves cleanly to NO-composable.

---

## Next step

Drop the dead `_ha : ¬ p ∣ a` binder (unused in the proof) and update the single
call site `CyclotomicUnits.lean:493` to pass one fewer argument; keep the lemma as a
project-local helper (it backs the `cyclo_mem_cycloTower1` milestone). Optionally,
cleanup-lane: cross-link the project's `localUnitsOne` membership to mathlib's
`ValuationSubring.principalUnitGroup` (`mem_principalUnitGroup_iff`, the `v(x−1) < 1`
one-unit characterisation) so the project's principal-unit condition is mathlib's.
**Do not open a mathlib PR** — the content is mathlib's ultrametric + principal-unit
API applied to a project-local cyclotomic-unit object.
