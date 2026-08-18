# Mathlibable assessment: `PadicLFunctions.Coleman.mem_cycloClosureOne_of_pow_mem`

**Final five-bucket verdict: `NO-composable-from-mathlib`** — but with a project-local
twist: the result is *not* a mathlib-call composition, it is a genuine multi-step proof.
However, every object in its statement (`cycloClosureOne`, `cycloClosure`, `cycloUnits`,
`localUnitsOne`, `zpPow`) is a **bespoke RJW-§11.3 project object with no mathlib
counterpart**, so the theorem cannot enter mathlib in its current form. Its content is a
specialisation, to those bespoke objects, of standard but *un-isolated* p-adic Iwasawa-theory
facts (1-units form a `ℤ_p`-module; a closed `ℤ_p`-submodule is stable under unique
`(p−1)`-th roots because `p−1 ∈ ℤ_p^×`). The **refactor action is: keep it project-local** —
there is nothing to delete or inline, but it is not a mathlib contribution.

- **Kind:** `theorem` (Prop-valued; Phase 4.5 diamond/defeq is therefore n/a).
- **Source:** `projects/PadicLFunctions/PadicLFunctions/Iwasawa/CyclotomicUnits.lean:673`
- **Mode:** A (single declaration), full 10-phase workflow with the 9-channel literature search.

```lean
/-- **`𝒞_{n,1}` is uniquely `(p−1)`-rooted** (RJW lem:global generators 2): a principal unit
`g ∈ 𝒰_{n,1}` whose `(p−1)`-th power lies in the closure `𝒞_{n,1}` lies in `𝒞_{n,1}` itself. -/
theorem mem_cycloClosureOne_of_pow_mem {n : ℕ} {g : ℂ_[p]ˣ}
    (hg : g ∈ localUnitsOne p n) (hgpow : g ^ (p - 1) ∈ cycloClosureOne p n) :
    g ∈ cycloClosureOne p n
```

---

## Phase 0 — Doctor / baseline

```
### Baseline (Phase 0)
- lake build:               build not re-run; reasoned from source (per task build note — the
                            build is stale/slow here; the decl + its full dependency chain were
                            read directly from source, the skill's Phase-0 fallback).
- decl `…mem_cycloClosureOne_of_pow_mem`:  ✓ resolved at CyclotomicUnits.lean:673
- kind:                     theorem
- has sorry:                no (body is a complete term/tactic proof; sibling cleanup reports
                            confirm the file is sorry-free and axiom-clean)
- branch:                   integrate-generalise (NB: not `main`)
- module docstring summary: RJW §11.3 — the global cyclotomic units 𝒟_n and their local
                            closures 𝒞_{n,1}, all built inside ℂ_[p].
```

Dependency chain read directly from source:

- `cycloClosureOne p n := cycloClosure p n ⊓ localUnitsOne p n` (`CyclotomicUnits.lean:218`)
- `cycloClosure p n := (cycloUnits p n).topologicalClosure ⊓ localUnits p n` (`:210`)
- `cycloUnits p n := Subgroup.closure (cycloGenSet p n) ⊓ globalUnits p n` (`:182`)
- `localUnitsOne p n` = principal local units `{u | u ∈ localUnits p n ∧ ‖(u:ℂ_[p]) − 1‖ < 1}`
  (`LocalUnits.lean:71`); `mem_localUnitsOne_iff` is `Iff.rfl` (`:96`)
- `zpPow p y a` = the `ℤ_[p]`-power `y^a` of a 1-unit, built from mathlib's
  `PadicInt.addChar_of_value_at_one` (the binomial series) (`LocalUnits.lean:170`)
- helper `zpPow_mem_cycloUnits_topologicalClosure` (`CyclotomicUnits.lean:631`): the
  topological closure is `zpPow`-closed.
- `PadicInt.norm_natCast_p_sub_one` (mathlib): `‖(p−1 : ℤ_[p])‖ = 1`, hence `p−1 ∈ ℤ_[p]^×`.

## Phase 1 — Comprehend

### Statement (Phase 1)

`mem_cycloClosureOne_of_pow_mem` is a **theorem** stating the following:

> Let `p` be prime and `n ≥ 0`. Inside the units `ℂ_[p]^×` of the completed algebraic closure
> of `ℚ_p`, let `g` be a *principal* unit (`g ≡ 1 mod 𝔭_n`, i.e. `‖g − 1‖ < 1`, so `g ∈ 𝒰_{n,1}`).
> If the `(p−1)`-th power `g^{p−1}` lies in the closure `𝒞_{n,1}` (the p-adic closure of the
> cyclotomic units `𝒟_n`, intersected with the principal local units), then `g` itself lies
> in `𝒞_{n,1}`.

In a phrase: **the closure `𝒞_{n,1}` is uniquely `(p−1)`-rooted** — closed under taking the
unique `(p−1)`-th root of its elements. This is RJW's "lem:global generators 2" / the
`(p−1)`-rootedness layer; it is the `ℤ_p`-module structure of the closure being used to divide
an exponent that is a `ℤ_p`-unit.

Variables / typeclasses (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the residue characteristic.
- `n : ℕ` — the level of the cyclotomic tower (`F_n = ℚ(μ_{p^n})`).
- `g : ℂ_[p]ˣ` — a unit of `ℂ_[p] = ℂ_p`, the completion of an algebraic closure of `ℚ_p`.

Hypotheses (Lean side):
- `hg : g ∈ localUnitsOne p n` — `g` is a principal local unit (gives `‖g − 1‖ < 1` and the
  local-unit membership).
- `hgpow : g ^ (p - 1) ∈ cycloClosureOne p n` — its `(p−1)`-th power is in the closure.

Conclusion (math): `g ∈ 𝒞_{n,1}`.
Conclusion (Lean): `g ∈ cycloClosureOne p n`.

**Proof shape (5 substantive steps, all genuine reasoning):**
1. `hgc : ‖g − 1‖ < 1` from `hg` (via `mem_localUnitsOne_iff`).
2. `hgpowclos : g^{p−1} ∈ (𝒟_n)⁻` — project the `cycloClosureOne` membership through two `⊓`s.
3. `p−1 ∈ ℤ_[p]^×` (`PadicInt.isUnit_iff` + `PadicInt.norm_natCast_p_sub_one`); take its
   left-inverse `c`.
4. `hgeq : (g:ℂ_[p]) = zpPow (g^{p−1}) c` — the **unique `(p−1)`-th root via the binomial
   `ℤ_p`-action**, using `zpPow_natCast`, `zpPow_mul`, `mul_comm`, `c·(p−1) = 1`.
5. Reassemble the three `⊓`-components of `𝒞_{n,1}`: the closure component from
   `zpPow_mem_cycloUnits_topologicalClosure` applied to step 4, the local + principal
   components inherited directly from `hg`.

## Phase 2 — Preliminary checks (size + one-line)

### Size classification (Phase 2a)

Verdict: **SMALL** (borderline). Reason: it is a *helper lemma* inside the §13 closure layer —
not a new structure, not named after a person/place, and not a top-level "Main result". It is,
however, a load-bearing node: both `wGamma_mem_cycloTower1` and `galNCU_wGamma_mem_cycloTower1`
(the cyclotomic-tower membership inputs to the Iwasawa main theorem) call it directly. Recorded
SMALL for framing; literature width is EXHAUSTIVE regardless.

### One-line check (Phase 2b)

n/a — kind is `theorem`, not a `def`/`abbrev`/`structure`. (Proof body is multi-line; not a
one-liner. Skipped.)

## Phase 3 — Literature search (EXHAUSTIVE, 9-channel protocol)

The concept was split into two layers for searching: (L1) the *named-source* form — RJW's
"global generators 2" lemma about the closure `𝒞_{n,1}`; and (L2) the *abstract mechanism* —
a closed `ℤ_p`-submodule of the principal units is stable under unique `n`-th roots when `n`
is a `ℤ_p`-unit (here `n = p−1`, a unit since `p−1 ≡ −1 mod p`).

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                                              | Hit? | Standard form found | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | principal units local field topological closure Z_p-module cyclotomic units Iwasawa (p−1)-th root                                  | partial | 1-units of a local field form a `ℤ_p`-module; cyclotomic units are closed `ℤ_p`-submodules in Iwasawa theory | Iwasawa-memoir notes (AMS), jtnb.1284 "semi-local units mod cyclotomic units", Ouyang's *Introduction to Iwasawa Theory* — all treat the `ℤ_p`-module structure as standard background; none isolate the `(p−1)`-rooting implication. |
|  2 | WebSearch (general form / mechanism) | principal 1-units local field Z_p module roots invertible exponent unique root closed subgroup                                  | partial | 1-units = `ℤ_p`-module; closed sub-`ℤ_p`-modules; `p`-power roots | Conrad notes (unit theorem), Crew *Local Class Field Theory*, arXiv:1612.04549 (formal groups/Tate cohomology), arXiv:1103.1125 (semi-local units as `ℤ_p[G]`-modules). Mechanism is textbook; the packaged implication is not a named lemma. |
|  3 | WebSearch (named-source / aliases) | Rodrigues Jacinto Williams "introduction to p-adic L-functions" cyclotomic units closure generators lemma global generators        | yes  | confirms RJW = Rodrigues Jacinto & Williams, *An introduction to p-adic L-functions*, arXiv:2309.15692 / Essential Number Theory 4(1) (2025); §11.3 "Cyclotomic units and Iwasawa's theorem", §12.4 "Generators for the local cyclotomic units" | This Lean theorem is the formalisation of RJW's lem:global generators 2 / the `(p−1)`-rootedness step of LemmaGeneratorCinfty1. It is an **in-proof step of an expository paper**, not a standalone named theorem elsewhere in the literature. |
|  4 | ChatGPT MCP                      | (would ask: "standard form + generality + historical evolution of: closure of cyclotomic units as a `ℤ_p`-module being stable under unique `(p−1)`-th roots") | n/a  | —                   | **ChatGPT MCP not configured in this environment** (not surfaced as an available tool). Recorded n/a; the WebSearch channels at three generality levels + WebFetch on the primary source cover the same ground. |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/`                                            | n/a  | (no references dir) | Both `.mathlib-quality/references/` and the gitignored `refs/` symlink are **absent** in this checkout — recorded n/a with reason. The source paper is identified anyway (channel 3). |
|  6 | nLab                             | principal units / one-units local field p-adic `ℤ_p`-module structure logarithm                                                    | partial | 1-units `1 + 𝔪` form a `ℤ_p`-module via the binomial/`exp`–`log` isometry | nLab has no dedicated page for this exact implication; the `ℤ_p`-module structure of 1-units is the standard ambient fact. |
|  7 | nCatLab (categorical)            | (same query, categorical framing)                                                                                                   | n/a  | —                   | Not a categorical concept — a concrete statement about a specific topological group of `p`-adic units. Recorded n/a with reason. |
|  8 | Stacks Project (alg geom)        | (would search "cyclotomic units", "principal units closure")                                                                        | n/a  | —                   | Not an algebraic-geometry / scheme-theoretic concept; the Stacks Project does not cover `p`-adic Iwasawa cyclotomic-unit closures. Recorded n/a with reason. |
|  9 | MathOverflow / Math.StackExchange | (covered via the WebSearch hits in #1/#2) — closed `ℤ_p`-submodule unique `n`-th root, `n` a unit                                  | partial | confirms the mechanism is folklore | Surfaced via channels 1–2 (Conrad, Crew, arXiv profinite/pro-`p` notes). The "unique root when the exponent is a unit" is treated as immediate; no standalone Q&A isolates it. |
| 10 | recent arXiv (last 5 years)      | p-adic logarithm on principal units; image of `log_p`; `ℤ_p`-module of 1-units                                                      | yes (context only) | `log_p` is an isometry `1 + 𝔪 ≅ 𝔪` for low ramification; principal local units form a `ℤ_p`-module | arXiv:1904.09850, arXiv:1907.06437 (image of `p`-adic log on principal units), arXiv:math/0512015 ("A Note on a result of Iwasawa"), arXiv:1701.06857. All reuse the `ℤ_p`-module structure freely as background; none state the `(p−1)`-rooting implication as a result. |

Protocol pass check:
- WebSearch ran **3 distinct queries** at different generality levels (specific form #1, abstract mechanism #2, named-source #3). ✓
- ChatGPT MCP: **n/a** with reason (not configured here). The intended query is recorded. ✓
- Local references: **n/a** with reason (dirs absent). ✓
- nLab: checked (#6). ✓
- Stacks / nCatLab / MathOverflow / arXiv: each checked or `n/a` with a reason (#7–#10). ✓
- WebFetch on the primary source (MSP published PDF, arXiv:2309.15692) attempted: the §11–12
  body text did not extract from the PDF (only the table of contents / section titles were
  recovered, confirming §11.3 + §12.4 exist). The prior sibling report
  (`…one_add_mul_derivative_logSeriesAt.md`) records the same arXiv-PDF extraction limitation.

### Literature summary (Phase 3)

Concept identified as: **the `(p−1)`-rootedness of the local closure of cyclotomic units** —
RJW "lem:global generators 2" / the closure-is-a-`ℤ_p`-module layer of LemmaGeneratorCinfty1
(arXiv:2309.15692, §12.4). The underlying mechanism is the standard fact that the principal
1-units of a `p`-adic field form a `ℤ_p`-module (binomial `ℤ_p`-power / `exp`–`log` isometry),
so a *closed* sub-`ℤ_p`-module is stable under multiplication by `ℤ_p`-units; since `p−1 ∈ ℤ_p^×`,
the unique `(p−1)`-th root `(g^{p−1})^{(p−1)⁻¹}` of a closure element stays in the closure.

Sources agree on the standard form: **yes** for the *ingredients* (`ℤ_p`-module structure of
1-units; closure is a closed `ℤ_p`-submodule; `p−1` is a unit). **No** source states this exact
*packaged implication* as a named, reusable theorem — it is universally an in-proof step.

Most general standard form: for a complete `p`-adic field `K` with ring of integers having
principal units `1 + 𝔪`, any closed `ℤ_p`-submodule `M ≤ 1 + 𝔪`, and any `m ∈ ℤ_p^×`:
`g ∈ 1 + 𝔪`, `g^m ∈ M ⟹ g ∈ M` (because `g = (g^m)^{m⁻¹}` and `M` is `ℤ_p`-stable and closed).

Generality dimensions where the literature varies:
- **Ambient field:** the literature states it for finite extensions of `ℚ_p` (local fields);
  the project works inside `ℂ_p` (the *completed algebraic closure*), restricting to the
  level-`n` local units `𝒰_n`. Same content; different (broader, non-locally-compact) ambient.
- **The submodule:** literature uses generic closed `ℤ_p`-submodules / semi-local units mod
  cyclotomic units; the project specialises to `𝒞_{n,1}` (the closure of cyclotomic units).
- **The exponent:** stated for a general `ℤ_p`-unit; the project uses the specific `p−1`.

Disagreement with the literature: **none** — the project's form is a faithful specialisation
of the standard mechanism to its bespoke objects.

## Phase 4 — Generality analysis

### 4a. Generality status table — `mem_cycloClosureOne_of_pow_mem`

Literature-standard form (from Phase 3): for any complete `p`-adic field, any **closed
`ℤ_p`-submodule** `M` of the principal 1-units, and any `m ∈ ℤ_p^×`:
`g^m ∈ M ⟹ g ∈ M`.

| # | Parameter / hypothesis             | Current Lean form                       | Literature-standard form                          | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------------------|-----------------------------------------|---------------------------------------------------|---------------------|----------------------------------|
| 1 | ambient `ℂ_[p]ˣ`, level `n`        | units of `ℂ_p`, RJW level-`n` machinery | principal units `1 + 𝔪` of any complete `p`-adic field | yes (in principle) | the proof uses only: `‖g−1‖<1`, the `zpPow` `ℤ_p`-action, and that the target is a `zpPow`-closed subgroup. None of that is special to `ℂ_p` or to level `n`. **But** the *generalised statement would be about a different, mathlib-level object* (a generic closed `ℤ_p`-submodule), not about `cycloClosureOne` — see Phase 4c / Phase 5. |
| 2 | `hgpow : g^{p−1} ∈ cycloClosureOne p n` | membership in the bespoke `𝒞_{n,1}` | membership in a generic closed `ℤ_p`-submodule `M` | yes (abstract `M`) | the only property of `𝒞_{n,1}` used is that its `(𝒟_n)⁻` component is `zpPow`-closed (the helper `zpPow_mem_cycloUnits_topologicalClosure`) plus the inherited `⊓`-components. Generalising replaces `𝒞_{n,1}` with "any closed subgroup closed under `zpPow`". |
| 3 | exponent `p − 1`                   | the natural number `p−1`                | any `m ∈ ℤ_p^×`                                   | yes                 | the proof uses `p−1` only through `IsUnit ((p−1:ℕ):ℤ_[p])` and its inverse `c`. It generalises verbatim to any `m` with `IsUnit (m:ℤ_[p])`. |
| 4 | `g : ℂ_[p]ˣ` (a unit)              | bundled unit                            | element of `1 + 𝔪`                               | NO (cosmetic only)  | the unit packaging is just bookkeeping for the multiplicative group; not a genuine generality axis. |

### 4b. Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** — *but only when re-aimed at a
generic closed `ℤ_p`-submodule object that does not exist in mathlib or the project.*

Number of weakening opportunities found: K = 3 (ambient field; bespoke `𝒞_{n,1}` → abstract
closed `ℤ_p`-submodule; `p−1` → arbitrary `ℤ_p`-unit). All three, however, point at a *general
lemma about a different object* — they do **not** give a better statement of *this* lemma about
`cycloClosureOne`. Within the project's object vocabulary the form is already as general as it
can be (it is a fact about `𝒞_{n,1}` specifically, used at exactly that type).

Proposed restatement (the general form the weakenings point to):

```lean
-- A genuinely mathlib-level lemma about ANY closed Z_p-stable subgroup of the 1-units:
theorem mem_of_pow_mem_of_zpPowClosed {M : Subgroup ℂ_[p]ˣ}
    (hMclosed : ∀ {y : ℂ_[p]ˣ} (a : ℤ_[p]) {x : ℂ_[p]ˣ},
        ‖(y:ℂ_[p]) - 1‖ < 1 → y ∈ M → (x:ℂ_[p]) = zpPow p (y:ℂ_[p]) a → x ∈ M)
    {g : ℂ_[p]ˣ} (hgc : ‖(g:ℂ_[p]) - 1‖ < 1) {m : ℕ} (hm : IsUnit ((m:ℕ):ℤ_[p]))
    (hgpow : g ^ m ∈ M) : g ∈ M := by sorry
```

Cost of restatement: **CHEAP–MODERATE** — the proof body would be essentially unchanged.
**BUT** this restatement is the wrong target for *this skill's verdict*, because the right home
for `mem_of_pow_mem_of_zpPowClosed` is still the project (it mentions `ℂ_[p]`, `ℤ_[p]`, and the
project's `zpPow` — none of which exist in mathlib). See Phase 5: there is no mathlib object to
re-aim at, so the weakening is an *internal-refactor* opportunity, not a mathlib-contribution
opportunity. This is why the verdict lands at NO-composable-from-mathlib rather than
YES-but-generalise-first (the generalised statement is *also* not mathlib material).

### 4c. Modern mathlib-idiom restatement — the Bourbaki 2.0 check

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses? | no | — | hypotheses are already typeclass-driven (`Fact p.Prime`); `g`'s principality is a genuine hypothesis, not a missing instance. |
|  2 | sequences/metric → filters/nets/topology? | no | — | the topology is already used abstractly (`topologicalClosure`, the density-of-ℕ-in-ℤ_p argument lives in the helper). No sequence-to-filter upgrade available. |
|  3 | construct an object → universal-property class? | no | — | no object is constructed; it is an implication about membership. |
|  4 | set-with-closure-predicate → bundled substructure? | partial | the abstract `M` form (Phase 4b) bundles "closed + `zpPow`-stable" — but as shown, that bundled object is *project-local*, not mathlib. | (project-internal only) |
|  5 | vector-space/metric/field-specific → modules/(semi)ring? | partial | the underlying "uniquely-divisible-by-units module → root membership" is `RootableBy`-flavoured (`Mathlib/GroupTheory/Divisible.lean`). But the project's group is `ℂ_[p]ˣ` with a `ℤ_[p]`-power that is NOT a mathlib `Module`/`RootableBy` instance (see Phase 5). | would need a `ℤ_p`-`Module`/`RootableBy` structure on 1-units in mathlib first — which does not exist. |
|  6 | 1-categorical → higher-categorical? | no | — | not categorical. |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary monoid/group? | yes | exponent `p−1 : ℕ` → `m ∈ ℤ_p^×` (already in 4b) | would compose with the project's `zpPow` `ℤ_p`-action API — but, again, that API is project-local. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for a *mathlib* contribution). The honest assessment: the
generalisations of Phase 4b/4c are real *project-internal* refactors (abstract the closed
`zpPow`-stable subgroup; let the exponent be any `ℤ_p`-unit), and the abstract mechanism is
morally the mathlib `RootableBy` / divisible-module story. **But** the only way it becomes a
*mathlib* statement is after mathlib gains (a) the field `ℂ_p`, (b) the `ℤ_p`-power `zpPow`
of 1-units / a `ℤ_p`-`Module` structure on principal units, and (c) a "closed `ℤ_p`-submodule
is stable under unit-exponent roots" lemma. Items (a)–(c) are themselves separate, large,
upstream questions — none is this theorem. One-line reason this is not a modernisation move:
*the contemporary form lives over objects mathlib does not have, so re-stating it is internal
project work, not a mathlib PR.*

## Phase 4.5 — Diamond / defeq risk

n/a — declaration kind is `theorem` (Prop-valued). No definitional equalities or
typeclass-search paths are introduced.

## Phase 5 — Mathlib search

Read `references/mathlib-search.md` (five-method protocol). Searched **both** the user's form
(about `cycloClosureOne`) and the literature-standard / abstract form (closed `ℤ_p`-submodule
stable under unit-exponent roots).

### Mathlib search-status: `mem_cycloClosureOne_of_pow_mem`

```
[A] Lean-Finder       "principal unit p-adic field, (p-1)-th power in closed subgroup implies
                       in subgroup"; "closed Z_p-submodule stable under roots"   →  n/a in this
                       environment (no Lean-Finder MCP surfaced). Substituted by WebSearch
                       channel for the mathlib4 docs (RootableBy) + direct grep [D].
[B] Loogle            (type patterns) `_ ^ _ ∈ _ → _ ∈ _` over `Subgroup`;
                       `Subgroup.topologicalClosure` + `pow`;  `RootableBy _ _`   →  no hit for
                       the implication shape; `RootableBy.surjective_pow` is the closest
                       primitive (whole-group surjectivity of `x ↦ x^n`, not a closed-subgroup
                       membership transfer).
[C] LeanSearch        "if the (p-1)th power of a principal unit lies in the closure of the
                       cyclotomic units then the unit lies in the closure"        →  no hit;
                       no mathlib statement mentions cyclotomic-unit closures or ℂ_p units.
[D] Grep mathlib src  `.lake/packages/mathlib/Mathlib`:
                       - `topologicalClosure` + pow/root/divisible/module  →  only
                         `mapClusterPt_atTop_pow_iff_mem_topologicalClosure_zpowers`
                         (closure of `zpowers`, unrelated).
                       - `of_pow_mem` / `pow_mem_.*closure` / `mem_.*_of_pow`  →  only
                         `elemExponent_le_of_pow_mem` (purely inseparable field exponents),
                         `jacobiSum_mem_algebraAdjoin_of_pow_eq_one`,
                         `apply_mem_rootsOfUnity_of_pow_eq_one` — all unrelated.
                       - `RootableBy` →  `Mathlib/GroupTheory/Divisible.lean`
                         (`RootableBy.surjective_pow`), `Haar/Unique.lean`
                         (`measurePreserving_zpow [RootableBy G ℤ]`). Abstract divisibility
                         only; nothing about closed subgroups of `p`-adic 1-units.
[E] Name pattern      `lean_local_search`-style grep for `cyclo`, `closureOne`, `zpPow`,
                       `localUnitsOne`, `ℂ_[p]` in mathlib  →  ZERO hits. Mathlib has no
                       `ℂ_p` (completed algebraic closure of ℚ_p), no `zpPow`, no
                       cyclotomic-unit closure objects. Every object in the statement is
                       project-defined.

Searched for both:
  - the user's current form (about `cycloClosureOne p n`)  →  not in mathlib (objects absent).
  - the literature-standard / abstract form (closed `ℤ_p`-submodule, unit exponent root)  →
    not in mathlib as a packaged lemma; only the unrelated `RootableBy` primitive exists, and
    crucially there is NO `ℤ_p`-`Module`/`RootableBy` instance on principal `p`-adic units to
    re-aim at.

Concluded: **not in mathlib** (all 5 methods exhausted, plus the literature-standard form).
There is no more-general mathlib decl `D'` to re-aim the lemma at — the entire ambient setting
(`ℂ_[p]`, `zpPow`, cyclotomic-unit closures) is project-local. So the re-aim rule does NOT
fire: this is a fact about bespoke project objects, not a redundant restatement of an existing
mathlib lemma.
```

## Phase 6 — Composition check (+ call-sites signal)

### 6.0. Call sites — `mem_cycloClosureOne_of_pow_mem`

```
Internal use count: K = 2  (within the project, NOT counting the declaring file)
External-to-file callers: 1 distinct file (IwasawaProof/Generators.lean)
```

| Caller file:line                              | Usage pattern (one-line excerpt)                                              |
|-----------------------------------------------|-------------------------------------------------------------------------------|
| IwasawaProof/Generators.lean:1734             | `exact mem_cycloClosureOne_of_pow_mem p hg hgpow` (in `wGamma_mem_cycloTower1`) |
| IwasawaProof/Generators.lean:1750             | `refine mem_cycloClosureOne_of_pow_mem p hg ?_` (in `galNCU_wGamma_mem_cycloTower1`) |

(Also referenced in prose in `IwasawaProof/Main.lean:204` and `Generators.lean:1723,1740` —
docstrings, not call sites.)

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?):
  - **(none)** — the `(p−1)`-rooting argument appears only here; both consumers route through
    this single lemma. No site re-derives the `zpPow`-root argument inline.

Composability signal: **K = 2 internal uses, both in the main Iwasawa-theorem proof chain, no
inline re-derivation.** Per the Phase-6.0.1 table this is a "real API" pattern leaning toward a
YES bucket *if the statement were mathlib material*. It is genuinely used and genuinely
factored — it is NOT a dead one-off or a bypassed wrapper. The reason it is not a mathlib YES is
purely that its objects are project-local (Phase 5), not that it is redundant.

### Composition check (Phase 6)

Can `mem_cycloClosureOne_of_pow_mem` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: `exact RootableBy.something …` / divisible-module specialisation.
  - Mathlib decls used: `RootableBy.surjective_pow`, `Subgroup.topologicalClosure`.
  - Result: **fails**. `RootableBy` is about surjectivity of `x ↦ x^n` on a *whole* group with
    a registered instance; there is no `RootableBy` (nor `ℤ_p`-`Module`) instance on `ℂ_[p]ˣ`
    or on the 1-units, and no lemma transferring root-membership into a *closed subgroup*. The
    `(p−1)`-th root here is built by hand from the project's `zpPow` binomial action.
  - Notes: the genuine work — `g = zpPow (g^{p−1}) (p−1)⁻¹` and "the closure is `zpPow`-closed"
    — is not available from mathlib at all.

Attempt 2: direct unfold + reassembly.
  - The body is: extract one of three `⊓` components, build the root via `zpPow_mul` +
    `zpPow_natCast` (project lemmas), apply the project helper
    `zpPow_mem_cycloUnits_topologicalClosure`, reassemble three components. That is **5 genuine
    `have`-steps with real reasoning between them**, using **project** lemmas, not mathlib calls.
  - Result: **fails** as a "mathlib composition" — it is a proof in disguise (per the Phase-6b
    heuristics, "multiple `have`s with non-trivial reasoning between" = NO).

Conclusion: **NOT-COMPOSABLE** from mathlib (it is composable only from *project* primitives,
which is what the proof already does — and those project primitives are themselves not mathlib).

> Note on bucket nomenclature: the canonical `NO-composable-from-mathlib` is a ≤3-line *mathlib*
> composition. Here the composition exists but only from *project* lemmas. The verdict lands at
> NO-composable in the sense that **the result is not standalone mathlib material** — it is a
> project-internal consequence of project-internal API (`zpPow`, the `zpPow`-closed closure,
> `cycloClosureOne`). The refactor action is correspondingly "keep project-local", not "inline
> a mathlib one-liner". This is spelled out in the Phase-7 WHY paragraph as required by the gate.

## Phase 7 — Verdict

## Verdict: `PadicLFunctions.Coleman.mem_cycloClosureOne_of_pow_mem`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the ingredients (1-units are a `ℤ_p`-module; closed
  `ℤ_p`-submodules; `p−1 ∈ ℤ_p^×`) are textbook; the *packaged implication* is an in-proof step
  of RJW arXiv:2309.15692 §12.4 (lem:global generators 2), never a named reusable theorem.
- Generality analysis (Phase 4): STRICTLY NARROWER *only when re-aimed at a generic closed
  `ℤ_p`-submodule* — but that generalised statement is itself project-local (it still mentions
  `ℂ_[p]`, `ℤ_[p]`, `zpPow`), so it is not a mathlib target. Within the project's vocabulary the
  form is appropriately general. Phase 4c: no *mathlib* modernisation move.
- Mathlib search (Phase 5): not in mathlib; **no more-general mathlib `D'` to re-aim at** —
  `ℂ_p`, `zpPow`, and cyclotomic-unit closures are all absent from mathlib. `RootableBy` is the
  nearest primitive and does not apply (no instance, no closed-subgroup transfer lemma).
- Composition check (Phase 6): NOT-COMPOSABLE from mathlib (the real `(p−1)`-rooting argument
  uses project-only `zpPow` machinery; it is a genuine 5-step proof, not a ≤3-call composition).
  Call sites: K = 2, both in the Iwasawa main-theorem chain, no inline re-derivation.

**Rationale:**

`mem_cycloClosureOne_of_pow_mem` is a faithful, well-factored formalisation of a standard
Iwasawa-theory step: the local closure `𝒞_{n,1}` of the cyclotomic units is a `ℤ_p`-module, so
it is stable under the unique `(p−1)`-th root, since `p−1` is a `ℤ_p`-unit. The mathematics is
classical and the underlying mechanism (binomial `ℤ_p`-action on 1-units / `exp`–`log`
isometry, closed sub-`ℤ_p`-modules) is treated as background folklore across the literature
(Iwasawa's memoir notes, Conrad, Crew, arXiv:1904.09850/1907.06437). Crucially, however, **every
object in the statement is a bespoke project construction** — `cycloClosureOne`, `cycloClosure`,
`cycloUnits` (all judged NO-composable / BORDERLINE in their own sibling assessments),
`localUnitsOne`, and the project-local `zpPow` — none of which exists in mathlib, which has no
`ℂ_p`, no `ℤ_p`-power of 1-units, and no cyclotomic-unit-closure machinery. The Phase-5 search
turned up no more-general mathlib decl to specialise from, so the re-aim rule does not fire.

The result is therefore **not standalone mathlib material in any form**: not as-is (its objects
are project-local), not after generalisation (the general "closed `ℤ_p`-submodule is stable
under unit-exponent roots" statement is *also* over project-local objects), and not as a
trivial mathlib composition (the `(p−1)`-rooting is a genuine 5-step proof using only project
API). It is a correctly-placed, genuinely-used (K = 2 consumers in the main Iwasawa proof)
project lemma. The honest bucket is NO-composable-from-mathlib, read as "this belongs in the
project, not mathlib", with the caveat that the composition is from *project* primitives rather
than mathlib ones.

**WHY not (refactor-actionable detail):**

Mathlib does **not** have the building blocks at the right altitude. It has the abstract
divisibility primitive `RootableBy` / `RootableBy.surjective_pow`
(`Mathlib/GroupTheory/Divisible.lean`) and the closure-of-`zpowers` lemma
`mapClusterPt_atTop_pow_iff_mem_topologicalClosure_zpowers`
(`Mathlib/Topology/Algebra/Group/SubmonoidClosure.lean`), but neither composes to give this:
there is no `ℤ_p`-`Module`/`RootableBy` instance on the principal `p`-adic units, no field
`ℂ_p`, and no lemma transferring unit-exponent-root membership into a *closed subgroup*. The
genuine content lives in the **project's own** `zpPow` API
(`PadicLFunctions/Iwasawa/LocalUnits.lean`): `zpPow_natCast`, `zpPow_mul`,
`norm_zpPow_sub_one_lt_one`, and the helper `zpPow_mem_cycloUnits_topologicalClosure`
(`CyclotomicUnits.lean:631`, which encodes "the closure is `zpPow`-closed").

Mathlib building blocks (such as they are):
`Mathlib.GroupTheory.Divisible.RootableBy` (+ `RootableBy.surjective_pow`),
`Mathlib.Subgroup.topologicalClosure`, `PadicInt.norm_natCast_p_sub_one`,
`PadicInt.isUnit_iff` — but these only cover the trivial top of the argument
(`p−1 ∈ ℤ_p^×`); the load-bearing `zpPow`-rooting is project-only.

Composition sketch (NOT a mathlib ≤3-liner — this is what the proof already does, in the
project, and is why the lemma stays project-local):

```lean
-- (project) g = zpPow (g^{p−1}) c with c = (p−1)⁻¹ in ℤ_p, then push through the
-- zpPow-closed closure and reassemble the three ⊓-components of 𝒞_{n,1}:
--   zpPow_mem_cycloUnits_topologicalClosure p hypowc hgpowclos c hgeq  -- closure component
--   ((mem_localUnitsOne_iff p).1 hg).1                                  -- local component
--   hg                                                                  -- principal component
```

Call sites in the project (from Phase 6.0): **K = 2** — `wGamma_mem_cycloTower1`
(`Generators.lean:1734`) and `galNCU_wGamma_mem_cycloTower1` (`Generators.lean:1750`).

**Refactor plan:** **none against mathlib** — there is nothing to delete or inline, because the
result is not a mathlib duplicate or a mathlib one-liner. Keep `mem_cycloClosureOne_of_pow_mem`
in the project at its current location; both call sites continue to use it as-is. The *only*
optional internal refactor (independent of mathlib) is the Phase-4b generalisation: extract a
`mem_of_pow_mem_of_zpPowClosed` lemma over an abstract `zpPow`-closed `Subgroup ℂ_[p]ˣ` with an
arbitrary `ℤ_p`-unit exponent, and derive both `mem_cycloClosureOne_of_pow_mem` and the prose
argument in `galNCU_wGamma_mem_cycloTower1` from it. That is a project-internal cleanup, not a
mathlib contribution, and is out of scope for this verdict.

### Verdict gate check

- Required evidence for NO-composable-from-mathlib: Phase 5 building-blocks list ✓; Phase 6
  composition analysis ✓ (concluded NOT a mathlib composition; the project composition sketch is
  shown). Phase 6.0 call-sites table present with K and inline-derivation fields filled ✓.
- The WHY paragraph names the concrete mathlib altitude gap (no `ℤ_p`-`Module`/`RootableBy` on
  1-units; no `ℂ_p`; no closed-subgroup root-transfer lemma) and gives the refactor plan
  ("keep project-local; optional internal abstraction"), at refactor-actionable detail ✓.
- Not YES-add-as-is: Phase 5 found the objects are project-local and Phase 6 is NOT a standalone
  novel mathlib statement (the general form is also non-mathlib) ✓.
- Not NO-mathlib-has-it: Phase 5 did not find an existing mathlib decl ✓.
- Cost was not used as the deciding factor ✓.

---

## Next step

Keep `mem_cycloClosureOne_of_pow_mem` **in the project** — it is not a mathlib contribution
(every object in its statement is project-local; there is no mathlib counterpart to specialise
from and no ≤3-call mathlib composition). No deletion, no inlining. Optional, mathlib-independent
internal cleanup: factor out an abstract `mem_of_pow_mem_of_zpPowClosed` lemma (closed
`zpPow`-stable `Subgroup ℂ_[p]ˣ`, arbitrary `ℤ_p`-unit exponent) and derive the two consumers
(`wGamma_mem_cycloTower1`, `galNCU_wGamma_mem_cycloTower1`) from it — but this stays in the
project. If mathlib ever gains `ℂ_p` + a `ℤ_p`-`Module` structure on principal `p`-adic units +
a "closed `ℤ_p`-submodule is stable under unit-exponent roots" lemma, revisit then (those are
separate large upstream questions, not this theorem).
