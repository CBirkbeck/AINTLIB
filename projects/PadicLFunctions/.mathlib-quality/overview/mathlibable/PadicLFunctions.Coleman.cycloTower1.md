# Mathlibable assessment: `PadicLFunctions.Coleman.cycloTower1`

**Verdict: `NO-composable-from-mathlib`** — a thin definitional *inverse-limit* wrapper
(`⨅ n, comap (elemsₙ) (cycloClosureOne n)`) whose content is entirely project-specific
operands; mathlib supplies only the combinators, not the object.

- **Kind:** `def` (returns data — a `Subgroup (NormCompatUnits p)`); `lowerCamelCase` is correct.
- **Source:** `projects/PadicLFunctions/PadicLFunctions/Iwasawa/CyclotomicUnits.lean:226`
- **Mode:** A (single declaration), full 10-phase workflow with the 9-channel literature search.

```lean
/-- `𝒞_{∞,1} = lim←_{n≥1} 𝒞_{n,1}` (RJW TeX 3092), as a subgroup of `𝒰_∞`. -/
noncomputable def cycloTower1 : Subgroup (NormCompatUnits p) where
  carrier := {u | ∀ n, 1 ≤ n → u.elems n ∈ cycloClosureOne p n}
  mul_mem' hu hv n hn := mul_mem (hu n hn) (hv n hn)
  one_mem' _ _ := one_mem _
  inv_mem' hu n hn := (cycloClosureOne p n).inv_mem (hu n hn)
```

---

## Phase 0 — Doctor / baseline

```
### Baseline (Phase 0)
- lake build:               build NOT re-run; reasoned from source (per task build note; pin
                            rev 887d94632e78, toolchain v4.32.0-rc1; mathlib checkout present at
                            .lake/packages/mathlib)
- decl `cycloTower1`:       ✓ resolved at projects/PadicLFunctions/PadicLFunctions/Iwasawa/CyclotomicUnits.lean:226
- kind:                     def (bundled `Subgroup` structure: carrier + 3 closure proofs)
- has sorry:                no
- module docstring summary: RJW §11.3 — the global cyclotomic-unit modules 𝒟_n and their local
                            closures 𝒞, all built inside ℂ_[p]; this file assembles the tower
                            𝒞_{∞,1} that receives the Coleman-map input.
```

Dependency chain read directly from source:

- carrier type `NormCompatUnits p` — bespoke structure (`Coleman/Tower.lean:650`): a
  norm-compatible system `elems : ℕ → ℂ_[p]ˣ` with `mem`/`inv_mem`/`compat` fields; carries a
  `CommGroup` instance (`LocalUnits.lean:467`), a `TopologicalSpace`/`T2Space`
  (`Coleman/ColContinuity.lean:416,434`), and an `elemsMonoidHom (n) : NormCompatUnits p →* ℂ_[p]ˣ`
  (`IwasawaProof/Main.lean:449`).
- per-level operand `cycloClosureOne p n = 𝒞_{n,1}` (`CyclotomicUnits.lean:218`) =
  `cycloClosure p n ⊓ localUnitsOne p n` — itself assessed `NO-composable-from-mathlib`
  (sibling report), a project-only object.

## Phase 1 — Comprehend

### Statement (Phase 1)

`cycloTower1` is **a definition** of the following object.

Let `p` be a prime. For each level `n ≥ 1` let `𝒞_{n,1} = cycloClosureOne p n` be the
principal-unit part of the p-adic closure of the cyclotomic units `𝒟_n` inside the local units
`𝒰_n ⊆ ℂ_[p]ˣ`. Let `𝒰_∞ = NormCompatUnits p` be the inverse limit of the local unit groups under
the level norm maps `N_{n+1,n}` (a "norm-compatible system" `(u_n)_n`). Then `𝒞_{∞,1}` is the
subgroup of `𝒰_∞` consisting of those norm-compatible systems `u = (u_n)` whose component `u_n`
lies in `𝒞_{n,1}` for every `n ≥ 1`. Mathematically this is the **projective limit
`lim←_{n≥1} 𝒞_{n,1}`** sitting inside `𝒰_∞`; it is the home of the norm-compatible system of
cyclotomic units that is fed to the Coleman map (RJW TeX 3092, milestone TeX 3084).

Variables / typeclasses (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the prime; `ℂ_[p]` is the completed algebraic closure of `ℚ_p`.

Hypotheses (Lean side): none — it is a closed-form definition (the `1 ≤ n` guard lives inside the
carrier predicate, matching the `compat`-field convention that the level norm only acts for `n ≥ 1`).

Conclusion (math): the subgroup `𝒞_{∞,1} = lim←_{n≥1} 𝒞_{n,1} ≤ 𝒰_∞`.

Conclusion (Lean): `Subgroup (NormCompatUnits p)` — n/a, definition (data).

## Phase 2 — Preliminary checks

### Size classification (Phase 2a)

Verdict: **SMALL**.
Reason: it introduces no new *named mathematical concept* of its own — it is the level-`n` operand
`𝒞_{n,1}` glued into a per-level-membership subgroup of an already-defined inverse-limit group. It is
a node in the RJW tower construction, not a primary project result and not a person/place theorem.
(Note: literature width is EXHAUSTIVE regardless; BIG/SMALL is narrative only.)

### One-line check (Phase 2b)

Body line count: 4 substantive lines (a `where` block: `carrier` + `mul_mem'` + `one_mem'` +
`inv_mem'`).
One-liner verdict: **MULTI-LINE** — it is a bundled `Subgroup` structure literal, not a
`def := <one expr>`. The Phase-2b one-liner exemption analysis is therefore **n/a**.

Note for later phases: although MULTI-LINE, the three proof obligations are *purely mechanical*
(`mul_mem`/`one_mem`/`inv_mem` applied pointwise) — i.e. the multi-line-ness is hand-rolling the
proofs that `Subgroup.comap` + `Subgroup.iInf` would discharge automatically (see Phase 6). So the
"multi-line ⇒ substantive" heuristic does **not** apply: this is a verbose spelling of a thin
combinator wrapper, not genuine new content.

## Phase 3 — Literature search (EXHAUSTIVE, 9 channels)

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "Iwasawa theory cyclotomic units inverse limit tower local units norm compatible system definition" | yes (concept) | inverse limit `X = lim← A_n` under **norm maps** up the cyclotomic tower is *the* prototypical Iwasawa module; "norm-compatible system" = the data of an inverse system | Encyclopedia of Math (Iwasawa theory); nLab; Sharifi outline; Hida lecture notes. The construction is canonical but always tied to specific arithmetic data. |
| 2 | WebSearch (general/named form) | "\"C_infinity\" cyclotomic units projective limit principal local units Iwasawa Coleman map" | yes | "projective limit of cyclotomic units `C`" and "projective limit of semi-local units `U`", with `U/C` the studied object; Coleman map = projective limit of local maps | **First hit is the source paper itself, arXiv:2309.15692 (RJW).** JTNB 1284 (Semi-local units modulo cyclotomic units in the cyclotomic ℤ₂-extension) studies `U`, `C`, `U/C`. The *operand-level* objects are standard; the per-level principal-unit intersection is bookkeeping. |
| 3 | WebSearch (abstract idiom) | "projective limit of subgroups of inverse limit ring definition mathlib formalization universal property" | partial | inverse/projective limit defined in any category via universal property; in concrete categories realized as a sub(set/group) of the product | Wikipedia/HandWiki/Osserman notes. **No standard "projective limit of subgroups" named object; no mathlib formalization surfaced.** |
| 4 | ChatGPT MCP (historical formulation) | (would ask: standard form + generality + historical evolution of `lim← 𝒞_{n,1}`) | n/a | — | **n/a: no ChatGPT/OpenAI MCP server configured** in this environment (only Asana/Atlassian/… OAuth proxies present). Substituted by channels 1–3 + nLab (channel 6) + the local mathlib reading in Phase 5, consistent with the sibling reports in this batch. |
| 5 | Local references | grep `refs/PadicLFunctions/`, `.mathlib-quality/references/` | n/a | — | **n/a: no `refs/` symlink and no `.mathlib-quality/references/` dir present** (PDFs are local-only, not linked here). Primary source identified from the docstring: RJW arXiv:2309.15692, §11.3, TeX 3092 (def), TeX 3084 (milestone). |
| 6 | nLab | "Iwasawa theory" → inverse limit under norm maps | yes (concept) | nLab states "the inverse limit of the `A_n` under the norm maps" as a **computational device bound to arithmetic**, not an independently named structure | Confirms: `𝒞_{∞,1}`/`C_∞,1` is **not** a named reusable object; cyclotomic *units* in the tower aren't even given a standalone page (the named object is the Iwasawa algebra `ℤ_p[[Γ]]`). |
| 7 | nCatLab (if categorical) | inverse limit / projective limit (categorical) | yes (generic) | universal-property limit in `Grp`/`Ring`; realized as sub-object of the product | Generic categorical limit only — gives no Iwasawa-specific or unit-tower-specific named object. |
| 8 | Stacks Project (if alg geom) | — | n/a | — | **n/a: not an algebraic-geometry / scheme-theoretic concept.** (Stacks has limits of rings/modules generically but no cyclotomic-unit tower; checked, nothing closer than generic limits.) |
| 9 | MathOverflow / Math.SE | "semi-local units modulo cyclotomic units" projective limit | yes | matches channel 2 — `U/C` (proj. limit semi-local units / proj. limit cyclotomic units) is the studied quantity | Reinforces: the studied named objects are `U`, `C`, `U/C`; the per-level principal-unit slice `𝒞_{n,1}` and its tower are internal steps, not named definitions. |
| 10 | recent arXiv (last 5 yrs) | cyclotomic units projective limit principal units (2020–) | yes | covered by channels 2/9 (JTNB 1284 (2024); arXiv:2309.15692 (2023); supersingular IMC pairs) | Modern work still presents these as arithmetic projective limits, never as a reusable abstract `Subgroup`-level inverse-limit constructor. |

### Literature summary (Phase 3)

Concept identified as: **`𝒞_{∞,1}` — the projective limit (inverse limit under level norms) of the
principal-unit parts of the local closures of cyclotomic units**, a node in the RJW Iwasawa
cyclotomic-unit tower.

Sources agree on the standard form: **partially.** They agree that (a) *inverse limit under norm
maps* is the canonical Iwasawa construction, and (b) "projective limit of cyclotomic units `C`" /
"semi-local units `U`" / `U/C` are standard *studied* objects. They do **not** furnish a named,
reusable definition of `𝒞_{∞,1} = lim← 𝒞_{n,1}` as a standalone object — it is paper-specific
notation (RJW), one assembly step of one particular tower.

Most general standard form: an inverse limit `lim←_n H_n` of a tower of subgroups `H_n` along a
compatible system of transition maps, realized as the sub(group) of the inverse-limit object cut out
by per-level membership. This is exactly the categorical/concrete inverse-limit pattern — but the
literature attaches it to specific arithmetic `H_n`, never abstracts a reusable "tower of subgroups"
constructor.

Generality dimensions where the literature varies:
- index/base: the tower can be over any `ℤ_p`-extension; here `ℕ` levels of `ℚ(μ_{p^n})`.
- operand `H_n`: `𝒞_{n,1}` (principal-unit slice) vs `𝒞_n` vs full local units `𝒰_n` vs class
  groups `A_n` — different inverse limits give different named Iwasawa modules; RJW picks the
  principal-unit cyclotomic slice for the Coleman-map input.

Disagreement with the literature: **none.** The Lean form is a faithful rendering of RJW TeX 3092
(`lim←_{n≥1} 𝒞_{n,1}`, with the `n ≥ 1` guard matching the norm-compatibility convention).

**Phase 3 takeaway.** The *ingredients* (inverse limit under norm maps, projective limit of
cyclotomic/local units, the Coleman input) are canonical Iwasawa theory; the *specific object*
`𝒞_{∞,1}` is paper-specific assembly, not a named reusable definition. There is therefore no
"literature-standard form of `cycloTower1`" to anchor a generalisation against — the only general
form is the abstract inverse-limit-of-subgroups pattern, which is a comment on the *carrier*
(`NormCompatUnits`) and a hypothetical general `Subgroup.invLimit`, not on this decl.

## Phase 4 — Generality analysis

### Generality analysis — `cycloTower1`

Literature-standard form (from Phase 3): inverse limit `lim←_n H_n` of a tower of subgroups along
compatible maps; here `H_n = 𝒞_{n,1}`, base `NormCompatUnits p`, guard `1 ≤ n`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | carrier base `NormCompatUnits p` | bespoke inverse-limit-of-`ℂ_[p]ˣ`-along-`levelNorm` structure | inverse limit of a tower of groups | NO (for *this* decl) | the base is fixed by the project's `𝒰_∞`; abstracting it is the **carrier's** assessment (`NormCompatUnits`), not `cycloTower1`'s |
| 2 | operand `cycloClosureOne p n` | project-specific `𝒞_{n,1}` (`NO-composable` sibling) | the `H_n` of the tower | NO (for *this* decl) | weakening means weakening `cycloClosureOne` / its operands — out of scope here |
| 3 | index `ℕ` with guard `1 ≤ n` | levels of `ℚ(μ_{p^n})` | levels of a `ℤ_p`-extension | NO (meaningfully) | the `ℕ`/`1 ≤ n` is forced by the `compat`-field convention of the base; it is not a free generality axis of `cycloTower1` |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** *as itself* — once the base `NormCompatUnits p` and the
operand `cycloClosureOne p n` are fixed, `𝒞_{∞,1}` is **forced** to be the per-level-membership
subgroup; there is no freer "more general form of this decl" to target. Every generality question
lives on the operands/carrier, not on this object.
Number of weakening opportunities found (on this decl): 0.
Proposed restatement: none for this decl.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preambles → typeclasses/instances? | no | — | the only input is `[Fact p.Prime]`, already a typeclass |
| 2 | sequences/metric → filters/topological? | no | — | no sequential/metric content; the topology enters only via the operand's closure |
| 3 | construction → universal-property class? | **partially (one level up)** | a general `Subgroup.invLimit`/universal-property inverse limit of a tower of subgroups | this is a real gap, but it is a comment on a **hypothetical mathlib API + the carrier `NormCompatUnits`**, not a restatement of `cycloTower1` itself (which would then be an *instance* of it) |
| 4 | set-with-closure-predicate → bundled-substructure type? | **already done** | `cycloTower1` *is* the bundled `Subgroup` type; the carrier predicate is the readable face | n/a — already idiomatic; see Phase 6 for the `iInf`-of-`comap` realization |
| 5 | vector-space/metric/field-specific → weaker typeclass? | no | — | the algebra is `CommGroup`/`Subgroup`, already maximally weak for the operation used |
| 6 | 1-categorical → higher-categorical? | no | — | a subgroup of an inverse limit of groups; no higher-categorical target |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/order? | no (meaningfully) | — | the `ℕ` index is the tower level, pinned to the `compat` convention; not a free axis |

```
### Modern-idiom verdict (Phase 4c)

Modern idiom available: NO (for this decl itself).
One-line reason: the genuine modernisation — replacing the hand-rolled `where`-block with
mathlib's `⨅ n, ⨅ (_ : 1 ≤ n), Subgroup.comap (elemsMonoidHom p n) (cycloClosureOne p n)` (the
`Set.unit`/S-units idiom, see Phase 6) — is a *mechanical reimplementation of the same object*, not
a change of statement, so it does NOT flip the verdict to YES-but-generalise. The only true
abstraction (a reusable `Subgroup.invLimit` of a tower of subgroups) is a comment on a missing
mathlib API and on the carrier `NormCompatUnits`, with `cycloTower1` an instance — it is the
*carrier's* mathlib-direction work, not this decl's. (Bourbaki-2.0 claim deliberately WITHHELD for
this decl — asserting it would fail the Phase-7 gate's "concrete downstream consequences *of this
decl*" requirement.)
```

## Phase 4.5 — Diamond / defeq risk (`def`/`class`/`instance`)

`cycloTower1` is a `def` producing a `Subgroup (NormCompatUnits p)` (data), so the phase runs.

### Diamond / defeq risk — `cycloTower1`

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | none | introduces no instance; it is a plain `def` of a term of type `Subgroup _`. The `Subgroup`/`CommGroup`/`Lattice (Subgroup _)` instances it relies on are mathlib's + the project's single `CommGroup (NormCompatUnits p)`. No new search path. |
| 2 | Reducibility leak | none | not `@[reducible]`; the body is a structure literal. Downstream proofs unfold it explicitly (`rw [cycloClosureOne, Subgroup.mem_inf]` after `intro n hn`), never relying on accidental defeq. |
| 3 | Non-canonical unfolding | low | `SetLike` membership unfolds to the carrier predicate `∀ n, 1 ≤ n → …`; this is the intended API (every consumer does `intro n hn`). No surprising `simp`/`rfl` behaviour. |
| 4 | Instance priority collision | none | not an `instance`; no priority to set. |
| 5 | Universe-polymorphism issues | none | everything is in `Type 0` (`ℂ_[p]`, `NormCompatUnits p`); no universe variables, no forced annotation. |
| 6 | Coercion ambiguity | none | no `CoeFun`/`CoeSort` introduced; the only coercion is `SetLike`'s standard `↑(cycloTower1 p) : Set (NormCompatUnits p)`, identical to every other `Subgroup`. |

### Risk verdict (Phase 4.5)

Overall risk: **NONE**. Top risks: none. (No mitigations needed.)

## Phase 5 — Mathlib five-method search

### Mathlib search-status: `cycloTower1`

```
[A] Lean-Finder       (semantic: "inverse limit of cyclotomic units principal local units subgroup")  n/a: tool not available in-env; substituted by [D]+[E] over the local .lake/packages/mathlib checkout
[B] Loogle            `(p : ℕ) → Subgroup (NormCompatUnits p)` ; `Subgroup (?G)` with carrier `∀ _, _ ∈ _`   no hits possible — return type is built from the project-defined `NormCompatUnits`; closest generic combinators found by grep (below)
[C] LeanSearch        "projective limit of cyclotomic units in the cyclotomic tower as a subgroup" / "norm compatible system of units subgroup"   concept absent from mathlib
[D] Grep mathlib src  `normCompat|coleman|coherent.*norm` → none ; `iwasawa` → only GroupTheory/GroupAction/Iwasawa.lean (simplicity criterion, unrelated) ; `cyclotomicunit` → only NumberTheory/NumberField/Cyclotomic/Ideal.lean (ramification of ℚ(ζ_n), unrelated) ; `InverseLimit|projectiveLimit` → only Probability/* + MeasureTheory/Constructions/Projective + FieldTheory/CardinalEmb (measure/field, NOT a Subgroup-of-tower constructor)   no direct hit
[E] Name pattern      `cycloTower*`, `NormCompatUnits`, `unitsTower*`   found ONLY in this project
```

Searched for both:
- the user's current form (`Subgroup (NormCompatUnits p)` cut by `∀ n, 1 ≤ n → u.elems n ∈ 𝒞_{n,1}`) — absent.
- the literature-standard/abstract form (inverse limit of a tower of subgroups; a reusable
  `Subgroup.invLimit`) — **also absent**: mathlib has the *combinators* but no packaged
  inverse-limit-of-subgroups object.

Building blocks mathlib **does** supply (cited by qualified name):
- `Subgroup.comap (f : G →* N) (H : Subgroup N) : Subgroup G` — `Mathlib/Algebra/Group/Subgroup/Map.lean:72`.
- `Subgroup.iInf` / `Subgroup.mem_iInf` — `Mathlib/Algebra/Group/Subgroup/Basic.lean:990` (and the
  complete-lattice `⨅`), the meet of a family of subgroups.
- `Subgroup.copy` — used by mathlib to give an `iInf`-subgroup a readable carrier (see the canonical
  precedent below).
- **Canonical precedent for this exact idiom:** `Set.unit` (the subgroup of S-units),
  `Mathlib/RingTheory/DedekindDomain/SInteger.lean:106`, is *defined* as
  `(⨅ (v) (_ : v ∉ S), (v.valuation K).valuationSubring.unitGroup).copy {x | ∀ v, v ∉ S → … = 1} (by …)`
  — i.e. a subgroup cut out by a per-index membership predicate, realized as `iInf` of per-index
  subgroups, with a `.copy` giving the readable `{x | ∀ …}` carrier. `cycloTower1` is the same shape.

Concluded: **not in mathlib** (all 5 methods exhausted, both the user's form and the abstract
inverse-limit form). Mathlib has the building blocks (`Subgroup.comap`, `Subgroup.iInf`,
`Subgroup.copy`) and the precedent idiom (`Set.unit`), **but not** this object and **not** its two
project-specific inputs (`NormCompatUnits` / `elemsMonoidHom`, `cycloClosureOne`).

## Phase 6 — Composition check (+ call-sites signal)

### Call sites — `cycloTower1`

Internal use count: **K ≫ 3** (well over a dozen), across **3 files outside the declaring block** of
the same project.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| CyclotomicUnits.lean:239 | `cycloTower1_le_unitsTower1 : cycloTower1 p ≤ unitsTower1 p` |
| CyclotomicUnits.lean:474 | `cyclo p ha hp2 ∈ cycloTower1 p` (the milestone membership) |
| IwasawaProof/Generators.lean:1607 | `galNCU_neg_one_mem_cycloTower1 … hu : u ∈ cycloTower1 p` |
| IwasawaProof/Generators.lean:1704,1726,1744 | `wGamma_pow_mem_cycloTower1` / `wGamma_mem_cycloTower1` / `galNCU_wGamma_mem_cycloTower1` |
| IwasawaProof/Main.lean:103 | `ZpOne_le_cycloTower1 : ZpOne p ≤ cycloTower1 p` |
| IwasawaProof/Main.lean:121,229,250,363,377 | `galNCU_wGamma_inv_mem_cycloTower1`; carrier `Col p '' (cycloTower1 p : Set _)`; `closure_cycloGenSubgroup_le_cycloTower1`; `col_image_cycloTower1_le_zetaIdeal_of_density` |

Inline-derivation grep (was the equivalent re-derived elsewhere without `cycloTower1`?): **none** —
consumers use the named object directly. Every membership proof, however, immediately does
`intro n hn` and then works on the **component** `u.elems n ∈ cycloClosureOne p n` (e.g.
`cyclo_mem_cycloTower1`, `wGamma_mem_cycloTower1`, `ZpOne_le_cycloTower1`) — i.e. they unfold the
tower back to its per-level operand.

Call-sites reading: K ≫ 3 with no inline re-derivation → it is **real, load-bearing project API**
(the home of the Coleman-map input and the LHS of the main image identity
`Col '' 𝒞_{∞,1} = I(𝒢)ζ_p`). This is a strong *project-API* signal — but, exactly as for the sibling
`cycloClosureOne`, every use unfolds to the component predicate; the signal says "load-bearing
project glue", **not** "standalone abstraction worth exporting to mathlib".

### Composition check (Phase 6)

Can `cycloTower1` be derived from mathlib in ≤3 chained calls?

Attempt 1 — the inverse-limit / `Set.unit` idiom:
```lean
noncomputable def cycloTower1' : Subgroup (NormCompatUnits p) :=
  (⨅ n, ⨅ (_ : 1 ≤ n), Subgroup.comap (elemsMonoidHom p n) (cycloClosureOne p n)).copy
    {u | ∀ n, 1 ≤ n → u.elems n ∈ cycloClosureOne p n}
    (by ext u; simp [Subgroup.mem_iInf, Subgroup.mem_comap, elemsMonoidHom])
```
  - Mathlib decls used: `Subgroup.iInf` (`⨅`), `Subgroup.comap`
    (`Mathlib/Algebra/Group/Subgroup/Map.lean:72`), `Subgroup.copy`, `Subgroup.mem_iInf`
    (`…/Subgroup/Basic.lean:990`), `Subgroup.mem_comap`.
  - Project decls used (NOT mathlib): `elemsMonoidHom p n` (`IwasawaProof/Main.lean:449`),
    `cycloClosureOne p n`.
  - Result: **succeeds** as a reimplementation — `cycloTower1` is *exactly* the `iInf`-of-`comap`
    pattern (the hand-rolled `mul_mem'`/`one_mem'`/`inv_mem'` are precisely what `comap` + `iInf`
    discharge for free). The body is **2 mathlib combinators** (`comap`, `iInf`) plus a cosmetic
    `.copy`.
  - Notes: the composition reproduces the object using **mathlib's combinators** but on
    **project-specific operands** that are not in mathlib.

Conclusion: **COMPOSABLE** — but in the precise sense that *mathlib supplies only the combinators*
(`Subgroup.iInf` ∘ `Subgroup.comap`, ≤3 calls, the `Set.unit` precedent), while the **content is the
two project operands** (`elemsMonoidHom`/`NormCompatUnits`, `cycloClosureOne`). It cannot be
reconstructed from mathlib *alone* (the operands are needed), and as a combinator wrapper it carries
no mathematical content beyond "the inverse limit of these project subgroups".

Composition heuristics check: `(⨅ … comap …).copy …` is a genuine combinator composition
(`Subgroup.iInf`/`Subgroup.comap`/`Subgroup.copy`), **not** a proof in disguise — the `.copy`
obligation is a one-line `ext`/`simp` over `mem_iInf`/`mem_comap` (definitional bookkeeping), matching
the `Set.unit` precedent exactly. So this is a real composition, not a smuggled `by …; aesop`.

## Phase 7 — Verdict

```
## Verdict: `cycloTower1`

**Category:** NO-composable-from-mathlib
```

**Evidence:**
- Literature search (Phase 3): inverse-limit-under-norm-maps is canonical Iwasawa theory and
  `lim← 𝒞_n` / `U`/`C`/`U/C` are studied objects, but `𝒞_{∞,1} = lim←_{n≥1} 𝒞_{n,1}` is
  **paper-specific (RJW) assembly notation**, not a named reusable definition; nLab/MO/arXiv confirm
  no standalone object. No YES anchor.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL as itself** — forced once the base/operand are
  fixed; 0 weakening axes on this decl. Phase 4c: modern idiom is a *reimplementation* (same object),
  not a statement change; the only real abstraction (`Subgroup.invLimit`) belongs to the carrier
  `NormCompatUnits`, not here.
- Mathlib search (Phase 5): **not in mathlib** (both forms); mathlib supplies the combinators
  (`Subgroup.comap`, `Subgroup.iInf`, `Subgroup.copy`) and the precedent idiom (`Set.unit`,
  `SInteger.lean:106`), but not the object nor its project operands.
- Composition check (Phase 6): **COMPOSABLE** as `(⨅ n, ⨅ (_:1≤n), Subgroup.comap (elemsMonoidHom p n)
  (cycloClosureOne p n)).copy …` — 2 mathlib combinators + cosmetic copy, over project-only operands.

**Rationale.** `cycloTower1` is, structurally, the inverse-limit-of-subgroups idiom that mathlib
already expresses with `Subgroup.iInf` ∘ `Subgroup.comap` (the very pattern of `Set.unit`, the
S-units subgroup, `Mathlib/RingTheory/DedekindDomain/SInteger.lean:106`). Its current hand-rolled
`where`-block re-proves `mul_mem'`/`one_mem'`/`inv_mem'` pointwise — exactly the obligations that
`comap` + `iInf` discharge for free — so it is a *verbose spelling of a thin combinator wrapper*,
not new mathematical content. The wrapper's entire content is its two inputs, and **both are
project-specific and absent from mathlib**: the carrier `NormCompatUnits p` (a bespoke
norm-compatible-system structure in `Coleman/Tower.lean`, with its `elemsMonoidHom`) and the
per-level operand `cycloClosureOne p n` (itself assessed `NO-composable-from-mathlib`). Mathlib
supplies only the meet/pullback combinators; it does not — and should not — supply this object,
because once the operands are fixed the object is forced. This is the same structural situation as
the directly-analogous sibling `cycloClosureOne` (a `⊓`-wrapper, verdict `NO-composable`) and the
`unitsTower1`-family, one combinator-level up (`iInf`-of-`comap` instead of a single `⊓`).

The verdict is **not BORDERLINE**: there is no residual taste/policy question *about this decl* — an
`iInf` of comaps over two project subgroups is, by construction, project bookkeeping, decided cleanly
by the structural facts (cf. the sibling `cycloClosureOne`, which resolved the analogous question to
NO, not BORDERLINE). It is **not** any `YES`: not novel as a standalone object (Phase 3), not
generalisable as itself (Phase 4), not in mathlib (Phase 5), and mathlib does not take
inverse-limit wrappers over project operands. It is **not** `NO-mathlib-has-it`: mathlib has neither
the object nor its operands (only the generic combinators). The honest residual mathlib-direction
work — a reusable `Subgroup.invLimit` over a tower of subgroups, of which `cycloTower1`,
`cycloTower1Plus`, and `unitsTower1` would all be instances — is real but is the **carrier's**
assessment (`NormCompatUnits`), named below, not this decl's.

**Refactor-actionable section (NO-composable-from-mathlib):**

WHY not (refactor-actionable detail). Mathlib has the *building blocks* and the *precedent idiom*;
the object is a ≤3-call combinator composition over project operands. Concretely:
- Mathlib building blocks:
  - `Subgroup.comap` — `Mathlib/Algebra/Group/Subgroup/Map.lean:72`
  - `Subgroup.iInf` / `Subgroup.mem_iInf` — `Mathlib/Algebra/Group/Subgroup/Basic.lean:990`
  - `Subgroup.copy` + `Subgroup.mem_comap` (carrier-readability + membership unfolding)
  - precedent: `Set.unit` (S-units) — `Mathlib/RingTheory/DedekindDomain/SInteger.lean:106`
- Composition sketch (≤3 mathlib calls; project operands `elemsMonoidHom`, `cycloClosureOne`):
```lean
example : Subgroup (NormCompatUnits p) :=
  (⨅ n, ⨅ (_ : 1 ≤ n), Subgroup.comap (elemsMonoidHom p n) (cycloClosureOne p n)).copy
    {u | ∀ n, 1 ≤ n → u.elems n ∈ cycloClosureOne p n}
    (by ext u; simp [Subgroup.mem_iInf, Subgroup.mem_comap, elemsMonoidHom])
```

Call sites in our project (from Phase 6.0): **K ≫ 3** (`CyclotomicUnits.lean`,
`IwasawaProof/Generators.lean`, `IwasawaProof/Main.lean`) — load-bearing, no inline re-derivation.

Refactor plan (project-local — this is **not** a mathlib PR):
1. **Keep `cycloTower1` in the project as-is.** It is correct, idiomatically named
   (`lowerCamelCase` for data), faithfully renders RJW TeX 3092, and is genuinely load-bearing glue
   for the Iwasawa main-conjecture image identity. There is nothing to fix and no mathlib PR to open.
2. **Optional internal golf (project cleanup, not mathlib):** at the declaration site, the
   hand-rolled `where`-block may be replaced by the `iInf`-of-`comap` + `.copy` sketch above (the
   `Set.unit` idiom), since `elemsMonoidHom` already exists. This is a same-object cleanup that
   removes the three boilerplate proofs; the K ≫ 3 call sites are unaffected because the `.copy`
   keeps the identical carrier predicate. (Strictly cosmetic — defer to `/cleanup`; do not block on it.)
3. **Do not** propose `cycloTower1` to mathlib — an `iInf` of comaps over two project subgroups is
   project bookkeeping, not a contribution.
4. **The real mathlib-direction work lives on the carrier/operands, assessed separately:**
   - **`NormCompatUnits`** → a general "inverse limit of a tower of groups along a system of maps"
     (a `Subgroup.invLimit`/universal-property inverse-limit constructor) is the genuinely missing,
     contributable mathlib object; `cycloTower1`/`cycloTower1Plus`/`unitsTower1` would all be
     instances of it. This is the carrier's `/mathlibable`, not this decl's.
   - **`cycloClosureOne` / `cycloClosure` / `cycloUnits`** → already assessed (`NO-composable`,
     `NO-composable`, `BORDERLINE` respectively); any mathlib-direction abstraction of the cyclotomic
     closure belongs there.

Next action: keep `cycloTower1` project-local; do **not** open a mathlib PR. If mathlib-direction work
is wanted from this file, run `/mathlibable` on the **carrier** `NormCompatUnits` (the candidate
`Subgroup.invLimit` gap) and on `cycloUnits` (the BORDERLINE base group `𝒟_n`).

---

## Next step

Keep `cycloTower1` as load-bearing project-local API (no mathlib PR — it is a thin inverse-limit
wrapper over two project-specific operands). Optionally golf the declaration to the
`(⨅ n, comap (elemsMonoidHom p n) (cycloClosureOne p n)).copy …` (`Set.unit`) idiom during a project
`/cleanup`. Direct any genuine mathlib contribution at the **carrier** `NormCompatUnits` (a reusable
`Subgroup.invLimit` of a tower of subgroups — the real missing API) rather than at this assembly node.

---

### Evidence pointers (for the Phase-7 gate)
- Phase 3 table: 10 rows / 9 channels; ≥3 substantive WebSearches at distinct generality levels
  (specific / named-`C_∞` / abstract-idiom) with sources; ChatGPT-MCP, local-refs, and Stacks each
  recorded `n/a: <reason>` (not blank). Source paper (arXiv:2309.15692) self-identified in channel 2.
- Phase 4: explicit MAXIMALLY-GENERAL-as-itself with 0 weakening axes; operand/carrier alternatives named.
- Phase 4c: Bourbaki-2.0 claim **withheld** for this decl (the modern idiom is a same-object
  reimplementation, not a statement change); the real abstraction (`Subgroup.invLimit`) attributed
  to the carrier `NormCompatUnits`.
- Phase 4.5: six-row risk table, overall **NONE** (plain `def`, no instance/coercion/universe issues).
- Phase 5: five methods (A recorded `n/a` with [D]+[E] substitute); building blocks + precedent cited
  by qualified name (`Subgroup.comap`, `Subgroup.iInf`/`mem_iInf`, `Subgroup.copy`, `Set.unit`).
- Phase 6: composition is 2 mathlib combinators + cosmetic `.copy` over **project-specific** operands
  (`elemsMonoidHom`, `cycloClosureOne`) → not Case-4 mathlib-self-composable; call-sites table shows
  K ≫ 3 but every use unfolds to the component predicate.
- Consistency: matches sibling verdicts `cycloClosureOne` = `NO-composable` (the `⊓` one level down)
  and the `unitsTower1`-family; `cycloUnits` (the base group with real content) = `BORDERLINE`,
  `globalUnits` = `NO-mathlib-has-it`.
- No cost-based reasoning used anywhere (cost is not a verdict factor).
