# Mathlibable assessment: `PadicLFunctions.Coleman.cycloClosureOnePlus`

**Final verdict: `NO-composable-from-mathlib`** (a thin definitional single-`⊓` wrapper over
two project-specific subgroups; not a standalone mathlib object).

- **Kind:** `def` (returns data — a `Subgroup ℂ_[p]ˣ`), so `lowerCamelCase` is correct.
- **Source:** `projects/PadicLFunctions/PadicLFunctions/Iwasawa/CyclotomicUnits.lean:222`
- **Mode:** A (single declaration), full 10-phase workflow with the 9-channel literature search.

```lean
/-- `𝒞⁺_{n,1} = 𝒞_n⁺ ∩ 𝒰_{n,1}` (RJW TeX 3091). -/
noncomputable def cycloClosureOnePlus (n : ℕ) : Subgroup ℂ_[p]ˣ :=
  cycloClosurePlus p n ⊓ localUnitsOne p n
```

This decl is the direct structural sibling of `cycloClosureOne` and `cycloClosurePlus`, both
already assessed in this directory as `NO-composable-from-mathlib`. The reasoning below is
re-derived independently (own literature + mathlib searches), not merely inherited, and lands
at the same bucket.

---

## Phase 0 — Doctor / baseline

Per the task's build note, `lake build` was **not** re-run (the build is known stale/slow here).
**Build not re-run; reasoned from source.** The declaration and its full dependency chain were
read directly from source:

- `cycloClosurePlus p n := cycloClosure p n ⊓ localUnitsPlus p n` (`CyclotomicUnits.lean:214`)
- `cycloClosure p n := (cycloUnits p n).topologicalClosure ⊓ localUnits p n`
  (`CyclotomicUnits.lean:210`)
- `cycloUnits p n := Subgroup.closure (cycloGenSet p n) ⊓ globalUnits p n`
  (`CyclotomicUnits.lean:182`)
- `localUnitsOne p n` = principal local units, carrier
  `{u | u ∈ localUnits p n ∧ ‖(u : ℂ_[p]) − 1‖ < 1}` (`LocalUnits.lean:71`)
- `localUnitsPlus p n` = `{u | u ∈ localUnits p n ∧ (u : ℂ_[p]) ∈ KPlus p n}` (`LocalUnits.lean:115`)
- `localUnits p n` = units of `O_n` (`LocalUnits.lean:39`)

All operands are **project-defined** objects of the RJW (arXiv:2309.15692) §11.3 Iwasawa
cyclotomic-unit tower, living inside `ℂ_[p]`. No `sorry` is present in the def itself (it is data).
One downstream *consumer* (`cycloClosureOnePlus_le_closure_wGammaTranslate`, `Generators.lean:1847`)
is a `sorry`'d theorem — that is the owning producer's WIP and is out of scope for this assessment.

## Phase 1 — Comprehend

`cycloClosureOnePlus p n` is `𝒞⁺_{n,1}`: the meet (lattice `⊓` on `Subgroup ℂ_[p]ˣ`) of

1. `cycloClosurePlus p n = 𝒞_n⁺` — the plus part of the p-adic (topological) closure of the
   cyclotomic units `𝒟_n` inside the local units `𝒰_n` (itself `cycloClosure p n ⊓ localUnitsPlus p n`);
   and
2. `localUnitsOne p n = 𝒰_{n,1}` — the principal local units (`‖u − 1‖ < 1`).

Mathematically it is the **principal-unit, totally-real part** of the local closure of the
cyclotomic units at level `n` — one node in the construction of the tower `𝒞⁺_{∞,1}` (built
immediately below it as `cycloTower1Plus`) that receives the Coleman-map input. It is data (a
bundled subgroup), defined as a **single `⊓`** of two project subgroups (one of which is itself
a `⊓` of project subgroups — so fully expanded it is `cycloClosure ⊓ localUnitsPlus ⊓ localUnitsOne`).

## Phase 2 — Preliminary BIG/SMALL + one-line check

SMALL by construction: the body is one `⊓`. It is **not** a one-liner equal to an existing mathlib
decl (both operands are project-specific), so the one-line exemption does not apply — it is a *new
project definition that happens to be a trivial combination of project objects*.

**One-liner exemption check (defeq-abuse / diamond-avoidance / API-stability):** none apply.

- *Defeq abuse / unfolding barrier* — **no**. Every external consumer immediately unfolds the def:
  all four `Main.lean` sites are `rw [cycloClosureOnePlus, Subgroup.mem_inf, cycloClosurePlus,
  Subgroup.mem_inf]`. The def is routinely punched through, not relied on as a sealed spelling.
- *Diamond avoidance* — **no**. No new instance is introduced; it reuses mathlib's
  `Lattice (Subgroup G)` (`Subgroup.instMin`).
- *API stability* — **weak/no**. The name carries the RJW symbol `𝒞⁺_{n,1}` + a docstring (TeX 3091),
  which is *some* source-faithfulness value for readers, but there is **no stable opaque API
  surface**: there are zero lemmas stated about `cycloClosureOnePlus` as such, and consumers reach
  its factors by unfolding, not by an exported interface.

## Phase 3 — Exhaustive literature search (9 channels)

| # | Channel | Query | Result |
|---|---|---|---|
| 1 | WebSearch | "Iwasawa theory cyclotomic units p-adic closure principal local units plus part tower C_n,1" | Concepts standard (Iwasawa, Sharifi *A Climb up the Tower*; Coates–Sujatha; structure of plus-part of principal units mod cyclotomic units — math/0512015, 1907.06437). **No standalone "C⁺_{n,1}" object**; the per-level principal-unit-plus intersection is paper-specific bookkeeping. |
| 2 | WebSearch | "Rubin de Shalit cyclotomic units local closure intersection principal units totally real plus subfield definition" | Rubin's Euler systems / `99RubinES`; Rubin's conjecture on local units in the anticyclotomic tower (2401.09037); circular units & class groups (labmath UQAM). Plus/minus splittings `V±` of local units, `U/C` quotients appear — but the intersection-with-principal-units is *inside specific proofs*, never a named definition. |
| 3 | WebSearch (sibling-corroborated) | "'semi-local units modulo cyclotomic units' projective limit principal units p-adic closure" | (from sibling `cycloClosureOne` assessment, same literature) Sciencedirect (Kim) + JTNB: `U` (proj. limit semi-local units), `C` (proj. limit cyclotomic units), study of `U/C`. The *operand-level* objects are standard; the per-level plus/principal intersection is bookkeeping. |
| 4 | ChatGPT MCP (historical formulation) | n/a | **n/a: MCP server not configured in this environment.** Substituted by the WebSearches above + local-mathlib reading. |
| 5 | Local refs (`refs/PadicLFunctions/`) | — | **n/a: no `refs/` symlink present** (PDFs are local-only and not linked here). Primary source from the docstring: RJW arXiv:2309.15692, §11.3, TeX 3090–3094. |
| 6 | nLab | cyclotomic units / principal units / plus part | No page treating this exact per-level plus-principal intersection as a named object. |
| 7 | nCatLab / Stacks | local units, principal units, Iwasawa | Stacks has valuation/units machinery; no cyclotomic-unit local-closure tower. |
| 8 | MathOverflow | semi-local units modulo cyclotomic units; plus part of local units | Matches channels 1–3 — `U/C` and `V±` are the studied objects, not `𝒞⁺_{n,1}` per se. |
| 9 | arXiv | (covered by 1–3) | math/0512015, 1907.06437, 2401.09037, RJW 2309.15692, JTNB circular-units notes. |

**Phase 3 conclusion.** The *ingredients* (cyclotomic units, their p-adic/topological closure, the
plus/totally-real part, principal/semi-local units, and the quotient `U/C` or splitting `V±`) are
canonical Iwasawa theory. The *specific object* `𝒞⁺_{n,1} = 𝒞_n⁺ ∩ 𝒰_{n,1}` is **not** a named,
reusable definition in the literature — it is one intersection step in a particular tower
construction (RJW). There is therefore no "literature-standard form of `cycloClosureOnePlus`" to
anchor a generalisation against.

## Phase 4 — Generality vs literature-standard form

`cycloClosureOnePlus` is `A ⊓ B`. There is no separate "more general form of the meet" to target.
The only generality questions live on the **operands**, and they are about *those* decls, not this one:

| # | Axis | User's form | More general standard | On this decl? | Note |
|---|---|---|---|---|---|
| 1 | ambient field | fixed `ℂ_[p]` | general CM / totally-real local tower | no | fixed by the whole RJW project setup, not a knob on this meet. |
| 2 | principal units `𝒰_{n,1}` | `‖u−1‖ < 1` predicate | `ValuationSubring.principalUnitGroup` | no (operand) | a real modernisation, but of `localUnitsOne`, not of this object. |
| 3 | closure operand `𝒞_n⁺` | `cycloClosurePlus` (project) | hypothetical general "closure of cyclotomic units in local units" | no (operand) | belongs to `cycloClosure`/`cycloUnits` assessment. |
| 4 | meet `⊓` | `Subgroup.⊓` | — | n/a | already maximally general (mathlib lattice meet). |

**Verdict for THIS decl: not separately generalisable.** It inherits whatever generality the operands
have; weakening it means weakening `localUnitsOne` / `cycloClosurePlus`, which is out of scope for
`cycloClosureOnePlus` and is the operands' own assessment. (Cost was not used as a factor anywhere.)

## Phase 4c — Modern-mathlib-idiom (Bourbaki 2.0) restatement

| # | Modern-idiom question | Applies here? | Downstream consequence? | Note |
|---|---|---|---|---|
| 1 | bundled subgroup vs ad-hoc subset | already bundled | — | `Subgroup ℂ_[p]ˣ` is the idiomatic form; the `⊓` is the idiomatic "intersection of two subgroups" (`Lattice (Subgroup G)`). |
| 2 | sequences/metric → filters/topological | no | — | the only topology is inside the *input* `cycloClosure` (via `Subgroup.topologicalClosure`, already the idiomatic mathlib form); this decl adds none. |
| 3 | concrete predicate → typeclass/valuation | no (operand) | on `localUnitsOne` only | restating `localUnitsOne` via `ValuationSubring.principalUnitGroup` is a genuine modernisation — but for that operand, with downstream consequences for `localUnits*`, not for `cycloClosureOnePlus`. |

The meet `⊓` is already the maximally idiomatic mathlib spelling. There is **no** modern-idiom
restatement of `cycloClosureOnePlus` *itself* with concrete downstream consequences: once the operands
are fixed, the object is forced to be their meet. (Bourbaki-2.0 claim deliberately **withheld** for
this decl — it would fail the Phase-7 gate's "downstream consequences" requirement. The real
modernisation lives one level down, on `localUnitsOne`.)

## Phase 4.5 — Diamond / defeq risk (def/class/instance)

| # | Risk | Level | Note |
|---|---|---|---|
| 1 | New instance / diamond | none | no instance introduced; reuses mathlib `Subgroup.instMin` / `Lattice (Subgroup G)`. |
| 2 | Reducibility leak | none | plain `noncomputable def`, not `@[reducible]`; body is `⊓`, itself sealed. |
| 3 | Non-canonical unfolding | low | unfolding exposes `cycloClosurePlus p n ⊓ localUnitsOne p n`; with `Subgroup.mem_inf` this is exactly the intended (and only) usage pattern. No surprise. |

## Phase 5 — Mathlib five-method search

| # | Method | Query | Result |
|---|---|---|---|
| A | Lean-Finder | (semantic) | **n/a: tool not available in-env**; substituted by D + E over the local `.lake/packages/mathlib` checkout. |
| B | Loogle / type | `(n : ℕ) → Subgroup ℂ_[p]ˣ` from project defs | No mathlib hit possible — the return type is built from project-defined subgroups. |
| C | LeanSearch / NL | "plus part of p-adic closure of cyclotomic units intersect principal units" | Concept absent from mathlib. |
| D | grep mathlib source | `CyclotomicUnit`/`cyclotomicUnit`, `principalUnitGroup`, `localUnits`, `Iwasawa`, `topologicalClosure` | `RingTheory/RootsOfUnity/CyclotomicUnits` + `NumberField/Cyclotomic/Ideal.lean` = generic number-field cyclotomic units / cyclotomic-field ideals (**not** a local-closure object). `ValuationSubring.principalUnitGroup` (`RingTheory/Valuation/ValuationSubring.lean:634`, with `mem_principalUnitGroup_iff` at :656) = general principal-unit group — closest analogue of the **operand** `localUnitsOne`, **not** of this object. `GroupTheory/GroupAction/Iwasawa.lean` = Iwasawa *simplicity criterion* (unrelated). `Subgroup.topologicalClosure` exists generally. **No cyclotomic-unit local-closure tower.** |
| E | name-pattern | `cycloClosure*`, `cycloClosureOnePlus`, `localUnits*`, `cycloUnits*` | Found **only** in this project. Grep over mathlib for `cycloClosureOnePlus` → 0 hits (expected — project-local). |

`Subgroup.mem_inf` (`Mathlib/Algebra/Group/Subgroup/Lattice.lean:233`) confirms the meet API mathlib
supplies. **Phase 5 conclusion: mathlib does NOT have `cycloClosureOnePlus` or any direct analogue.**
It has (a) the generic `⊓`, and (b) `ValuationSubring.principalUnitGroup` as a *general* sibling of one
operand — but not this object, and not the cyclotomic-unit-closure operand `cycloClosurePlus`.

## Phase 6 — Composition check (≤3 mathlib calls?)

The body is `cycloClosurePlus p n ⊓ localUnitsOne p n` — a **single** mathlib `⊓`. But the two operands
are **project-specific** subgroups that are **not in mathlib**. So:

- This is **not** the `NO-composable-from-mathlib` of Case 4 in `references/mathlibable-verdicts.md`
  in the strict "mathlib's own building blocks reproduce the object in ≤3 mathlib calls" sense. Here
  mathlib supplies only the `⊓`; the content is the operands, which only exist in the project.
- Equivalently: `cycloClosureOnePlus` is a **thin definitional wrapper internal to the project**,
  riding on the lattice meet. It carries no mathematical content beyond "intersect these two project
  objects." It cannot be reconstructed from mathlib alone (the operands are needed), and it is too
  trivial to be a standalone mathlib definition.

This matches the verdict-doc's "STRUCTURE" note (audit item 12): combined `A ⊓ B` wrappers over
separate objects/facts do not go to mathlib as standalone definitions. The same bucket label
(`NO-composable-from-mathlib`) is the closest fit and is exactly what the two structural siblings
(`cycloClosureOne`, `cycloClosurePlus`) received.

### Phase 6.0 — Call-sites (composability signal)

| Consumer | Site | Uses | Nature |
|---|---|---|---|
| `Iwasawa/CyclotomicUnits.lean:234` | `cycloTower1Plus` carrier | `{u \| ∀ n, 1 ≤ n → u.elems n ∈ cycloClosureOnePlus p n}` | in-file value (tower assembly) |
| `Iwasawa/CyclotomicUnits.lean:237` | `cycloTower1Plus` `inv_mem'` | `(cycloClosureOnePlus p n).inv_mem (hu n hn)` | in-file value (tower assembly) |
| `IwasawaProof/Generators.lean:1847` | `cycloClosureOnePlus_le_closure_wGammaTranslate` (statement) | `(cycloClosureOnePlus p n : Set ℂ_[p]ˣ) ⊆ …` | statement only — proof is `sorry` (producer WIP) |
| `IwasawaProof/Main.lean:528` | density step | `rw [cycloClosureOnePlus, Subgroup.mem_inf, cycloClosurePlus, Subgroup.mem_inf]` | code (unfold) |
| `IwasawaProof/Main.lean:612` | `≤` step | `rw [cycloClosureOnePlus, Subgroup.mem_inf, cycloClosurePlus, Subgroup.mem_inf] at h` | code (unfold) |
| `IwasawaProof/Main.lean:621` | `≤` step | `rw [cycloClosureOnePlus, Subgroup.mem_inf, cycloClosurePlus, Subgroup.mem_inf] at h` | code (unfold) |
| `IwasawaProof/Main.lean:753` | membership step | `rw [cycloClosureOnePlus, Subgroup.mem_inf, cycloClosurePlus, Subgroup.mem_inf]` | code (unfold) |

K ≥ 3 internal uses → it is *real, used* project API. **But** every code-level use unfolds it back to
its factors (`Subgroup.mem_inf`), and there are **zero lemmas stated about `cycloClosureOnePlus` as an
opaque object**. The one named theorem that mentions it (`…_le_closure_wGammaTranslate`) uses it only
in its *statement* and is itself unproved (`sorry`). The call-site signal says "load-bearing project
glue / readable node in the `⊓`-tower," **not** "standalone abstraction worth exporting to mathlib."

## Phases 7–8 — Verdict synthesis and gate

Weighing the artifacts:

- **Phase 3:** object is **not** a named literature definition (only its ingredients are) → no YES anchor.
- **Phase 4 / 4c:** **not separately generalisable / no modern restatement** of this decl (those moves
  belong to the operands) → not `YES-but-generalise-first`.
- **Phase 5:** **mathlib lacks it** and lacks both operands (`principalUnitGroup` is only a general
  sibling of one operand, not this object) → not `NO-mathlib-has-it`.
- **Phase 6:** it is a **single `⊓` over two project-specific, non-mathlib operands** → a thin wrapper,
  not standalone-novel; cannot live in mathlib without the operands.

The structural facts decide this cleanly, so it is **not** `BORDERLINE` (no residual taste/policy
question — a `⊓` of two project subgroups is, by construction, project bookkeeping). It is **not** any
`YES` (not novel as a standalone object; not generalisable as itself; mathlib PRs do not take `A ⊓ B`
wrappers). The best fit is:

### Final verdict: `NO-composable-from-mathlib`

with the precise reading: **a trivial definitional single-`⊓` wrapper over two project-specific
subgroups.** Mathlib supplies the meet (`Subgroup.mem_inf`); it does not — and should not — supply
this object, because its entire content is the two project operands.

**Recommended action (project-local, not a mathlib PR):**

1. **Keep `cycloClosureOnePlus` as-is in the project.** It is correct, idiomatically named
   (`lowerCamelCase` for data), and is genuinely load-bearing glue / a readable node in the RJW
   Iwasawa `⊓`-tower (`cycloClosure → cycloClosurePlus → cycloClosureOnePlus → cycloTower1Plus`). There
   is nothing to fix. (A cleaner may optionally inline it or drop `cycloClosurePlus,` from the
   `Main.lean` `rw` chains, since the consumers unfold it anyway — purely a readability call, not a
   correctness or mathlib-direction one.)
2. **Do not** propose `cycloClosureOnePlus` to mathlib — a `⊓` of two project subgroups is not a
   mathlib contribution.
3. **If** any mathlib-direction work is wanted from this file, it lives **on the operands**, assessed
   separately:
   - `localUnitsOne` → consider restating against `ValuationSubring.principalUnitGroup` (mathlib's
     general principal-unit group; `mem_principalUnitGroup_iff` matches the `‖u−1‖<1` predicate) — a
     real Bourbaki-2.0 modernisation *for that decl*.
   - the cyclotomic-unit closure (`cycloClosure` / `cycloUnits`) → a general "topological closure of
     cyclotomic units in the local units" API would be the contributable object, if abstracted away
     from the bespoke `ℂ_[p]` setup.

---

### Evidence pointers (for the Phase-7 gate)

- **Phase 3 table:** 9 channels; 3 substantive web channels with sources; ChatGPT-MCP and local-refs
  recorded `n/a: <reason>` (not blank).
- **Phase 4:** explicit "not separately generalisable" with the operand-level alternatives named; no
  cost-based reasoning.
- **Phase 4c:** Bourbaki-2.0 claim **withheld** for this decl (no downstream consequence) — only
  asserted for the operand `localUnitsOne`.
- **Phase 5:** five methods, A recorded `n/a` with substitute; mathlib decls cited by qualified name
  (`Subgroup.mem_inf` @ Lattice.lean:233, `ValuationSubring.principalUnitGroup` @ ValuationSubring.lean:634,
  `RootsOfUnity.CyclotomicUnits`, `NumberField.Cyclotomic.Ideal`, `GroupTheory.GroupAction.Iwasawa`).
- **Phase 6:** composition is one `⊓`; building blocks are project-specific → not Case-4 mathlib-composable
  in the strict sense; call-sites table shows K ≥ 3 but every code use unfolds to factors and there are
  zero opaque-object lemmas.
- **Consistency:** structural siblings `cycloClosureOne` and `cycloClosurePlus` independently received
  the same `NO-composable-from-mathlib` verdict; this decl is the same `A ⊓ B`-over-project-subgroups
  pattern.
