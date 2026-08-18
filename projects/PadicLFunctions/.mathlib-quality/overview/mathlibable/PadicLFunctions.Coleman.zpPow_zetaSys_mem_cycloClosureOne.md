# `/mathlibable` report — `PadicLFunctions.Coleman.zpPow_zetaSys_mem_cycloClosureOne`

Mode A (single declaration, full 10-phase workflow, exhaustive literature sweep).

---

### Baseline (Phase 0)

- lake build:               build not re-run; reasoned from source (per task build note — `lake build` is stale/slow here; declaration and its dependency closure read directly from source).
- decl `PadicLFunctions.Coleman.zpPow_zetaSys_mem_cycloClosureOne`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/Iwasawa/CyclotomicUnits.lean:569`
- kind:                      theorem
- has sorry:                 no (proof body lines 569–612, sorry-free; whole file has 0 `sorry`)
- module docstring summary:  "Cyclotomic units: the global modules 𝒟_n and their local closures 𝒞 (RJW §11.3)" — builds, inside `ℂ_[p]`, the cyclotomic units `𝒟_n = cycloUnits`, their p-adic closures `𝒞_n`, `𝒞_{n,1} = cycloClosureOne`, and the towers, en route to the Iwasawa-main-conjecture milestone `cyclo ∈ 𝒞_{∞,1}`.

---

### Statement (Phase 1)

`zpPow_zetaSys_mem_cycloClosureOne` is **a theorem** stating the following:

Fix a prime `p` and the compatible system of primitive `pⁿ`-th roots of unity `ξₙ = zetaSys p n` living inside `ℂ_[p]` (the `p`-adic complex numbers). For `n ≥ 1` and any `p`-adic integer exponent `a ∈ ℤ_p`, the `ℤ_p`-power `ξₙ^a` (defined via the binomial/Mahler additive character `zpPow`, mathlib's `PadicInt.addChar_of_value_at_one`) lies in the group `𝒞_{n,1} = cycloClosureOne p n` — the intersection of the **`p`-adic topological closure of the cyclotomic units `𝒟_n`** with the **principal local units `𝒰_{n,1}`**.

The mathematical content is a *density-plus-membership* fact: the continuous map `c ↦ ξₙ^c : ℤ_p → ℂ_[p]ˣ` agrees with the ordinary integral powers `ξₙ^k` on the dense subset `ℕ ↪ ℤ_p`; since each `ξₙ^k` is a cyclotomic unit and the closure is closed, the whole `ℤ_p`-orbit (in particular `ξₙ^a`) lands in the closure `(𝒟_n)⁻`. The principal-unit part (`‖ξₙ^a − 1‖ < 1`) comes from `ξₙ` being a `1`-unit and `zpPow` preserving `𝒰_{n,1}`.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the prime (section variables).
- `n : ℕ` with `(hn : 1 ≤ n)` — the cyclotomic level.
- `a : ℤ_[p]` — the `p`-adic-integer exponent (the "Tate twist" / cyclotomic-character variable).
- `{x : ℂ_[p]ˣ}` together with `(hx : (x : ℂ_[p]) = zpPow p (zetaSys p n) a)` — `x` is the unit whose underlying value is `ξₙ^a`.

Hypotheses (Lean side):
- `hn : 1 ≤ n` — needed so `‖ξₙ − 1‖ < 1` (`ξₙ` is a genuine `1`-unit; fails for `n = 0` where `ξ₀ = 1` trivially but the principal-unit story is vacuous) and so `zetaSysU` is well-formed.
- `hx` — pins `x` to the `zpPow` value (works around `ℂ_[p]ˣ` vs `ℂ_[p]` bundling).

Conclusion (math): `ξₙ^a ∈ 𝒞_{n,1}` — the `ℤ_p`-power of the root of unity lies in the principal-unit part of the `p`-adic closure of the cyclotomic units.

Conclusion (Lean): `x ∈ cycloClosureOne p n`.

---

### Size classification (Phase 2a)

Verdict: **BIG** (borderline; classified BIG for framing).
Reason: it is a named step in a **main result** of the project — the milestone `cyclo ∈ 𝒞_{∞,1}` (RJW TeX 3084) feeding the Iwasawa main conjecture (its sole caller, `ZpOne_le_cycloTower1` in `IwasawaProof/Main.lean`, is the inclusion `ℤ_p(1) ⊆ 𝒞_{∞,1}` central to the §12.5 injectivity sub-lemma). It is not a new structure and not named after a person, but it is a load-bearing theorem of the project's flagship proof.

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for the report's framing only — it does not gate which channels Phase 3 runs.)

### One-line check (Phase 2b)

Body line count: ~37 substantive lines (44 lines incl. signature/docstring).
One-liner verdict: **n/a** — kind is `theorem`, not a `def`/`abbrev`/`structure`. No exemption table required.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query | Hit? | Standard form found | Notes |
|----|----------------------------------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form)        | "cyclotomic units p-adic closure principal units local field Iwasawa theory closure topology" | partial | closure of (global) principal/cyclotomic units in local units is a standard Iwasawa object | Returns Iwasawa/Hida/Coates–Sujatha treatments of `𝒰`/`𝒟` and their closures, but no isolated lemma "`ξ^a` ∈ closure". |
| 2 | WebSearch (source paper)         | "RJW arXiv 2309.15692 Iwasawa main conjecture cyclotomic units Coleman map" | yes | confirms the source: Loeffler–? "An introduction to p-adic L-functions" (arXiv:2309.15692); Coleman's construction via cyclotomic units, Iwasawa MC for Vandiver primes | The project's `RJW` references = this expository paper. The closure `𝒞` and the `ℤ_p(1) ⊆ 𝒞_{∞,1}` step are §11–12 internal scaffolding. |
| 3 | WebSearch (general form / aliases) | "primitive root of unity p-adic power belongs to closure cyclotomic units density natural number exponents" | no (as a named lemma) | none — the *density of ℕ in ℤ_p* and *closure-of-subgroup* facts are standard, but the packaged statement is not a named theorem | Wikipedia "Cyclotomic unit" + Coates–Sujatha; the combination is bespoke. |
| 4 | WebSearch (general form / Mazur–Wiles) | `"cyclotomic units" "p-adic" closure "principal units" Z_p module topological generators continuous power map Mazur-Wiles` | partial | the *closure of cyclotomic units is a ℤ_p-module / has topological generators* is classical (Iwasawa 1968; Mazur–Wiles; Rubin Euler systems) | Confirms the ambient theory but no atomic "`y^a` ∈ closure" statement; it is a routine internal lemma in those treatments. |
| 5 | ChatGPT MCP                      | (would ask: standard form + generality + historical evolution of "p-adic power of a root of unity lies in the closure of the cyclotomic units") | **n/a** | — | ChatGPT MCP server `chatgpt-math` is configured but **not authenticated and not in `enabledMcpjsonServers` this session** (only `lean-lsp` is enabled); its `mcp__*` tools were not surfaced. Substituted with two extra WebSearch generality levels (#3, #4) + the source-paper fetch (#10). |
| 6 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/` | **n/a** | (no references dir) | Neither `.mathlib-quality/references/` nor a local `refs/` store exists in this checkout — recorded n/a. Source paper identified via web instead (#2, #10). |
| 7 | nLab                             | "nLab cyclotomic units local closure principal local units topological closure subgroup" | no | nLab has "cyclotomic spectrum" (unrelated, homotopy-theoretic) and topological-generator facts for principal units of higher local fields, but not this lemma | The principal-unit group as a finitely-generated topological ℤ_p-module appears; the specific closure-membership statement does not. |
| 8 | nCatLab (if categorical)         | (covered by #7; nLab = nCatLab) | n/a | — | Not a categorical concept; no separate nCatLab hit beyond #7. |
| 9 | Stacks Project (if alg geom)     | — | **n/a** | — | Not an algebraic-geometry / scheme-theoretic concept; the Stacks Project does not treat `p`-adic Iwasawa unit closures. |
| 10 | MathOverflow / Math.StackExchange | "MathOverflow closure of cyclotomic units in local units Z_p power principal unit dense integral powers" | partial | Leopoldt-style facts: ℤ_p-rank of the closure of global principal units in local units; principal units a f.g. ℤ_p-module | Confirms the *closure* object is standard and studied, but the atomic membership lemma is not separately named. |
| 11 | recent arXiv (last 5 years)      | source-paper fetch `arxiv.org/abs/2309.15692` + Mazur–Wiles survey hits | yes (source) | confirms Coleman-via-cyclotomic-units construction; the closure tower is the algebraic side of the main conjecture | The abstract confirms the framing; section-level detail on `𝒞` not in the abstract (full text would be §11–12). |

The protocol passed: WebSearch ran ≥3 distinct queries at three generality levels (specific form #1, source paper #2, most-general/named-after #3/#4); local references checked (n/a, absent); nLab checked (#7); Stacks/nCatLab/MathOverflow/arXiv each checked or recorded n/a with reason. ChatGPT MCP recorded n/a (server unavailable this session) with two substitute WebSearch generality levels.

### Literature summary (Phase 3)

Concept identified as: the **`p`-adic (topological) closure of the cyclotomic units inside the local principal units** (`𝒟_n → 𝒞_n → 𝒞_{n,1}`), an Iwasawa-theory object; the specific result is "the `ℤ_p`-power `ξₙ^a` of a primitive root of unity lies in that closure", which is an *internal lemma* (a density argument) on the way to `ℤ_p(1) ⊆ 𝒞_{∞,1}`.

Sources agree on the standard form: **no atomic standard form** — the *closure object* `𝒞` is standard (Iwasawa 1968; Mazur–Wiles; Rubin; Coates–Sujatha; and the source paper arXiv:2309.15692), but the precise membership lemma `ξₙ^a ∈ 𝒞_{n,1}` is not a separately-named theorem in the literature. It is the kind of routine-but-essential step that textbooks fold into a larger argument.

Most general standard form: in the literature one works with the closure `\overline{C}` of the cyclotomic (or global) units inside the local units `U`, and uses that `U_1` is a finitely-generated ℤ_p-module on which the `ℤ_p`-action is continuous; the membership `ξ^a ∈ \overline{C}` is immediate from continuity + density of ℤ in ℤ_p. No single canonical lemma name attaches to it.

Generality dimensions where the literature varies:
  - Ambient field: from `ℚ_p(μ_{pⁿ})` (the honest local field `K_n`) to a fixed embedding into `ℂ_[p]` (the project's choice, R11.7). The project works inside `ℂ_[p]` throughout; the literature usually stays in `K_n`.
  - Which units: cyclotomic units `𝒟_n` vs all global/local principal units. The project uses the cyclotomic-unit closure specifically.
  - Exponent object: `ℤ` (integral powers, classical) vs `ℤ_p` (the `zpPow` extension, needed for the Tate-twist tower). The `ℤ_p` extension is the modern Iwasawa-theoretic move and the actual content here.

Disagreement with the literature: none — the statement is a faithful (if bespoke) rendering of a standard internal step. The literature simply does not isolate it as a stand-alone named result.

---

### Generality analysis — `zpPow_zetaSys_mem_cycloClosureOne`

Literature-standard form (from Phase 3): "for a `1`-unit `y` in the closure of a subgroup `H` of the (abelian, topological) principal units, every `ℤ_p`-power `y^a` is again in the closure of `H`" — a continuity+density fact, with `y = ξₙ` and `H = 𝒟_n` the concrete instance.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | the base element | `zetaSys p n` (a *fixed* primitive `pⁿ`-th root of unity from a chosen compatible system) | any `1`-unit `y` of the local field | **yes** | The proof uses only `‖ξₙ − 1‖ < 1`, that `ξₙ^k ∈ 𝒟_n`, and `ξₙ ∈ 𝒰_{n,1}`. The project **already** has the more general `zpPow_mem_cycloUnits_topologicalClosure` (same file, line 631) abstracting the base to a general `y` with `‖y−1‖<1` in the closure — i.e. the generalisation is realised internally. |
| 2 | the subgroup | `cycloUnits p n` (`𝒟_n`, project-local, RJW-specific) | any subgroup `H ≤ 𝒰_{n,1}` | yes (the closure-step) | The "lands in closure" half generalises to any `H`; only the "`ξₙ^k ∈ 𝒟_n`" half is `𝒟_n`-specific. The decomposition into the general `zpPow_mem_cycloUnits_topologicalClosure` + the principal-unit part already exposes this. |
| 3 | ambient field | `ℂ_[p]` (mathlib `PadicComplex`) | the local cyclotomic field `K_n = ℚ_p(μ_{pⁿ})` | not cleanly | The whole project commits to `ℂ_[p]` (decision R11.7) so every dependency lives there. Re-aiming at `K_n`/abstract local fields would require redoing `localUnits`, `zpPow`, `zetaSys` — a project-wide refactor, not a lemma weakening. |
| 4 | exponent | `a : ℤ_[p]` | `ℤ_p` (matches) | NO | This is already maximally general — the `ℤ_p` exponent (vs `ℤ`) is the point. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (in axis #1/#2: the base is a *fixed specific* root of unity `zetaSys p n` and the subgroup is the *project-specific* `cycloUnits p n`, whereas the standard form abstracts the base to any closure-member `1`-unit).

Number of weakening opportunities found: 2 (base element; subgroup), **both already realised inside the project** by `zpPow_mem_cycloUnits_topologicalClosure` (general base) which this theorem is the concrete `ξₙ`/`𝒟_n` instance of. The "narrowness" is a deliberate specialisation, not an oversight.

Proposed restatement: not a *mathlib*-facing restatement — the natural generalisation (`zpPow_mem_cycloUnits_topologicalClosure`) is itself stated over the same project-local objects (`cycloUnits`, `zpPow`, `ℂ_[p]`-local-units), none of which is mathlib material in its current bespoke form. So generalising does not move it toward mathlib; it stays a project-internal lemma.

Cost of restatement: **CHEAP** (and already done internally) — but irrelevant to the mathlib verdict, because the generalised form is still over project-local definitions.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preambles → typeclasses/instances? | no | — | Hypotheses are already minimal (`1 ≤ n`, `hx` defeq-pin); nothing to typeclass-ify. |
| 2 | sequences/metric → filters/topological? | no | — | The proof already uses `closure`, `Continuous`, `DenseRange`, `topologicalClosure` — fully filter/topology-idiomatic mathlib API. |
| 3 | construction → universal-property class? | no | — | No construction here; it is a membership theorem. |
| 4 | set-with-closure-predicate → bundled substructure? | **partially already done** | — | `cycloClosureOne`, `cycloUnits` are already bundled `Subgroup`s (not raw sets), composing with mathlib's `Subgroup.topologicalClosure` lattice API. Good idiom already. |
| 5 | vector-space/field-specific → modules/(semi)ring? | no | — | Already at the right altitude (`ℤ_p`-action on `ℂ_[p]ˣ`); no field-to-ring weakening available. |
| 6 | 1-categorical → higher-categorical? | no | — | Not categorical. |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group? | NO (and the point) | — | The exponent is already `ℤ_p`, the maximal sensible index; the *base* could generalise (axis #1 above) but only within project-local objects. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (the declaration is already written in contemporary mathlib idiom — bundled `Subgroup`s, `topologicalClosure`, `Continuous`/`DenseRange`/`closure_mono`, the `addChar_of_value_at_one` `ℤ_p`-character). There is no Bourbaki-2.0 reformulation that would move it toward mathlib; the only "generalisation" (abstract base/subgroup) keeps it over the same project-local definitions and is already realised by `zpPow_mem_cycloUnits_topologicalClosure`.
One-line reason this is not a modernisation move: the statement is intrinsically about *project-specific* objects (`zetaSys`, `cycloUnits`, the `ℂ_[p]`-local-unit tower) that are themselves not mathlib-standard, so no idiom change makes the result mathlib-shaped.

---

### Diamond / defeq risk — `zpPow_zetaSys_mem_cycloClosureOne`

n/a — declaration kind is `theorem` (introduces no definitional equalities or typeclass-search paths). Phase 4.5 skipped.

---

### Mathlib search-status: `zpPow_zetaSys_mem_cycloClosureOne`

[A] Lean-Finder       — **n/a: not available this session** (no Lean-Finder MCP tool surfaced).
[B] Loogle            `(_ : ℂ_[_]ˣ) ∈ Subgroup.topologicalClosure _`, `zpPow _ _ _ ∈ _` — **n/a: not available this session** (no Loogle MCP tool surfaced; lean-lsp enabled but its tools not exposed). Substituted with exhaustive source grep [D].
[C] LeanSearch        "p-adic power of root of unity in closure of cyclotomic units" — **n/a: not available this session** (no LeanSearch MCP tool surfaced).
[D] Grep mathlib src  `cyclo.*closure` / `cyclotomicUnit` / `localUnits` / `principalUnit` / `zpPow` / `padicPow` / `Iwasawa.*closure` / `Tate.?twist` / `ℂ_\[` over `.lake/packages/mathlib/Mathlib`  — **no hits** for the result. Findings: (i) mathlib's `Mathlib/RingTheory/RootsOfUnity/CyclotomicUnits.lean` is purely algebraic (`IsPrimitiveRoot.associated_sub_one_pow_sub_one_of_coprime` etc. — `ζ^j − 1` associated; no closure, no local units, no `ℂ_[p]`); (ii) `Mathlib/GroupTheory/GroupAction/Iwasawa.lean` is the unrelated group-simplicity Iwasawa criterion; (iii) **no** `localUnits`/`localUnitsOne`/`principalUnit` notion for `p`-adic fields; (iv) **no** `zpPow`/`padicPow` (`ℤ_p`-power of a `1`-unit) anywhere.
[E] Name pattern      grep for `zpPow`, `cycloClosure`, `cycloUnits`, `zetaSys`, `globalUnits`, `localUnitsOne` across mathlib — **no hits**; all are project-local (`projects/PadicLFunctions/...`).

Searched for both:
  - the user's current form (`ξₙ^a ∈ 𝒞_{n,1}`) — not in mathlib.
  - the literature-standard form (closure of cyclotomic/principal units; `ℤ_p`-power lands in closure of a subgroup of principal units) — **the building blocks are in mathlib** (`Subgroup.topologicalClosure`, `Subgroup.isClosed_topologicalClosure`, `image_closure_subset_closure_image`, `closure_mono`, `PadicInt.denseRange_natCast`, `PadicInt.addChar_of_value_at_one`, `PadicInt.continuous_addChar_of_value_at_one`, and the ambient `ℂ_[p] = PadicComplex` in `Mathlib/NumberTheory/Padics/Complex.lean`), but **the assembled statement and every project-specific object in it are not**.

Concluded: **"not in mathlib (all available methods exhausted, plus the literature-standard form)."** Mathlib supplies the *generic topological and `p`-adic primitives* used in the proof, but neither the result nor its constituent definitions (`cycloUnits`, `cycloClosure`, `cycloClosureOne`, `zpPow`, `zetaSys`, `localUnits`, `localUnitsOne`, `globalUnits`) exist in mathlib.

---

### Call sites — `zpPow_zetaSys_mem_cycloClosureOne`

Internal use count: **1** (within the project, not counting the declaring file).
External-to-file callers: 1 distinct file (`IwasawaProof/Main.lean`).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| `PadicLFunctions/IwasawaProof/Main.lean:106` | `exact zpPow_zetaSys_mem_cycloClosureOne p hn a (ha n hn)` — discharges the levelwise membership in `ZpOne_le_cycloTower1 : ZpOne p ≤ cycloTower1 p` (the `ℤ_p(1) ⊆ 𝒞_{∞,1}` inclusion, RJW §12.5 injectivity sub-lemma). |
| `PadicLFunctions/IwasawaProof/Main.lean:100` | docstring reference (names the lemma as the closure step). |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `zpPow_zetaSys_mem_cycloClosureOne`?):
  - (none) — but note the sibling `zpPow_mem_cycloUnits_topologicalClosure` (line 631) runs the *same density argument* for a general base; the two share the technique deliberately (the docstring at line 628 says so), not a duplication of *this* statement.

What the call-sites pattern tells us: **K = 1 internal use only** — the single-consumer pattern leans toward "possibly the wrong abstraction / could be inlined", *but* the consumer is the project's flagship Iwasawa-main-conjecture inclusion and the proof is a substantive 37-line argument (not inlinable as a one-liner). So the K=1 signal here means "internal scaffolding for one proof", reinforcing project-specificity rather than mathlib-readiness.

---

### Composition check (Phase 6)

Can `zpPow_zetaSys_mem_cycloClosureOne` be derived from mathlib in ≤3 chained calls?

Attempt 1: assemble from `image_closure_subset_closure_image` + `PadicInt.denseRange_natCast` + `closure_mono` + `Subgroup.isClosed_topologicalClosure`.
  - Mathlib decls used: the four above, plus `PadicInt.addChar_of_value_at_one`, `Units.continuous_iff`.
  - Result: **fails as a ≤3-call composition.** The actual proof is ~37 lines: it (a) establishes continuity of `c ↦ zpPow ξₙ c` through the `addChar` representation, (b) builds the continuous unit-valued map `F c = ⟨ξₙ^c, ξₙ^{−c}⟩` with two `zpPow_add`/`zpPow_natCast` side-conditions, (c) rewrites `range F = F '' closure(range ℕ-cast)` and pushes through `image_closure_subset_closure_image` + `closure_mono`, (d) discharges `F(ℕ) ⊆ 𝒟_n` via the project lemma `zetaSysU_pow_mem_cycloUnits`, and (e) separately obtains the principal-unit part from `zpPow_mem_localUnitsOne` + `zetaSysU_mem_localUnitsOne`. This is a genuine multi-`have` proof with non-trivial reasoning between steps — a proof, not a composition (per the Phase 6b heuristics: "multiple `have`s with non-trivial reasoning between" → NO).
  - Notes: every intermediate object (`cycloUnits`, `zetaSysU`, `zpPow`, `localUnitsOne`) is project-local; mathlib supplies only the generic topology lemmas.

Attempt 2: cite a single project-internal lemma. The closest is `zpPow_mem_cycloUnits_topologicalClosure` (general-base version) — but that is **project code, not mathlib**, and even using it one still needs the principal-unit part and the `ξₙ^k ∈ 𝒟_n` input. Not a mathlib composition.

Conclusion: **NOT-COMPOSABLE** (from mathlib). Phase 7 therefore does not consider NO-composable-from-mathlib; it weighs the YES verdicts vs BORDERLINE.

---

## Verdict: `zpPow_zetaSys_mem_cycloClosureOne`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature search (Phase 3): the *closure of cyclotomic units in the local principal units* is a standard Iwasawa object (Iwasawa 1968; Mazur–Wiles; Rubin; Coates–Sujatha; source paper arXiv:2309.15692), but the precise membership lemma `ξₙ^a ∈ 𝒞_{n,1}` is **not a separately-named result** anywhere — it is a routine internal density step. No single literature-standard atomic form emerged.
- Generality analysis (Phase 4): STRICTLY NARROWER (fixed base `zetaSys`, project-specific subgroup `cycloUnits`), but the generalisation stays over project-local objects and is already realised internally by `zpPow_mem_cycloUnits_topologicalClosure`. Phase 4c found no modernisation move toward mathlib (already idiomatic).
- Mathlib search (Phase 5): not in mathlib; mathlib supplies the generic primitives (`Subgroup.topologicalClosure`, `image_closure_subset_closure_image`, `PadicInt.addChar_of_value_at_one`, `PadicComplex`) but **none of the project-specific definitions** in the statement.
- Composition check (Phase 6): NOT-COMPOSABLE (a 37-line multi-`have` density proof, not a ≤3-call mathlib composition). Call sites: K = 1 (the flagship `ZpOne_le_cycloTower1`).

**Rationale (1–2 paragraphs):**

The theorem is true, sorry-free, cleanly proved in modern mathlib idiom, and *not* in mathlib — and yet it should not be shipped to mathlib in its current form, because every object it mentions is bespoke to this project's rendering of the RJW paper (arXiv:2309.15692). The statement is built from `zetaSys` (a *fixed, choice-extracted* compatible system of primitive roots of unity), `cycloUnits`/`cycloClosure`/`cycloClosureOne` (the RJW-specific cyclotomic-unit groups and their `ℂ_[p]`-closures, defined with the project's R11.7 "everything inside `ℂ_[p]`" convention rather than the textbook local field `K_n`), `zpPow` (the project's `ℤ_p`-power of a `1`-unit), and the project's `localUnits`/`localUnitsOne` tower. None of these is a mathlib definition. Mathlib's own `CyclotomicUnits` file is purely the algebraic `ζ^j − 1`-associated theory; its `Iwasawa` file is the unrelated group-simplicity criterion. So this is not "a missing mathlib lemma" — it is internal scaffolding for one specific Iwasawa-main-conjecture proof (its single consumer is `ZpOne_le_cycloTower1`, the `ℤ_p(1) ⊆ 𝒞_{∞,1}` inclusion).

This is precisely the situation of the verdicts-doc Case 5 (`localZetaSum_chebotarev`): a specialised analytic-number-theory object, no single literature-standard atomic form, and membership turning on whether the underlying definitions are meant to be public reusable mathlib API or project-local bookkeeping. The mathlib-worthy *kernel* here is generic — "in an abelian topological group, the `ℤ_p`-power of a `1`-unit lying in a subgroup's closure stays in that closure" — and *that* (the `zpPow_mem_cycloUnits_topologicalClosure` shape, abstracted away from `cycloUnits`) could conceivably be a mathlib contribution **only if** `zpPow` itself (the `ℤ_p`-power of a `1`-unit via `addChar_of_value_at_one`) is first promoted to mathlib as a named operation with its API. Whether to invest in that upstreaming, and at what generality, is a judgment call about project scope and `zpPow`'s general utility that the skill cannot make alone. Hence BORDERLINE rather than a self-resolving NO or YES.

**Numbered questions (≤5):**

1. Is `zpPow` (the `ℤ_p`-power `y^a` of a principal `1`-unit, `a ↦ (1+(y−1))^a` via mathlib's `PadicInt.addChar_of_value_at_one`) intended to be reusable beyond this project — i.e. would you upstream `zpPow` + its API (`zpPow_add`, `zpPow_natCast`, continuity, `zpPow_mem_localUnitsOne`) to mathlib as the canonical "`ℤ_p`-power of a `1`-unit"? If **no**, this theorem stays project-local (drop from mathlib consideration). If **yes**, proceed to Q2.
2. Assuming `zpPow` is upstreamed: is the *generic* closure lemma `zpPow_mem_cycloUnits_topologicalClosure` (general base `y`, any subgroup whose closure is `zpPow`-stable — abstracting away `cycloUnits`/`zetaSys`) the form worth contributing, with **this** `zetaSys`/`𝒟_n` theorem remaining a project-local instance? (The generic lemma is the mathlib-shaped kernel; the `zetaSys` specialisation is not.)
3. The whole development hard-codes the ambient field as `ℂ_[p]` (`PadicComplex`) per decision R11.7, rather than an abstract complete non-archimedean field or the local field `K_n`. For a mathlib `zpPow`/closure API, should the base ring be a general complete normed/ultrametric field (mathlib idiom) rather than `ℂ_[p]`? (This would be the real generalisation cost.)
4. Are `cycloUnits`/`cycloClosure`/`cycloClosureOne` and the `localUnits` tower meant to ever be public mathlib API, or are they permanently project-internal RJW bookkeeping? (If permanently internal, every theorem stated in terms of them — including this one — is automatically out of mathlib scope regardless of Q1–Q3.)

**Next action:** user answers the questions; re-run `/mathlibable zpPow_zetaSys_mem_cycloClosureOne` to resolve. Likely outcomes based on the answers:
  - `zpPow` stays project-local (Q1 = no) **or** the local-unit definitions are permanently internal (Q4 = internal) → drop this theorem from mathlib consideration entirely; it is correct, useful, project-internal scaffolding and belongs exactly where it is.
  - `zpPow` + the generic closure lemma are wanted in mathlib (Q1 = yes, Q2 = generic form) → contribute `zpPow` and `zpPow_mem_cycloUnits_topologicalClosure` (re-aimed at a general complete non-archimedean field per Q3) as a `YES-but-generalise-first` package; **this** `zetaSys`/`𝒟_n` theorem remains a project-local instance of the upstreamed generic lemma (still NO for mathlib).

---

## Next step

User answers questions 1–4 above; re-run `/mathlibable zpPow_zetaSys_mem_cycloClosureOne` to resolve. As written — a specific-`zetaSys`, specific-`cycloUnits`, `ℂ_[p]`-fixed membership lemma with a single internal consumer — it is not a mathlib contribution; the mathlib-worthy kernel (if any) is the generic `zpPow` operation plus the abstract closure-stability lemma, whose upstreaming is the judgment the questions surface.
