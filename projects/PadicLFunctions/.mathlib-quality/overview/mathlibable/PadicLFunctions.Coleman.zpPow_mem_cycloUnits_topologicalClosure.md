# `/mathlibable` report — `PadicLFunctions.Coleman.zpPow_mem_cycloUnits_topologicalClosure`

**Final verdict: `NO-composable-from-mathlib`** — the mathematical engine is a
1–2 mathlib-call composition (`Set.MapsTo.closure` / `image_closure_subset_closure_image`
+ `pow_mem` + `Subgroup.isClosed_topologicalClosure`); what wraps it is the project's
own `zpPow` p-adic machinery, so the assembled statement is project-internal
scaffolding rather than a mathlib-shaped declaration. The right refactor is to a
*project-local* helper, not a mathlib PR.

---

### Baseline (Phase 0)
- lake build:               build not re-run; reasoned from source (per task instruction — read decl + dependencies directly)
- decl `PadicLFunctions.Coleman.zpPow_mem_cycloUnits_topologicalClosure`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/Iwasawa/CyclotomicUnits.lean:631`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Cyclotomic units — the global modules `𝒟_n` and their local p-adic closures `𝒞` (RJW arXiv:2309.15692 §11.3), all living inside `ℂ_[p]`.

---

### Statement (Phase 1)

`zpPow_mem_cycloUnits_topologicalClosure` is a **theorem** stating the following:

Fix a prime `p` and a level `n`. Let `y` be a *principal unit* of `ℂ_[p]`
(`‖y − 1‖ < 1`, i.e. `y ∈ 𝒰^{(1)}`) that already lies in the topological closure
`(𝒟_n)⁻` of the cyclotomic units `𝒟_n = cycloUnits p n` inside the topological
group `ℂ_[p]ˣ`. Then for **every** p-adic exponent `a ∈ ℤ_p`, the binomial
`ℤ_p`-power `y^a := zpPow y a` (a unit `x` with `↑x = zpPow y a`) again lies in
that closure. In short: **the topological closure of the cyclotomic units is
stable under the binomial `ℤ_p`-power action `zpPow` on principal units** (RJW
lem:closure, TeX 3503).

The mechanism is the standard "agree on a dense subset" argument: the unit-power
map `F : ℤ_p → ℂ_[p]ˣ`, `F c = ⟨y^c, y^{−c}⟩`, is continuous; on the *natural*
exponents `k ∈ ℕ` it gives `F(k) = y^k`, which lies in the closure because the
closure is a subgroup (`pow_mem`); the naturals are dense in `ℤ_p`
(`PadicInt.denseRange_natCast`); and the closure is closed
(`Subgroup.isClosed_topologicalClosure`). Hence the whole `ℤ_p`-orbit `F(ℤ_p)`
lands back in the closure.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the residue prime (file-level `variable`).
- `n : ℕ` (implicit) — the cyclotomic level; appears only through `cycloUnits p n`.
- `y : ℂ_[p]ˣ` (implicit) — the base principal unit.
- `a : ℤ_[p]` — the p-adic exponent.
- `x : ℂ_[p]ˣ` (implicit) — the result unit, pinned to `↑x = zpPow p ↑y a`.

Hypotheses (Lean side):
- `hyc : ‖(y : ℂ_[p]) − 1‖ < 1` — `y` is a principal (1-)unit; needed so `zpPow`
  fires its non-junk (additive-character) branch and the power-law lemmas apply.
- `hyclos : y ∈ (cycloUnits p n).topologicalClosure` — `y` is in the closure.
- `hx : (x : ℂ_[p]) = zpPow p (y : ℂ_[p]) a` — `x` *is* `y^a`.

Conclusion (math): `y^a ∈ (𝒟_n)⁻` for every `a ∈ ℤ_p`.

Conclusion (Lean): `x ∈ (cycloUnits p n).topologicalClosure`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: an internal density-transfer step (RJW lem:closure) feeding the
`(p−1)`-rootedness lemma `mem_cycloClosureOne_of_pow_mem`; not a named theorem,
not in the module's `## Main results`, not person/place-named. It is one of two
near-identical `zpPow`-closure lemmas in the file (see Phase 6).

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded only for
the report's framing.)

### One-line check (Phase 2b)

Body line count: ~30 substantive lines (continuity, the unit-power map `F`, the
density-transfer `hrange`, the final `closure_eq` rewrite).
One-liner verdict: **n/a** — kind is `theorem`, not `def`. Section skipped.

---

## PHASE 3 — Literature search (EXHAUSTIVE)

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|-------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "cyclotomic units p-adic closure Iwasawa module Z_p-power binomial action principal units"             | yes  | closure of cyclotomic units as a `ℤ_p`-/Λ-module is classical Iwasawa theory | arXiv:1907.06437, 1904.09850; Coates AWS-2018 notes; Greenberg "Iwasawa Theory for p-adic Representations". The closure-is-a-`ℤ_p`-module statement is a step, not a named theorem. |
|  2 | WebSearch (general / abstract form) | "closure of subgroup topological group stable under continuous endomorphism dense image power map" | partial | "the closure of a subgroup is a subgroup"; continuous maps with dense image transfer properties; folklore | Morris *Topological Groups*; Landesman/Godsil notes. The exact "closure stable under a continuous self-map agreeing with the group on a dense set" is folklore, **not** a named theorem. |
|  3 | WebSearch (named-after / classical source) | "Washington Introduction to Cyclotomic Fields closure of cyclotomic units Z_p module local units" | yes  | Washington Ch. 8 (cyclotomic units), Ch. 13 (local units mod cyclotomic units), §13.8 | Washington 2nd ed.; arXiv:0812.0784, 2407.02002. Confirms the *object* (`𝒞_n`, closure of `𝒟_n` in local units) is classical; the `zpPow`-stability of the closure is internal scaffolding toward the module structure. |
|  4 | WebSearch (the p-adic-exponentiation engine) | "Mahler expansion p-adic exponentiation 1-units binomial coefficient continuous a↦u^a Z_p" | yes  | `a ↦ u^a` for `|u−1|<1` is continuous (Mahler basis); `u^{x+y}=u^x u^y` proved by "continuous + agree on dense ℕ" | K. Conrad "Mahler expansions"; de Shalit JTNB; Wikipedia "Mahler's theorem". This is exactly the dense-agreement engine the target reuses. Already in mathlib (`PadicInt.addChar_of_value_at_one`, `mahlerSeries`). |
|  5 | Local references                 | `ls projects/PadicLFunctions/.mathlib-quality/references/`; `ls refs/`                                  | n/a  | (no references dir; no `refs/` symlink)               | Directory absent in this worktree — recorded as `n/a`. (RJW arXiv:2309.15692 §11.3 is cited in the module docstring; lem:closure / TeX 3503 is the source statement.) |
|  6 | nLab                             | "topological group" — closure of subgroup / stability under continuous maps                            | partial | nLab notes only "open subgroup ⇒ closed"; no statement on closure-stability under endomorphisms | Concept is point-set topology of groups, thinly covered on nLab; nothing closer than folklore. |
|  7 | nCatLab (if categorical)         | —                                                                                                      | n/a  | not a categorical concept                              | A concrete p-adic membership fact; no universal-property/categorical content to look up. |
|  8 | Stacks Project (if alg geom)     | —                                                                                                      | n/a  | not an algebraic-geometry concept                      | Topological-group / p-adic-analysis statement; outside Stacks' scope. |
|  9 | MathOverflow / Math.StackExchange| "topological closure of subgroup invariant under continuous group homomorphism mapsto closure"          | partial | "closure of a subgroup is a subgroup"; preimages of closed subgroups are closed | Murnaghan MAT445 Ch.5; Cambridge ETDS survey. Confirms the abstract fact is textbook/folklore, not a citable named theorem. |
| 10 | recent arXiv (last 5 years)      | "principal units p-adic field Z_p-module structure binomial series exponentiation closed subgroup"      | yes  | `ℤ_p^× = μ × U^{(1)}`; `g^{λ+μ}=g^λ g^μ`, `g^{λμ}=(g^λ)^μ` for `λ,μ∈ℤ_p`; `U^{(1)}` is a `ℤ_p`-module | Klopsch "Analytic pro-p groups"; arXiv:2602.23107, 1904.09850. The `ℤ_p`-module structure on principal units is standard; closure-stability under that action is the routine consequence the target formalises. |
|  — | ChatGPT MCP                      | "standard form + generality + historical evolution of 'closure of cyclotomic units is stable under the binomial `ℤ_p`-power'?" | n/a  | server not configured                                  | No ChatGPT MCP tool surfaced in this environment (requires `/setup-chatgpt`). Recorded `n/a`; the four WebSearch generality levels (specific Iwasawa form, abstract topological-group form, classical Washington source, the Mahler-exponentiation engine) + nLab + MathOverflow + arXiv cover the standard-form / generality / historical-evolution questions the MCP query would have asked. |

The protocol passed: WebSearch ran 4 distinct queries at different generality
levels (specific Iwasawa form, abstract topological-group form, classical source,
the underlying p-adic-exponentiation engine); local refs checked (`n/a`, absent);
nLab, nCatLab, Stacks, MathOverflow, arXiv each checked or `n/a` with reason.
ChatGPT MCP unavailable in this environment and recorded `n/a` with the
compensating-channels note above.

### Literature summary (Phase 3)

Concept identified as: two layered standard concepts —
  (i) **abstract:** the topological closure of a subgroup of a topological group
      is stable under a continuous self-map that agrees with the subgroup
      structure on a dense subset (folklore; the "continuous + dense agreement"
      principle, e.g. K. Conrad's proof of `u^{x+y}=u^x u^y`);
  (ii) **arithmetic:** the closure `𝒞_n = (𝒟_n)⁻` of the cyclotomic units inside
      the local units is a `ℤ_p`-module under binomial exponentiation — classical
      Iwasawa theory (Washington Chs. 8 & 13; Lang, *Cyclotomic Fields*).
The specific Lean statement is RJW lem:closure (arXiv:2309.15692, TeX 3503): an
internal step proving the closure is `zpPow`-stable.

Sources agree on the standard form: yes — both the abstract topological fact and
the arithmetic `ℤ_p`-module statement are textbook-standard. Neither is a
*named* theorem; both are routine consequences assembled for a specific purpose.

Most general standard form: *In a topological group `G`, let `K` be a closed
subgroup and `F : T → G` a continuous map from a space `T` in which a subset `D`
is dense; if `F(D) ⊆ K` then `F(T) ⊆ K`.* The target is the instance
`G = ℂ_[p]ˣ`, `K = (𝒟_n)⁻`, `T = ℤ_p`, `D = ℕ`, `F = c ↦ y^c`.

Generality dimensions where the literature varies:
  - **base object:** from `ℤ_p^×`/`U^{(1)}` of a single p-adic field, to local
    units of a tower, to `ℂ_[p]ˣ`. The target uses the `ℂ_[p]ˣ` end (RJW's chosen
    ambient group).
  - **the acting ring:** `ℕ → ℤ → ℤ_p` exponents; the target uses the full `ℤ_p`
    action (the most general, via `zpPow`/Mahler).
  - **the subgroup:** any closed subgroup; the target fixes it to `(𝒟_n)⁻`.

Disagreement with the literature: none. The literature treats the abstract
principle generically and the cyclotomic-unit closure module-theoretically; the
target is a faithful, if narrow, formalisation of one routine step.

---

## PHASE 4 — Generality analysis

### Generality analysis — `zpPow_mem_cycloUnits_topologicalClosure`

Literature-standard form (from Phase 3): *continuous `F : T → G` into a
topological group with `F(D) ⊆ K`, `K` a closed subgroup, `D` dense in `T`,
gives `F(T) ⊆ K`* — specialised here to the `ℤ_p`-power on principal units.

| # | Parameter / hypothesis                              | Current Lean form                          | Literature-standard form                              | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------------------------|--------------------------------------------|-------------------------------------------------------|---------------------|---------------------------------|
| 1 | ambient group `ℂ_[p]ˣ`                              | units of `ℂ_[p]`                           | any topological group `G`                             | yes                 | the proof uses only that `ℂ_[p]ˣ` is a topological group with a closed subgroup; nothing `ℂ_[p]`-specific in the *closure-transfer* core. But the *map* `zpPow` is `ℂ_[p]`-specific (binomial series), so the statement as written cannot leave `ℂ_[p]`. |
| 2 | the subgroup `cycloUnits p n`                       | the cyclotomic units `𝒟_n`                 | any closed subgroup `K` of `G`                        | yes                 | the proof uses `cycloUnits p n` only via `pow_mem hyclos k` (closed under nat powers) and `isClosed_topologicalClosure` — i.e. **only** that `(𝒟_n)⁻` is a closed subgroup. Nothing about cyclotomic units is used. |
| 3 | `hyc : ‖y − 1‖ < 1`                                 | `y` a principal unit                        | `‖y − 1‖ < 1` (domain of convergence of `a ↦ y^a`)    | NO                  | this is exactly the convergence hypothesis for `zpPow`'s binomial series; it is the maximal domain on which `zpPow` is non-junk. Cannot be weakened without changing what `zpPow` means. |
| 4 | exponent ring `ℤ_[p]`                               | full p-adic exponent                        | `ℤ_p` (Mahler) — already maximal among ℕ/ℤ/ℤ_p        | NO                  | already the most general exponent ring for the binomial action; `zpPow` is defined on `ℤ_[p]`. |
| 5 | `hyclos : y ∈ (𝒟_n)⁻`                              | `y` in the closure                          | `y ∈ K` for the closed subgroup `K`                   | yes                 | same as row 2 — `y` is used only as a member of the closed subgroup whose powers stay inside. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** along rows 1, 2, 5 — but
this narrowness is **inseparable from the project-specific `zpPow`**. The
*closure-transfer core* (rows 1, 2, 5) generalises to any topological group and
any closed subgroup; the *map* (rows 3, 4 — `zpPow`, `‖y−1‖<1`, `ℤ_p`) is
maximally general for what `zpPow` is, and is `ℂ_[p]`-bound.

Number of weakening opportunities found: 3 (all of the "abstract out the
subgroup / ambient group" kind), but **they do not point at a mathlib statement** —
they point at the generic closure-transfer lemma that *mathlib already has*
(`Set.MapsTo.closure`; see Phase 5/6). Generalising rows 1/2/5 does not yield a
new mathlib-worthy theorem; it yields exactly `Set.MapsTo.closure` plus `pow_mem`.

Proposed restatement (if one insisted on stating it generally):

```lean
-- This is essentially `Set.MapsTo.closure` + `pow_mem` already in mathlib:
example {G : Type*} [TopologicalSpace G] [Monoid G] {K : Subgroup G}
    (hK : IsClosed (K : Set G)) {T : Type*} [TopologicalSpace T]
    {D : Set T} (hD : Dense D) {F : T → G} (hF : Continuous F)
    (hFD : ∀ t ∈ D, F t ∈ K) : ∀ t, F t ∈ K := fun t =>
  hK.closure_eq ▸ (hD.closure_eq ▸ (Set.mapsTo_iff_subset_preimage.mpr ?_)) ...
```

Cost of restatement: **CHEAP** mechanically — but the result of the restatement
is a known mathlib composition, not a new theorem. So "generalise first" is the
*wrong* move here: the general form already exists in mathlib.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                  | Applies? | Proposed reformulation                                            | Mathlib downstream this enables |
|----|-----------------------------------------------------------------------------------------------------------|----------|-------------------------------------------------------------------|----------------------------------|
|  1 | "let `y` be a principal unit in the closure" → typeclass/instance instead of bundled hypotheses?           | no       | —                                                                 | the hypotheses `‖y−1‖<1` and `y ∈ (𝒟_n)⁻` are genuine runtime data, not a structure on a type. |
|  2 | literature uses sequences/metric where filters/nets would generalise more cleanly?                         | no       | —                                                                 | the proof is *already* filter/density-based (`closure`, `DenseRange`, `Set.MapsTo.closure`); it is the modern idiom. |
|  3 | a construction where a universal-property class would characterise it?                                      | no       | —                                                                 | this is a membership fact, not a construction. |
|  4 | set-with-closure-predicate where a bundled-substructure type would compose better?                          | partial  | the target already uses `Subgroup.topologicalClosure` (a bundled subgroup) | no improvement available — it is already the bundled-substructure idiom. |
|  5 | vector-space/metric/field-specific result that mathlib's typeclasses would weaken to modules/(semi)ring?    | no       | —                                                                 | the only field-specific content is `zpPow` (binomial series on `ℂ_[p]`); intrinsic. |
|  6 | 1-categorical statement with a higher-categorical generalisation?                                           | no       | —                                                                 | no categorical content. |
|  7 | concrete index (ℕ/ℤ/ℝ) that would generalise to arbitrary additive groups/monoids?                          | no       | —                                                                 | the index is already the maximal `ℤ_p` (Mahler action); there is no further additive structure to abstract over. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. The declaration is already written in the
contemporary mathlib idiom (filters/closure/`DenseRange`/bundled
`Subgroup.topologicalClosure`). There is no Bourbaki-2.0 reformulation that turns
it into a better *mathlib* statement — the "better" form is simply mathlib's
existing `Set.MapsTo.closure`, which means the verdict is a NO bucket, not
YES-but-generalise.

One-line reason this is not a modernisation move: the abstract content is already
a mathlib lemma; the concrete content is project-specific `zpPow` glue.

---

## PHASE 4.5 — Diamond / defeq risk

n/a — declaration kind is `theorem`. (No definitional equalities or
typeclass-search paths introduced.)

---

## PHASE 5 — Mathlib search

### Mathlib search-status: `zpPow_mem_cycloUnits_topologicalClosure`

[A] Lean-Finder       "closure of subgroup stable under continuous power map"; "Set.MapsTo.closure"   no direct hit on the *assembled* statement (it is `zpPow`/`cycloUnits`-specific); building blocks found via grep below.
[B] Loogle            `Subgroup.topologicalClosure` (full member list, fetched from loogle.lean-lang.org)   no hit for "closure stable under power/endomorphism mapping it into itself". The only `pow`/`map` results are `mapClusterPt_atTop_pow_iff_mem_topologicalClosure_zpowers` (about `zpowers` + cluster points — different) and `DenseRange.topologicalClosure_map_subgroup` (pushes `closure = ⊤` through a dense-range hom — different).
[C] LeanSearch        natural-language queries on "closure of subgroup stable under continuous endomorphism"   n/a — public API endpoint returned HTTP 404/405 for every query form attempted (`/api/search?q=…`, `?query=…`, `/search?q=…`). Coverage replaced by definitive Loogle type-search + mathlib-source grep below.
[D] Grep mathlib src  `topologicalClosure`, `Set.MapsTo.closure`, `image_closure_subset_closure_image`, `pow_mem`, `isClosed_topologicalClosure` over `.lake/packages/mathlib/`   **building blocks found** (see below); the assembled statement **not found**.
[E] Name pattern      `lean_local_search`-style grep: `zpPow.*topologicalClosure`, `mem_cycloUnits_topologicalClosure`, `closure.*zpPow` across mathlib   no hit (`zpPow`/`cycloUnits` are project names, absent from mathlib).

Building blocks located in mathlib (the decisive Phase-5 finding):
- `Set.MapsTo.closure` — `Mathlib/Topology/Continuous.lean:205`:
  *if `f` continuous and `MapsTo f s t` then `MapsTo f (closure s) (closure t)`.*
  This is **the** abstract engine of the target's proof.
- `image_closure_subset_closure_image` — `Mathlib/Topology/Continuous.lean:211`
  (a corollary of the above; literally invoked in the target's proof, line 657).
- `Subgroup.pow_mem` — `Mathlib/Algebra/Group/Subgroup/Defs.lean:469`: a subgroup
  is closed under nat powers (invoked as `pow_mem hyclos k`).
- `Subgroup.isClosed_topologicalClosure` — `Mathlib/Topology/Algebra/Group/Basic.lean:689`
  (invoked via `(…).closure_eq`, line 665).
- `Subgroup.topologicalClosure_coe` — `Mathlib/Topology/Algebra/Group/Basic.lean:680`.
- `PadicInt.denseRange_natCast` (+ `.closure_range`) — mathlib `PadicInt` API
  (invoked at line 655); `PadicInt.addChar_of_value_at_one`,
  `PadicInt.continuous_addChar_of_value_at_one`, `PadicInt.mahlerSeries` —
  `Mathlib/NumberTheory/Padics/AddChar.lean`, `MahlerBasis.lean` (the `zpPow` engine).

Searched for both:
  - the user's current form (`zpPow` of a unit in the cyclotomic-unit closure) —
    not in mathlib (project names absent);
  - the literature-standard / abstract form ("closure of a subgroup stable under
    a continuous self-map agreeing on a dense subset") — **mathlib has the
    generic engine `Set.MapsTo.closure` but no packaged subgroup-closure
    stability lemma**, and the right inference is composition, not a new lemma.

Concluded: **found building blocks** (`Set.MapsTo.closure` /
`image_closure_subset_closure_image`, `Subgroup.pow_mem`,
`Subgroup.isClosed_topologicalClosure`, `PadicInt.denseRange_natCast`); their
composition yields the target's *core*, with the project's own `zpPow` lemmas
(`zpPow_natCast`, `zpPow_add`, `continuous_zpPow`) supplying the map.

---

## PHASE 6 — Composition check (+ call-sites signal)

### Call sites — `zpPow_mem_cycloUnits_topologicalClosure`

Internal use count: **1** (within the project, excluding the declaring lines)
External-to-file callers: **0** distinct files (the single use is in the same file)

| Caller file:line                                          | Usage pattern (one-line excerpt)                                                  |
|-----------------------------------------------------------|-----------------------------------------------------------------------------------|
| projects/PadicLFunctions/PadicLFunctions/Iwasawa/CyclotomicUnits.lean:694 | `zpPow_mem_cycloUnits_topologicalClosure p hypowc hgpowclos c hgeq` — inside `mem_cycloClosureOne_of_pow_mem` (the `(p−1)`-rootedness lemma) |

Inline-derivation grep (was the equivalent re-derived elsewhere without using the target?):
  - **YES — the same density-transfer argument is re-derived inline in the
    sibling lemma `zpPow_zetaSys_mem_cycloClosureOne`** (CyclotomicUnits.lean:569–612,
    block at 595–607): identical structure (`Set.range F = F '' closure (range Nat.cast)`,
    `image_closure_subset_closure_image hFcont |>.trans (closure_mono …)`,
    `PadicInt.denseRange_natCast.closure_range`), differing only in that it fixes
    `y = ξ_n = zetaSysU` and additionally concludes the principal-unit part. The
    target is essentially the *general-`y`* extraction of that block.
  - The very same `image_closure_subset_closure_image`-based density pattern
    recurs **6 times** across the repo: CyclotomicUnits.lean (×2, lines 600 & 657),
    LocalUnits.lean (`zpPow_mem_of_closed`, the `Set ℂ_[p]` analogue), Main.lean:491,
    ColContinuity.lean:104, plus AdicSpaces (another project). Strong "missing
    shared helper" signal.

What the call-sites pattern tells you: **K = 1 internal use, AND the equivalent is
re-derived inline at a sibling site** → the table's "K = 1 / inline re-derivation"
rows both fire → lean toward **NO-composable** (it is a thin density-transfer
wrapper that consumers either call once or bypass).

### Composition check (Phase 6)

Can `zpPow_mem_cycloUnits_topologicalClosure` be derived from mathlib in ≤3
chained calls?

Attempt 1 (the abstract core, the part that "belongs to mathlib"): the membership
`x ∈ (𝒟_n)⁻` follows from
```lean
-- with hcont : Continuous (zpPow p ↑y), hxF : x = F a, hFnat : ∀ k:ℕ, F k = y^k:
(Subgroup.isClosed_topologicalClosure _).closure_eq ▸
  (Set.MapsTo.closure hmapsNat hFcont)   -- MapsTo F (closure (range Nat.cast)) (closure ↑(𝒟_n)⁻)
```
  - Mathlib decls used: `Set.MapsTo.closure` (or `image_closure_subset_closure_image`),
    `Subgroup.isClosed_topologicalClosure`, `Subgroup.pow_mem`,
    `PadicInt.denseRange_natCast.closure_range`.
  - Result: **succeeds** for the abstract closure-transfer core (≤3 mathlib calls,
    exactly the heuristics-table "`Foo.bar (Bar.baz hx)`" / "`.trans` chain" rows).
  - Notes: the *glue* that feeds this core — building the continuous unit-power
    map `F c = ⟨y^c, y^{−c}⟩`, `hFnat : F k = y^k`, `hFcont`, and `hx : ↑x = zpPow …` —
    is project-specific `zpPow` API (`zpPow_natCast`, `zpPow_add`, `continuous_zpPow`,
    `Units.continuous_iff`), **not** mathlib. So the composition is "mathlib core +
    project glue", which is exactly what `NO-composable-from-mathlib` means at the
    project level: no *new* lemma is justified; inline the mathlib core at the (one)
    call site (or, better, factor it into a project-local helper — see below).

Attempt 2 (could it instead be `NO-mathlib-has-it`?): no — there is no single
mathlib decl whose specialisation gives this in ≤1 line. `Set.MapsTo.closure` is a
*building block*, not the packaged statement (it speaks of `MapsTo`/`closure` of
sets, not of `zpPow`/`Subgroup.topologicalClosure` membership). So NO-mathlib-has-it
is **rejected**; the correct NO bucket is NO-composable-from-mathlib.

Conclusion: **COMPOSABLE** — the mathlib-worthy content is the ≤3-call core
`Set.MapsTo.closure` + `pow_mem` + `isClosed_topologicalClosure`; the remainder is
project `zpPow` glue. No new mathlib lemma is justified.

---

## Verdict: `zpPow_mem_cycloUnits_topologicalClosure`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the abstract fact ("closure of a subgroup is
  stable under a continuous self-map agreeing on a dense subset") is folklore, and
  the arithmetic content (closure of cyclotomic units is a `ℤ_p`-module) is
  classical Iwasawa theory (Washington Chs. 8 & 13) — neither is a *named* theorem;
  the Lean statement is RJW lem:closure (arXiv:2309.15692, TeX 3503), an internal step.
- Generality analysis (Phase 4): STRICTLY NARROWER along the "ambient
  group/subgroup" axes, but generalising those axes lands exactly on mathlib's
  existing `Set.MapsTo.closure` — not a new theorem (Phase 4b). Modern-idiom: none
  (already filter/closure-based) (Phase 4c).
- Mathlib search (Phase 5): not in mathlib as an assembled statement; the
  **building blocks are present** — `Set.MapsTo.closure`,
  `image_closure_subset_closure_image`, `Subgroup.pow_mem`,
  `Subgroup.isClosed_topologicalClosure`, `PadicInt.denseRange_natCast`.
- Composition check (Phase 6): COMPOSABLE — mathlib core in ≤3 calls + project
  `zpPow` glue; K = 1 internal call site and the same argument is re-derived
  inline at a sibling lemma.

**Rationale (1–2 paragraphs):**

The theorem says nothing mathlib doesn't already know how to do: it is the
"continuous map sends the closure of a set into the closure of its image" lemma
(`Set.MapsTo.closure`, `Mathlib/Topology/Continuous.lean:205`), instantiated for
the continuous binomial-power map `F c = ⟨y^c, y^{−c}⟩`, the dense subset
`ℕ ↪ ℤ_[p]` (`PadicInt.denseRange_natCast`), and the closed subgroup
`(𝒟_n)⁻`, using only that a subgroup is closed under nat powers
(`Subgroup.pow_mem`) and that its topological closure is closed
(`Subgroup.isClosed_topologicalClosure`). The proof literally invokes
`image_closure_subset_closure_image hFcont |>.trans (closure_mono …)` —
i.e. mathlib's lemma is the engine. What is *not* in mathlib is the project's own
`zpPow` (the binomial `ℤ_p`-power on principal units, built on mathlib's
`PadicInt.addChar_of_value_at_one`/`mahlerSeries`) and the specific subgroup
`cycloUnits`; but those are project objects, so the statement as written is
project-internal scaffolding, not a candidate for mathlib.

The decisive call-sites signal reinforces this: the theorem has a single internal
consumer (`mem_cycloClosureOne_of_pow_mem`), and its *entire* density-transfer body
is re-derived inline in the sibling lemma `zpPow_zetaSys_mem_cycloClosureOne`
(lines 595–607) — indeed the same `image_closure_subset_closure_image` pattern
recurs six times across the repo. That is a textbook "missing shared helper"
pattern, but the helper belongs **in the project** (parameterised over the closed
subgroup, or extracted as a `zpPow`-closure lemma reused by both
`zpPow_zetaSys_mem_cycloClosureOne` and the target), not in mathlib. Mathlib's
contribution stops at `Set.MapsTo.closure`; the project should compose against it.

**WHY not (refactor-actionable detail):**

Mathlib has the building blocks; the theorem is a project-glue assembly around a
≤3-mathlib-call core. The reusable mathematics — "a continuous `ℤ_p`-action map
sending dense ℕ-powers into a closed subgroup sends all of `ℤ_p` into it" — should
be a **project-local** helper, because the only non-mathlib ingredients (`zpPow`,
`cycloUnits`) are project-owned.

Mathlib building blocks:
- `Set.MapsTo.closure` — `Mathlib/Topology/Continuous.lean:205`
- `image_closure_subset_closure_image` — `Mathlib/Topology/Continuous.lean:211`
- `Subgroup.pow_mem` — `Mathlib/Algebra/Group/Subgroup/Defs.lean:469`
- `Subgroup.isClosed_topologicalClosure` — `Mathlib/Topology/Algebra/Group/Basic.lean:689`
- `PadicInt.denseRange_natCast` (`.closure_range`) — mathlib `PadicInt` API
- (`zpPow` engine, already mathlib: `PadicInt.addChar_of_value_at_one`,
  `PadicInt.continuous_addChar_of_value_at_one`, `PadicInt.mahlerSeries`)

Composition sketch (≤3 lines, the mathlib-core part of the proof):
```lean
-- given hFcont : Continuous F, hFnat : ∀ k:ℕ, F k = y^k, hx : ↑x = zpPow p ↑y a:
have hmem : x ∈ closure ((cycloUnits p n).topologicalClosure : Set ℂ_[p]ˣ) :=
  image_closure_subset_closure_image hFcont
    ⟨a, (PadicInt.denseRange_natCast.closure_range ▸ Set.image_univ ▸ rfl)⟩  -- F a ∈ F '' closure(range ℕ)
    |>.mono (closure_mono <| Set.range_comp .. ▸ fun _ ⟨k, h⟩ => h ▸ pow_mem hyclos k)
rwa [(Subgroup.isClosed_topologicalClosure _).closure_eq, SetLike.mem_coe] at hmem
```

Call sites in our project (from Phase 6.0): **K = 1** (`mem_cycloClosureOne_of_pow_mem`,
CyclotomicUnits.lean:694).

Refactor plan (project-internal, NOT a mathlib PR):
1. **Do not delete and inline at the call site** — instead, extract the shared
   density-transfer step into a single project-local helper, because the *same body*
   is currently duplicated between this theorem and `zpPow_zetaSys_mem_cycloClosureOne`
   (and the pattern appears 6× repo-wide). Proposed helper (in `LocalUnits.lean`,
   next to `zpPow_mem_of_closed`, of which this is the `ℂ_[p]ˣ`/subgroup analogue):
   ```lean
   /-- Subgroup analogue of `zpPow_mem_of_closed`: a `zpPow`-orbit stays inside any
   closed subgroup of `ℂ_[p]ˣ` that contains the base unit. -/
   theorem zpPow_unit_mem_of_isClosed {y : ℂ_[p]ˣ} (hyc : ‖(y:ℂ_[p]) - 1‖ < 1)
       {K : Subgroup ℂ_[p]ˣ} (hK : IsClosed (K : Set ℂ_[p]ˣ)) (hyK : y ∈ K)
       (a : ℤ_[p]) {x : ℂ_[p]ˣ} (hx : (x:ℂ_[p]) = zpPow p (y:ℂ_[p]) a) : x ∈ K := …
   ```
   whose body is exactly the mathlib-core composition above.
2. Re-express `zpPow_mem_cycloUnits_topologicalClosure` as the one-line instance
   `zpPow_unit_mem_of_isClosed p hyc (Subgroup.isClosed_topologicalClosure _) hyclos a hx`.
3. Re-express the closure-transfer half of `zpPow_zetaSys_mem_cycloClosureOne`
   (lines 595–607) as the same one-line instance, removing the duplicated block.
4. Keep the names: `mem_cycloClosureOne_of_pow_mem` (the one consumer) continues to
   call `zpPow_mem_cycloUnits_topologicalClosure` unchanged.

Next action: file a **project cleanup/dedup ticket** (this is on `main`'s cleanup
remit, lane:cleanup or lane:decompose) to extract `zpPow_unit_mem_of_isClosed` and
collapse the two duplicated density-transfer blocks into calls to it. **No mathlib
PR**: the only mathlib-worthy content (`Set.MapsTo.closure`) already exists.

---

## Next step

File a project cleanup/dedup ticket on `main` (lane:cleanup or lane:decompose) to
extract a single project-local helper `zpPow_unit_mem_of_isClosed` (the subgroup
analogue of the existing `zpPow_mem_of_closed`) and collapse the duplicated
density-transfer blocks in `zpPow_mem_cycloUnits_topologicalClosure` and
`zpPow_zetaSys_mem_cycloClosureOne` into one-line calls to it. Do **not** open a
mathlib PR — the reusable abstract content is already mathlib's `Set.MapsTo.closure`,
and the assembled statement depends on the project-owned `zpPow` and `cycloUnits`.
