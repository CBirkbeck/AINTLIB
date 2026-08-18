# `/mathlibable` report — `PadicLFunctions.Coleman.cyclo_mem_unitsTower1`

**Final verdict: `NO-composable-from-mathlib`**

---

### Baseline (Phase 0)

- lake build:               build not re-run; reasoned from source (per task build note — the
  declaration and its entire dependency chain were read directly from
  `projects/PadicLFunctions/PadicLFunctions/Iwasawa/CyclotomicUnits.lean` and `Iwasawa/LocalUnits.lean`;
  both files are `sorry`-free in the relevant region, and the file's only recent commits are the daily
  mathlib bump + golf cleanups, no new math, so it is in a built state).
- decl `PadicLFunctions.Coleman.cyclo_mem_unitsTower1`: resolved at
  `projects/PadicLFunctions/PadicLFunctions/Iwasawa/CyclotomicUnits.lean:495`
- kind:                      theorem
- has sorry:                 no (proof term is total; dependency chain `cycloTower1_le_unitsTower1`,
  `cyclo_mem_cycloTower1`, `cyclo`, `cycloTower1`, `unitsTower1` are all `sorry`-free — `grep -c sorry`
  on `CyclotomicUnits.lean` / `LocalUnits.lean` = 0)
- module docstring summary:  Cyclotomic units — the global modules `𝒟_n` and their local closures `𝒞`
  (RJW arXiv:2309.15692 §11.3); culminates in the milestone (TeX 3084) that the Coleman-map inputs
  `c_n(a)` "are naturally elements of `𝒟_n`, hence global" — `cyclo ∈ 𝒞_{∞,1} ≤ 𝒰_{∞,1}`.

The full text:

```lean
theorem cyclo_mem_unitsTower1 {a : ℕ} (ha : ¬ (p : ℕ) ∣ a) (hp2 : p ≠ 2)
    (ha1 : a ≡ 1 [MOD p]) :
    cyclo p ha hp2 ∈ unitsTower1 p :=
  cycloTower1_le_unitsTower1 p (cyclo_mem_cycloTower1 p ha hp2 ha1)
```

---

### Statement (Phase 1)

`cyclo_mem_unitsTower1` is a theorem stating the following:

For a prime `p ≠ 2` and a natural number `a` coprime to `p` with `a ≡ 1 (mod p)`, the norm-compatible
system of cyclotomic units `c(a) = (c_n(a))_n` — the input of the Coleman map `coleman_to_kl` — belongs
to the principal-local-unit tower `𝒰_{∞,1}`. In symbols: `c(a) ∈ 𝒰_{∞,1}` inside the norm-compatible
system group `𝒰_∞ = NormCompatUnits p` (RJW arXiv:2309.15692, the milestone line TeX 3084 read down to
its `𝒰_{∞,1}` half).

This is the **terminal, weaker corollary** of the milestone. The genuine mathematical content — that the
cyclotomic system actually lands in `𝒞_{∞,1}` (the *cyclotomic* tower: globally cyclotomic, `p`-adically
closed, AND principal at every level via `‖c_n(a) − 1‖ < 1`) — is the *sibling* result
`cyclo_mem_cycloTower1` (CyclotomicUnits.lean:472). Since `𝒞_{∞,1} ≤ 𝒰_{∞,1}` by definition
(`cycloTower1_le_unitsTower1`, CyclotomicUnits.lean:239), this theorem is literally that membership
pushed forward along the inclusion: it carries none of the hard content itself. The hypothesis
`a ≡ 1 (mod p)` is inherited verbatim from `cyclo_mem_cycloTower1` (needed there for the principal-unit
estimate; see the T1113 statement note in the source) and is otherwise unused at this top level.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the fixed prime (section variables).
- `{a : ℕ}` — the exponent / character index of the cyclotomic unit `c_n(a) = (ξ_n^a − 1)/(ξ_n − 1)`.

Hypotheses (Lean side):
- `ha : ¬ (p : ℕ) ∣ a` — `a` is prime to `p` (so `c_n(a)` is a genuine unit).
- `hp2 : p ≠ 2` — excludes `p = 2` (matches `cyclo`'s and the milestone's hypotheses).
- `ha1 : a ≡ 1 [MOD p]` — the principal-unit condition; passed straight through to
  `cyclo_mem_cycloTower1` (needed only there).

Conclusion (math): `c(a) ∈ 𝒰_{∞,1}` — the cyclotomic norm-compatible system is a principal-unit tower.

Conclusion (Lean): `cyclo p ha hp2 ∈ unitsTower1 p`, i.e.
`∀ n, 1 ≤ n → (cyclo p ha hp2).elems n ∈ localUnitsOne p n`.

Key definitional facts (all project-local; `Iwasawa/CyclotomicUnits.lean`, `Iwasawa/LocalUnits.lean`,
`Coleman/Map.lean`):
- `cyclo p ha hp2`            := the `NormCompatUnits p` with `elems n = c_n(a)` (`n ≥ 1`), `1` at `n=0`   (Map.lean:180)
- `unitsTower1 p`             := `{u | ∀ n, 1 ≤ n → u.elems n ∈ localUnitsOne p n}`                       (LocalUnits.lean:479)
- `cycloTower1 p`             := `{u | ∀ n, 1 ≤ n → u.elems n ∈ cycloClosureOne p n}`                     (CyclotomicUnits.lean:226)
- `cycloClosureOne p n`       := `cycloClosure p n ⊓ localUnitsOne p n`                                   (CyclotomicUnits.lean:218–219)
- `cycloTower1_le_unitsTower1`:= `fun _ hu n hn => (Subgroup.mem_inf.1 (hu n hn)).2`                      (CyclotomicUnits.lean:239)
- `cyclo_mem_cycloTower1`     := the milestone `cyclo p ha hp2 ∈ cycloTower1 p` (the hard result)        (CyclotomicUnits.lean:472)

So the whole proof is: take the milestone `cyclo ∈ 𝒞_{∞,1}`, then push along `𝒞_{∞,1} ≤ 𝒰_{∞,1}`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A one-line corollary — the milestone `cyclo_mem_cycloTower1` already proves `cyclo ∈ 𝒞_{∞,1}`,
and `𝒞_{∞,1} ≤ 𝒰_{∞,1}`, so this is `mem_of_le_of_mem` applied to a single project lemma and a single
project inclusion. It is NOT a new structure, NOT a person/place-named theorem, and is itself only the
*weaker half* of the headline (the headline content lives in `cyclo_mem_cycloTower1` /
`norm_cycloUnit_sub_one_lt_one`). It is a sibling of an entire project-internal family of
`*_mem_unitsTower1` / `*_mem_cycloTower1` membership milestones — `galNCU_mem_unitsTower1`
(Generators.lean:1016), `wGamma_mem_unitsTower1` (Generators.lean:1651),
`wGamma_mem_cycloTower1` (Generators.lean:1726), etc.

Caveat: the module docstring (TeX 3084) does call the *combined* statement "the milestone", so a reader
could argue BIG by association. But the milestone's substance is the `𝒞_{∞,1}` membership
(`cyclo_mem_cycloTower1`); this declaration is the trivial `≤ 𝒰_{∞,1}` projection of it. Recording SMALL
for the *content this declaration adds*. (Literature width was run EXHAUSTIVE regardless; BIG/SMALL is
framing only.)

### One-line check (Phase 2b)

Body line count: 1 substantive line (`cycloTower1_le_unitsTower1 p (cyclo_mem_cycloTower1 p ha hp2 ha1)`)
One-liner verdict: **n/a — kind is `theorem`, not `def`** (the defeq/diamond/API exemption table is for
`def`/`abbrev`/`structure`; a theorem introduces no definitional equality or typeclass-search path).
Noted only: the *proof term* is a single function application of one project lemma to another, which is a
strong signal that the statement is a thin composition (carried into Phase 6/7).

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

The theorem separates into two "concepts": (i) the **number-theoretic content** — the cyclotomic
norm-compatible system (the Coleman-map input) lying in the principal local units of the cyclotomic
tower (classical Coleman/Iwasawa theory; RJW arXiv:2309.15692 is the immediate source); and (ii) the
**structural mechanism** actually being proved — membership transported along a subgroup inclusion
(`x ∈ H`, `H ≤ K` ⟹ `x ∈ K`), here built on the meet projection `𝒞_{n,1} = 𝒞_n ∩ 𝒰_{n,1} ≤ 𝒰_{n,1}`
threaded through a pointwise inverse limit. Both were searched.

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific NT form)     | "cyclotomic units contained in principal local units inverse limit norm-compatible Iwasawa theory C_∞ ⊆ U_∞" | yes  | `C_∞ ⊆ U_∞`; cyclotomic/circular units sit inside the (principal) local units, studied via the projective limit under norm maps | Sharifi *Iwasawa theory: a climb up the tower*; Hida *Elementary Iwasawa Theory*; Shariﬁ AWS notes; arXiv:math/0512015; arXiv:0912.2528 — textbook Iwasawa theory (Washington Ch. 7–8, Lang *Cyclotomic Fields*) |
|  2 | WebSearch (NT, Coleman-input)    | "Iwasawa theory cyclotomic units norm compatible system input Coleman map global units principal units tower membership" | yes  | the Coleman map is defined on the inverse limit of local-unit towers; the cyclotomic units form the norm-compatible family that is its input (→ Kubota–Leopoldt p-adic L-function) | Chris Williams *p-adic L-functions II*; Sharifi notes; "Coleman power series for K₂"; arXiv:1411.3655 (Coleman obituary). Confirms `cyclo ∈ 𝒰_{∞,1}` is exactly the ambient Coleman-input setup, never isolated as a named lemma |
|  3 | WebSearch (general / structural) | "subgroup membership specialization a element subgroup H, H ≤ K implies element of K monotone inclusion lattice" | yes  | the lattice of subgroups is ordered by inclusion (`≤`); `x ∈ H` and `H ≤ K` ⟹ `x ∈ K`; meet `H ⊓ K` is the intersection, below both factors | Wikipedia "Lattice of subgroups"; PlanetMath "lattice of subgroups"; mathlib `Subgroup.Lattice` docs; LibreTexts §3.2. The structural fact is the defining order property — "too elementary to have a name" outside `≤`/`SetLike` |
|  4 | ChatGPT MCP                      | (intended: "standard form + generality + historical evolution of 'cyclotomic units ⊆ principal local units' and of 'membership transported along H ≤ K'") | n/a  | —                                | ChatGPT MCP server not configured in this environment (ToolSearch surfaces no such tool — only the Asana/Atlassian auth stubs). Recorded n/a; compensated by extra WebSearch breadth (rows 1–3), nLab (row 6), and direct mathlib source reading (Phase 5) |
|  5 | Local references                 | `projects/PadicLFunctions/.mathlib-quality/references/`, `refs/PadicLFunctions/`, any local `*.pdf`      | n/a  | (no references dir)              | Neither `.mathlib-quality/references/` nor a gitignored `refs/` store exists; no local `*.pdf` found anywhere in the repo. The RJW arXiv:2309.15692 PDF is not available locally. The `--refs` path passed by the task points at the *skill's own* reference docs, not the project's source papers. Recorded n/a |
|  6 | nLab                             | "Iwasawa theory" (cyclotomic units / principal local units / norm-compatible inverse limits)            | partial | nLab "Iwasawa theory" treats class-group inverse limits over the Iwasawa algebra; does NOT engage the unit-group constructions `U_∞`/`C_∞` directly | Fetched ncatlab.org/nlab/show/Iwasawa+theory: confirms the *area* but not this specific unit-tower inclusion; nothing categorical-novel is asserted by the theorem |
|  7 | nCatLab (if categorical)         | (covered by nLab row 6)                                                                                 | n/a  | not a higher-categorical concept | The theorem is a 1-categorical/order-theoretic membership; no ∞-categorical content |
|  8 | Stacks Project (if alg geom)     | —                                                                                                      | n/a  | not an algebraic-geometry concept | This is `p`-adic / Iwasawa number theory + subgroup-lattice order theory; Stacks has no bearing |
|  9 | MathOverflow / Math.StackExchange| "x ∈ H, H ≤ K subgroup membership" / "cyclotomic units principal units inverse limit"                  | yes  | confirms `x ∈ H ∧ H ≤ K ⟹ x ∈ K` is the elementary inclusion-order property; confirms the NT inclusion is ambient background, never a quotable named lemma | The structural fact is "too trivial to name"; the NT inclusion is standing background in every Iwasawa/Coleman text |
| 10 | recent arXiv (last 5 years)      | RJW arXiv:2309.15692 (the project's own source) + arXiv:2208.06777, arXiv:math/0512015                  | yes  | RJW §11.3 (TeX 3060–3112): defines `𝒞_{∞,1}` as the inverse limit of `𝒞_{n,1} = 𝒞_n ∩ 𝒰_{n,1}`; TeX 3084 states the milestone `c_n(a)` "are naturally elements of `𝒟_n`, hence global" and uses `𝒞_{∞,1} ≤ 𝒰_{∞,1}` without a separate name | The source packages the `≤ 𝒰_{∞,1}` step as definitional bookkeeping atop the milestone, exactly as the Lean theorem does |

The protocol passes: WebSearch ran 3 distinct queries at different generality levels (specific NT
inclusion, the Coleman-input NT framing, and the most-general structural `x ∈ H ∧ H ≤ K ⟹ x ∈ K` form);
ChatGPT MCP recorded n/a with reason (not installed); local references recorded n/a with reason
(absent); nLab checked (fetched); nCatLab / Stacks / MathOverflow / arXiv each checked or n/a-with-reason.

### Literature summary (Phase 3)

Concept identified as: a project-specific packaging of two standard ingredients — (NT) "the cyclotomic
norm-compatible system (the Coleman-map input) lies in the principal local units of the cyclotomic tower"
(classical Coleman/Iwasawa theory; RJW arXiv:2309.15692 §11.3 + TeX 3084 is the immediate source), and
(structure) "membership transported along a subgroup inclusion `x ∈ H`, `H ≤ K` ⟹ `x ∈ K`", here with
`H = 𝒞_{∞,1}`, `K = 𝒰_{∞,1}`, and `H ≤ K` itself coming from the level-wise meet projection
`𝒞_{n,1} = 𝒞_n ∩ 𝒰_{n,1} ≤ 𝒰_{n,1}`.

Sources agree on the standard form: yes. The NT inclusion is ambient background in Washington / Lang /
Hida / Sharifi / Williams / RJW (the cyclotomic units ARE the canonical Coleman-map input, and their
landing in the principal local units is the precondition that makes the Coleman map applicable). The
structural fact `x ∈ H ∧ H ≤ K ⟹ x ∈ K` is the defining inclusion-order property of the subgroup lattice
(Wikipedia, PlanetMath, LibreTexts), and in mathlib is exactly `mem_of_le_of_mem` (alias of
`SetLike.le_def`).

Most general standard form: the *structural* skeleton is `mem_of_le_of_mem : a ∈ s → s ≤ t → a ∈ t` over
any `SetLike`. Everything else here (`cyclo`, `NormCompatUnits`, `cycloTower1`, `unitsTower1`,
`cycloClosureOne`, `localUnitsOne`, `cycloClosure`) is bespoke RJW-tower scaffolding with no
literature-standard or mathlib counterpart.

Generality dimensions where the literature varies:
  - The NT objects (`cyclo`, `𝒞`/`𝒰` towers) — RJW realises them concretely inside `ℂ_p`; other
    treatments (Coleman, Rubin, de Shalit) use abstract local fields / Lubin–Tate formal groups. Either
    way they are not mathlib objects.
  - The structural fact — already maximally general in mathlib as `mem_of_le_of_mem` over `SetLike` (and,
    for the `H ≤ K` input one level down, `inf_le_right` over `SemilatticeInf`).

Disagreement with the literature: none. The Lean statement matches the (corollary-of-the-milestone)
inclusion the source states, and the proof matches the elementary membership-transport the literature
gives for it.

---

### Generality analysis — `cyclo_mem_unitsTower1` (Phase 4)

Literature-standard form (from Phase 3): structurally `mem_of_le_of_mem : a ∈ s → s ≤ t → a ∈ t` over any
`SetLike` (with the `s ≤ t` input here being `inf_le_right` lifted through the inverse limit, =
`cycloTower1_le_unitsTower1`); semantically the RJW corollary `c(a) ∈ 𝒞_{∞,1} ≤ 𝒰_{∞,1}`.

| # | Parameter / hypothesis                | Current Lean form                              | Literature-standard form                       | Weaker form exists? | Reason it can/can't be weakened |
|---|---------------------------------------|------------------------------------------------|------------------------------------------------|---------------------|----------------------------------|
| 1 | `cyclo p ha hp2` (the element)        | bespoke `NormCompatUnits p` system `(c_n(a))_n` | no mathlib/literature-standard analogue (project object) | NO | `cyclo` is glued out of `cycloUnit`, `NormCompatUnits`, `levelNorm` — all project-only; the statement is intrinsically about this object |
| 2 | `unitsTower1 p` (target subgroup)     | bespoke inverse-limit subgroup of `NormCompatUnits p` | no analogue (project object)             | NO | `unitsTower1` / `localUnitsOne` / `NormCompatUnits` are RJW-specific |
| 3 | `ha1 : a ≡ 1 [MOD p]` (hypothesis)    | principal-unit congruence                      | inherited from the milestone `cyclo_mem_cycloTower1` | NO (at this level) | Unused at the top level; passed straight to `cyclo_mem_cycloTower1`, which genuinely needs it (`‖c_n(a) − 1‖ < 1`; T1113 note). Dropping it would break the dependency, not generalise this theorem |
| 4 | the underlying transport step         | `cycloTower1_le_unitsTower1 p (· )` applied to the milestone | `mem_of_le_of_mem` over `SetLike` (with `≤` = `inf_le_right` lifted) | (already maximal) | The abstract kernel is already mathlib's maximal membership-transport (`mem_of_le_of_mem`); the `≤` input is `inf_le_right`. No further generalisation of the *fact* is meaningful |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (for the objects it is about). There are zero weakening
opportunities: the theorem is a statement *about* two specific project objects (`cyclo`, `unitsTower1`),
and the only abstract content (membership transport `x ∈ H`, `H ≤ K` ⟹ `x ∈ K`) is already at mathlib's
maximal generality (`mem_of_le_of_mem` over `SetLike`). Nothing can be weakened without either (a) being
a statement about different (non-existent-in-mathlib) objects, or (b) collapsing to `mem_of_le_of_mem`,
which already exists. The hypothesis `ha1` is not removable here (the milestone it feeds needs it).

Number of weakening opportunities found: 0
Proposed restatement: none (MAXIMALLY GENERAL).
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                  | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|---------------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                      | no       | —                      | Hypotheses are already the `p`/`Fact p.Prime` section vars plus the arithmetic conditions on `a`; nothing to typeclass-ify |
|  2 | sequences/metric → filters/topological?                                                                  | no       | —                      | The towers are indexed over `ℕ` with an `n ≥ 1` predicate (the inverse-system index), not a metric limit. Already the right idiom |
|  3 | construct an object → universal-property class?                                                          | no       | —                      | This is a membership theorem, not a construction |
|  4 | set-with-closure-predicate → bundled substructure?                                                       | no       | —                      | Both `unitsTower1` and `cycloTower1` are already bundled `Subgroup`s; the proof already uses `Subgroup`/`SetLike` machinery. Idiomatic |
|  5 | vector-space/metric/field-specific → weaker typeclass?                                                   | no       | —                      | No algebraic-structure hypothesis to weaken; the abstract core already lives over `SetLike`/`SemilatticeInf` |
|  6 | 1-categorical → higher-categorical?                                                                      | no       | —                      | Order-theoretic membership; no categorification target |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive/ordered structure?                                          | no       | —                      | The `ℕ`-index is the inverse-system's directed index; abstracting it would mean re-engineering `NormCompatUnits`, the project's chosen model, not a mathlib idiom gap |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**.
One-line reason: the theorem is already stated idiomatically (bundled `Subgroup`s, `SetLike` membership,
section typeclasses); its only generalisable kernel is already mathlib's `mem_of_le_of_mem`. There is no
Bourbaki-2.0 reformulation to make — the objects themselves are project-bespoke and out of mathlib scope.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (no definitional equality or typeclass-search path is introduced).

---

### Mathlib search-status: `cyclo_mem_unitsTower1` (Phase 5)

Note on environment: the Lean MCP search tools (`lean_loogle`, `lean_leansearch`, `lean_local_search`,
Lean-Finder) are not installed here; Loogle was attempted via its public JSON endpoint (WebFetch — it
timed out / errored on the Unicode membership-transport query), and method D (grep mathlib source) was
run directly and is decisive. Each method is recorded with what was actually executed.

[A] Lean-Finder       "cyclotomic units in principal local units tower", "membership transported along subgroup inclusion"  —  n/a: MCP/web app not reachable from this harness; subsumed by grep (D) + the Phase-3 literature sweep, which jointly resolve the question.
[B] Loogle            `(_ : _ ∈ _), (_ : _ ≤ _) → _ ∈ _`  →  endpoint returned a heartbeat-timeout/error page (the wildcard membership-transport pattern is too broad for the public endpoint). Resolved instead by direct grep (D): the primitive is `mem_of_le_of_mem`. Loogle on the *concrete* statement (`cyclo _ ∈ unitsTower1 _`) is impossible — the constants are project-local, not in any Loogle-indexed library.
[C] LeanSearch        "cyclotomic system is a principal-unit tower" / "element of subgroup contained in larger subgroup"  —  n/a: NL endpoint not reachable from this harness; the concept ("`x ∈ H`, `H ≤ K` ⟹ `x ∈ K`") is unambiguous and pinned by grep (D) to `mem_of_le_of_mem`, so NL search adds nothing.
[D] Grep mathlib src  `NormCompatUnits`, `cyclo `, `cycloTower1`, `unitsTower1`, `cycloClosureOne`, `localUnitsOne` over `.lake/packages/mathlib/Mathlib/`  →  **0 files each** (all six are project-only). Also grepped `Data/SetLike/Basic.lean`: the relevant general lemma is `mem_of_le_of_mem` (alias of `SetLike.le_def`, line 258: `S ≤ T ↔ ∀ ⦃x⦄, x ∈ S → x ∈ T`; line 251 `coe_subset_coe`). For the `H ≤ K` input one level down, `inf_le_right` (`Mathlib/Order/Lattice.lean:87`). There is **no** generic "cyclotomic-system-is-a-principal-unit-tower" lemma to specialise from.
[E] Name pattern      grep project + mathlib for `*_mem_unitsTower*`, `*_mem_cycloTower*`, `cyclo_mem_*`, `mem_of_le`  →  finds only the *project's own* sibling family (`cyclo_mem_cycloTower1`, `galNCU_mem_unitsTower1`, `wGamma_mem_unitsTower1`, `wGamma_mem_cycloTower1`, …) plus mathlib's generic `mem_of_le_of_mem`. No mathlib name matches the concrete statement.

Searched for both:
  - the user's current form (`cyclo p ha hp2 ∈ unitsTower1 p`) — built entirely from project-only
    constants; **not in mathlib** (cannot be, by construction).
  - the literature-standard / abstract form (`x ∈ H`, `H ≤ K` ⟹ `x ∈ K`) — **in mathlib** as
    `mem_of_le_of_mem` (`Mathlib/Data/SetLike/Basic.lean:258`), the building block the proof is a thin
    application of (the `H ≤ K` input being the project's `cycloTower1_le_unitsTower1`, itself
    `inf_le_right` lifted level-wise).

Concluded: **found building blocks (`mem_of_le_of_mem` + the project inclusion `cycloTower1_le_unitsTower1`,
itself `inf_le_right`); composition would yield our form.** The exact concrete statement is *not* in
mathlib (it is about objects that exist only in this project), but its entire proof content is a
≤1-call application of one project lemma (`cyclo_mem_cycloTower1`) along one project inclusion
(`cycloTower1_le_unitsTower1`) — no mathlib lemma is created or needed.

---

### Call sites — `cyclo_mem_unitsTower1` (Phase 6.0)

Internal use count: **0** (within the project, NOT counting the declaring line 495).
External-to-file callers: 0.
External-to-project callers: 0 (no downstream library consumes it).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| (none)           | `cyclo_mem_unitsTower1` is not referenced anywhere outside its own declaration |

Inline-derivation grep (was the equivalent re-derived elsewhere without using this theorem?):
  - The *stronger* fact `cyclo ∈ 𝒞_{∞,1}` (the milestone `cyclo_mem_cycloTower1`) is itself referenced 0
    times externally; and downstream consumers that need "X ∈ 𝒰_{∞,1}" route through the more general
    `cycloTower1_le_unitsTower1` directly (e.g. `IwasawaProof/Main.lean:442/522/537–538` apply
    `cycloTower1_le_unitsTower1 p h` to whatever cyclo-tower membership they have on hand — they do NOT
    go through `cyclo_mem_unitsTower1`). So `cyclo_mem_unitsTower1` is a **terminal, currently-unused
    statement of the milestone** (`K = 0`, no inline re-derivation routing through it).

Per the Phase-6 signal table: `K = 0` with no consumer routing through it normally reads as "dead code OR
genuinely-new + unused (BORDERLINE)". Here it is neither junk nor a new mathlib candidate — it is the
named, RJW-paper-faithful *statement of the milestone's conclusion* (TeX 3084), kept as the headline even
though downstream code happens to use the more general inclusion lemma instead. The decisive factor for
the *mathlib* question is independent of usage count: the *objects* are out of mathlib scope (Phase 5: 0
mathlib hits for all of `cyclo` / `unitsTower1` / `cycloTower1` / `NormCompatUnits`), which caps the
verdict at a NO bucket.

### Composition check (Phase 6)

Can `cyclo_mem_unitsTower1` be derived in ≤3 chained calls? (Here "composable" means: given the project's
own definitions and the already-existing project results, is the *proof* a trivial composition, so that
no standalone result earns its keep against mathlib's "no thin wrappers" rule — there is nothing mathlib-
shaped to add?)

Attempt 1: the existing one-line proof term itself —
`cycloTower1_le_unitsTower1 p (cyclo_mem_cycloTower1 p ha hp2 ha1)`
  - Decls used: the project lemma `cycloTower1_le_unitsTower1` (CyclotomicUnits.lean:239, itself
    `fun _ hu n hn => (Subgroup.mem_inf.1 (hu n hn)).2`, i.e. `inf_le_right` lifted) applied to the
    project milestone `cyclo_mem_cycloTower1` (CyclotomicUnits.lean:472). Abstractly this is mathlib's
    `mem_of_le_of_mem` (`Mathlib/Data/SetLike/Basic.lean:258`): `mem_of_le_of_mem (cyclo_mem_cycloTower1 …)
    (cycloTower1_le_unitsTower1 p)`.
  - Result: **succeeds** — this is the verbatim current proof; 1 application of a project inclusion to a
    project lemma (= 1 mathlib `mem_of_le_of_mem` call over project inputs).
  - Notes: the genuine mathematics is entirely upstream of this line (`cyclo_mem_cycloTower1` →
    `norm_cycloUnit_sub_one_lt_one` → the principal-unit estimate). This declaration adds only the
    transport `𝒞_{∞,1} ↪ 𝒰_{∞,1}`.

Conclusion: **COMPOSABLE** — a 1-call composition (mathlib's `mem_of_le_of_mem` over the project's own
`cyclo_mem_cycloTower1` and `cycloTower1_le_unitsTower1`). No new mathlib-worthy result is created by this;
its only abstract content is `mem_of_le_of_mem` / `inf_le_right`, both already in mathlib.

---

## Verdict: `cyclo_mem_unitsTower1`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the NT content — the cyclotomic norm-compatible system (the Coleman-map
  input) lying in the principal local units of the cyclotomic tower — is ambient, classical Coleman/Iwasawa
  theory (Sharifi/Hida/Williams/Washington/Lang; RJW §11.3 + TeX 3084 treats it as the natural milestone,
  with the `≤ 𝒰_{∞,1}` step unnamed). The structural kernel is the elementary membership transport
  `x ∈ H`, `H ≤ K` ⟹ `x ∈ K` (Wikipedia/PlanetMath/LibreTexts) = mathlib `mem_of_le_of_mem`. Nothing novel.
- Generality analysis (Phase 4): MAXIMALLY GENERAL (0 weakenings; `ha1` is not removable — it feeds the
  milestone); modern-idiom: none — already idiomatic; the only abstract kernel is already maximally general
  in mathlib.
- Mathlib search (Phase 5): the concrete statement is not in mathlib (all of `cyclo`, `unitsTower1`,
  `cycloTower1`, `cycloClosureOne`, `localUnitsOne`, `NormCompatUnits` have 0 mathlib hits — project-only);
  the building blocks `mem_of_le_of_mem` (`Mathlib/Data/SetLike/Basic.lean:258`) and `inf_le_right` ARE in
  mathlib.
- Composition check (Phase 6): COMPOSABLE — the proof is
  `cycloTower1_le_unitsTower1 p (cyclo_mem_cycloTower1 p ha hp2 ha1)`, i.e. mathlib's `mem_of_le_of_mem`
  applied to two existing project results. `K = 0` call sites (terminal milestone statement).

**Rationale:**

This is the trivial corollary half of the project's milestone, not mathematics mathlib is missing. The
hard content — that the cyclotomic units `c_n(a)` are genuinely principal (`‖c_n(a) − 1‖ < 1`) and hence
form a norm-compatible system landing in the *cyclotomic* tower `𝒞_{∞,1}` — is proved upstream in
`norm_cycloUnit_sub_one_lt_one` and assembled in `cyclo_mem_cycloTower1` (CyclotomicUnits.lean:472). Since
`𝒞_{∞,1} ≤ 𝒰_{∞,1}` holds by definition (`cycloTower1_le_unitsTower1`, the `inf_le_right` projection of
`𝒞_{n,1} = 𝒞_n ∩ 𝒰_{n,1}`), `cyclo_mem_unitsTower1` is exactly that milestone membership pushed forward
along the inclusion — a single application of mathlib's `mem_of_le_of_mem` to two results that already
exist in the project. It carries none of the milestone's substance itself; it is the weaker, terminal
statement of the conclusion (RJW TeX 3084), kept as the headline even though downstream code
(`IwasawaProof/Main.lean`) routes through the more general `cycloTower1_le_unitsTower1` directly (hence
`K = 0` consumers of *this* declaration).

It also cannot go to mathlib because it is a statement *about objects mathlib does not have and will not
have*: `cyclo`, `NormCompatUnits`, `unitsTower1`, `cycloTower1`, `cycloClosureOne`, `localUnitsOne` are all
bespoke RJW-tower scaffolding (Phase 5: zero mathlib hits for each). There is nothing here to upstream —
the only reusable nugget, "membership transported along `H ≤ K`", is already `mem_of_le_of_mem`. The
theorem is correct and faithful to the source, and worth keeping *in the project* as the named statement
of the milestone, but for the *mathlib* question it is exactly the "1-mathlib-call composition over
project-local objects, inline-able" shape that the NO-composable bucket exists for. (It is the direct
analogue of its sibling `cycloTower1_le_unitsTower1`, already assessed `NO-composable-from-mathlib`.)

**WHY not (refactor-actionable detail):**

Mathlib already has the building block; the user's form is a 1-call composition of it over project-local
results, so no mathlib lemma is warranted. The composition is:
- Mathlib building blocks:
  - `mem_of_le_of_mem` — `.lake/packages/mathlib/Mathlib/Data/SetLike/Basic.lean:258`
    (alias of `SetLike.le_def`: from `a ∈ s` and `s ≤ t`, conclude `a ∈ t`)
  - (the `s ≤ t` input is the project lemma `cycloTower1_le_unitsTower1`, itself `inf_le_right`,
    `.lake/packages/mathlib/Mathlib/Order/Lattice.lean:87`)
- Project results it composes (NOT mathlib, but already proven in-project):
  - `cyclo_mem_cycloTower1` — `Iwasawa/CyclotomicUnits.lean:472` (the milestone; the real content)
  - `cycloTower1_le_unitsTower1` — `Iwasawa/CyclotomicUnits.lean:239` (the inclusion)

Composition sketch (≤3 lines) — this IS the current proof, shown to make inlining mechanical:
```lean
-- the current proof term:
example {a : ℕ} (ha : ¬ (p : ℕ) ∣ a) (hp2 : p ≠ 2) (ha1 : a ≡ 1 [MOD p]) :
    cyclo p ha hp2 ∈ unitsTower1 p :=
  cycloTower1_le_unitsTower1 p (cyclo_mem_cycloTower1 p ha hp2 ha1)
  -- equivalently, with the mathlib primitive named explicitly:
  -- mem_of_le_of_mem (cyclo_mem_cycloTower1 p ha hp2 ha1) (cycloTower1_le_unitsTower1 p)
```

Call sites in our project (from Phase 6.0): **K = 0** (no consumer routes through this declaration;
downstream code uses the more general `cycloTower1_le_unitsTower1` directly).

Refactor plan (for the *mathlib* question — honest recommendation): **do not** propose this for mathlib in
any form. There is nothing to add (`mem_of_le_of_mem` already exists) and nothing to generalise (the towers
are project-bespoke). For the *project*, this is a judgment call with two legitimate options, and since
`K = 0` it leans slightly toward inlining:
  - Option A (keep it): retain `cyclo_mem_unitsTower1` as the named, RJW-faithful statement of the
    milestone's conclusion (TeX 3084). It documents the headline even though no current code consumes it.
    No call sites to touch. This is a *project-documentation* decision, not a mathlib contribution.
  - Option B (inline / drop): since `K = 0`, the project's own cleanup pass could delete it and let
    consumers that ever need "`cyclo ∈ 𝒰_{∞,1}`" write
    `cycloTower1_le_unitsTower1 p (cyclo_mem_cycloTower1 p ha hp2 ha1)` directly (one line). No call-site
    edits are required today (there are none); only the declaration would be removed.

Next action for the **mathlib question specifically**: no mathlib PR. Keep the theorem project-local
(Option A) or drop it during a project cleanup (Option B); either is fine and is a project decision, not a
mathlib one.

---

## Next step

Do not open a mathlib PR. The reusable content is already `mem_of_le_of_mem`
(`Mathlib/Data/SetLike/Basic.lean:258`, with the `≤` input `inf_le_right`,
`Mathlib/Order/Lattice.lean:87`); the statement itself is about project-only objects
(`cyclo` / `unitsTower1` / `cycloTower1` / `cycloClosureOne` / `localUnitsOne` / `NormCompatUnits` — zero
mathlib hits) and is a 1-call composition of two existing project results
(`cyclo_mem_cycloTower1` along `cycloTower1_le_unitsTower1`). Since it has `K = 0` call sites, the project
may keep it as the named milestone statement (Option A) or drop it and inline the one-line composition if
ever needed (Option B). This is a project-cleanup/documentation decision, not a mathlib one.
