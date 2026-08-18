# `/mathlibable` report — `PadicLFunctions.Coleman.cycloClosure`

**Final verdict: `NO-composable-from-mathlib`** (the concept — the p-adic closure
`𝒞_n` of the cyclotomic units inside the local units — is a standard, named object
of cyclotomic Iwasawa theory, but the *definition* is a two-operation composition
of mathlib primitives, `Subgroup.topologicalClosure` followed by the lattice meet
`⊓`, applied to project-local subgroups; no new mathlib lemma is justified).

---

## Baseline (Phase 0)

- lake build:               **not re-run** (build stale/slow per task instructions); **reasoned from source** — Phase 0 fallback. The declaration and its whole file (`Iwasawa/CyclotomicUnits.lean`) are `sorry`-free; the dependency chain (`cycloUnits`, `localUnits`, `Subgroup.topologicalClosure`, `⊓`, `ℂ_[p] = PadicComplex`) all resolves, and downstream consumers (`Generators.lean`, `Main.lean`, `ColContinuity.lean`) compile against it on `main`.
- decl `PadicLFunctions.Coleman.cycloClosure`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/Iwasawa/CyclotomicUnits.lean:210`
- kind:                      `def` (a plain `noncomputable def` returning `Subgroup ℂ_[p]ˣ`, body = a single `⊓` expression)
- has sorry:                 no (whole file: 0 `sorry`/`admit`)
- module docstring summary:  Cyclotomic units: the global modules `𝒟_n` and their local closures `𝒞` (RJW arXiv:2309.15692 §11.3, TeX 3060–3112 + §9 notation), all realized **inside `ℂ_[p]`** (decomposition replan R11.7).

---

## Statement (Phase 1)

`PadicLFunctions.Coleman.cycloClosure p n` is **a definition** of the following:

Let `p` be a prime and `n : ℕ`. Inside the topological group `ℂ_[p]ˣ` of units of
the `p`-adic complex numbers (mathlib's `PadicComplex p`), let `𝒟_n = cycloUnits p n`
be the group of cyclotomic units of the cyclotomic field `F_n = ℚ(μ_{p^n})`
(realized as a `Subgroup ℂ_[p]ˣ`), and let `𝒰_n = localUnits p n` be the group of
local units (units of the local ring of integers `O_n`). Then `cycloClosure p n`
is **the p-adic closure `𝒞_n` of the cyclotomic units inside the local units** —
the topological closure of `𝒟_n` in `ℂ_[p]ˣ`, intersected with `𝒰_n`:
`𝒞_n = clos(𝒟_n) ∩ 𝒰_n`. This is RJW's Definition at TeX 3090. Because `𝒟_n ≤ 𝒰_n`
and `𝒰_n` is closed (`isClosed_localUnits`), the intersection with `𝒰_n` is
mathematically redundant — `clos(𝒟_n) ⊆ 𝒰_n` already — so `𝒞_n = clos(𝒟_n)`; the
`⊓ 𝒰_n` is kept by the file as an "honest subspace closure" presentation device.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the prime (fixed at file scope).
- `n : ℕ` — the cyclotomic level (the field is `ℚ(μ_{p^n})`, the local field `K_n = ℚ_p(μ_{p^n})`).
- ambient: `ℂ_[p]ˣ` = units of `PadicComplex p` — a topological group (so `Subgroup.topologicalClosure` applies).

Hypotheses (Lean side): none beyond the typeclasses; this is a plain `def`.

Body (math): `cycloClosure p n := (cycloUnits p n).topologicalClosure ⊓ localUnits p n`
— literally the meet of two subgroups, one of which is the topological closure of
`cycloUnits`.

Conclusion (math): `𝒞_n = clos(𝒟_n) ∩ 𝒰_n` (`= clos(𝒟_n)`), the p-adic closure of the cyclotomic units in the local units.

Conclusion (Lean): `Subgroup ℂ_[p]ˣ` — n/a (definition, not a proposition).

---

## Size classification (Phase 2a)

Verdict: **BIG** (borderline; "named construction" rather than "named structure").
Reason: `𝒞_n` (the p-adic closure of cyclotomic units in the local units) is a
*named object* of cyclotomic Iwasawa theory — it appears under exactly this name in
the source paper (RJW arXiv:2309.15692, Definition TeX 3090), in Coates–Sujatha's
*Cyclotomic Fields and Zeta Values*, in Hida's lecture notes, and in the
"semi-local units modulo cyclotomic units" literature (Iwasawa, the JTNB
`Z_2`-extension papers). It is a primary structural input to a `## Main results`-level
development (the milestone `cyclo_mem_cycloTower1`, RJW TeX 3084, and the Iwasawa
Main Conjecture machinery). So it is essentially guaranteed to be near the
literature — which is exactly why the literature width is EXHAUSTIVE. (But note:
unlike `cycloUnits` or `globalUnits`, `cycloClosure` does not introduce a *new kind
of structure*; it is the result of applying two generic `Subgroup` operations —
that is the crux of Phase 6.)

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL only frames the report.)

---

## One-line check (Phase 2b)

Body line count: **1 substantive line** —
`(cycloUnits p n).topologicalClosure ⊓ localUnits p n`.
One-liner verdict: **ONE-LINER** (a `def` whose body is a single `⊓` expression
combining two subgroups).

Exemption check (each row required):

| Exemption                         | Applies? | Evidence |
|-----------------------------------|----------|----------|
| Avoid defeq abuse                | **no**   | The def is *not* used as a defeq barrier — quite the opposite. Every consumer immediately `rw [cycloClosure, Subgroup.mem_inf]` to unfold it to `topologicalClosure ⊓ localUnits` and split the meet (CyclotomicUnits.lean:488; Generators.lean:1710; the closedness proof `isClosed_cycloClosureOne` at ColContinuity.lean:832–841 does `rw [cycloClosureOne, cycloClosure]; rfl`). It is unfolded on first contact, so it is sealing nothing. |
| Avoid typeclass diamonds         | **no**   | It returns a `Subgroup`, participates in no typeclass search; there are no competing `Mul`/`Zero`/`Inf` instances at stake. The `⊓` is mathlib's unique `Min (Subgroup G)` instance. |
| Mark semantic intent / API name  | **partially** | It *does* carry a name + a substantial docstring ("RJW Definition TeX 3090") and four suffixed siblings (`cycloClosurePlus`, `cycloClosureOne`, `cycloClosureOnePlus`) build on it. That gives it value *as project notation*. But the name is consumed by *unfolding*, not by a stable opaque API — so the "API stability" rationale is weak: re-implementing the body behind the same name would break every consumer (they all pattern-match on the `⊓` shape). |

Conclusion: **ONE-LINER WITH-(weak)-EXEMPTION** — the only live exemption is
"semantic intent / project notation", and even that is undercut by the
unfold-on-contact usage pattern. Carried into Phase 7: a one-liner whose sole
justification is a project-local label, where consumers unfold rather than reuse
opaquely, is a strong steer toward `NO-composable-from-mathlib` (the composition is
the def). This is consistent with the call-sites finding (Phase 6.0).

---

## Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "p-adic closure of cyclotomic units in local units Iwasawa theory definition" | yes | `C_n =` p-adic closure of cyclotomic units inside the principal/local units `U_n`; a **closed `Z_p[Gal]`-submodule** of `U_n` | Coates–Sujatha *Cyclotomic Fields and Zeta Values* (McGill PDF); Hida, *Elementary Iwasawa Theory for Cyclotomic Fields*; Shariﬁ, *Iwasawa theory: a climb up the tower*; arXiv:1907.06437 (image of `p`-adic log on principal units). The "plus part of the principal units modulo cyclotomic units" is the standard ambient. |
| 2 | WebSearch (general form) | "\"topological closure\" subgroup topological group definition closure of subgroup" | yes | "If `H` is a subgroup of a topological group `G`, then `cl(H)` is also a subgroup" — the **general** primitive | ProofWiki *Closure of Subgroup is Group*; Münster *Basic Properties of Topological Groups* ch.1; Vinroot/Godsil *Topological Groups MATH 519*; Landesman exercises. This is exactly mathlib's `Subgroup.topologicalClosure` — the generic operation, valid for any subgroup of any topological group. |
| 3 | WebSearch (named-after / aliases) | "cyclotomic units closure C_n local units U_n Coleman map p-adic L-function Iwasawa main conjecture" | yes | "A group of cyclotomic units is identified with a **closed** `Z_2[Gal(k_n/Q)]`-submodule of `U_{k_n}`"; Coleman determined `U/C` as a Λ-module | Top hit is the **source paper arXiv:2309.15692** (RJW). Also JTNB/Numdam "Semi-local units modulo cyclotomic units in the cyclotomic `Z_2`-extension"; arXiv:2312.09301; arXiv:2007.07454 (universal norms). Confirms `𝒞_n` ⊆ `𝒰_n` closed-submodule setup and the `U/C` Iwasawa quotient. |
| 4 | WebSearch (C_p-embedded form) | (folded into #3; the `ℂ_p`-ambient convention) | yes | (the SOURCE paper) | arXiv:2309.15692 is RJW *An introduction to p-adic L-functions* — the project reference; the `𝒞_n`/`𝒰_n` notation and the "everything inside `ℂ_p`" convention are this paper's. |
| 5 | ChatGPT MCP | "standard definition of the p-adic closure of cyclotomic units in the local units, its generality, historical evolution" | **n/a** | — | **ChatGPT MCP server not configured** in this environment (it is not in the deferred-tools list; only Asana/Atlassian/Box/… MCP servers are present). Recorded n/a per protocol; compensated with deeper WebSearch (#1–4) + WebFetch (#6) + direct mathlib grep (Phase 5). Consistent with sibling reports (`globalUnits.md`, `cycloGenSet.md`) in this batch. |
| 6 | nLab | "topological group" / closure of a subgroup | partial | nLab *topological group* covers closed subgroups ("every open subgroup is closed") but does not state the closure-of-a-subgroup-is-a-subgroup lemma on that page | WebFetch of https://ncatlab.org/nlab/show/topological+group — the abstract closure operation is standard textbook material (see #2); "p-adic closure of cyclotomic units" does not appear (it is a number-theory construction, not a categorical one). |
| 7 | nCatLab (categorical) | (same as nLab) | n/a | — | Not a categorical concept. `𝒞_n` is the meet of a topological-closure subgroup with another subgroup; no universal-property / higher-categorical form beyond "closure is the right adjoint to the inclusion of closed subgroups", which mathlib already encodes via `topologicalClosure_minimal`. |
| 8 | Stacks Project | "closure of subgroup / cyclotomic units" | n/a | — | Not an algebraic-geometry concept. The topological-closure-of-a-subgroup primitive is generic topology mathlib already has; cyclotomic-unit closures are cyclotomic Iwasawa theory, outside Stacks' scope. |
| 9 | MathOverflow / Math.SE | "closure of subgroup of topological group is subgroup" | yes (indirect) | Wikipedia *Closed-subgroup theorem*; the closure-is-a-subgroup fact is folklore/textbook (ProofWiki #2 is the canonical statement) | The direct MO/SE hits were thin (the search surfaced Wikipedia *Centrally/Conjugacy-closed subgroup* + *Closed-subgroup theorem*), but #2's ProofWiki entry is the canonical community statement; no specialised "closure of cyclotomic units" question turned up — it is paper-specific. |
| 10 | recent arXiv (last 5 yr) | the source + neighbours | yes | RJW arXiv:2309.15692 §11.3 (`𝒞_n`); arXiv:1907.06437 (2019, image of `p`-adic log on principal units); arXiv:2312.09301, arXiv:2007.07454 (Iwasawa/universal norms) | The closed-submodule-of-`U_n`-generated-by-cyclotomic-units construction is alive in current Iwasawa-theory literature; the definitional content is uniformly "take the closure of the cyclotomic units inside the local units". |

### Literature summary (Phase 3)

Concept identified as: **`𝒞_n`, the p-adic (topological) closure of the cyclotomic
units `𝒟_n` inside the local units `𝒰_n`** — a standard, named object of cyclotomic
Iwasawa theory (Coates–Sujatha, Hida, Sharifi, Iwasawa; the source paper RJW
arXiv:2309.15692 Def. TeX 3090). In the literature it is uniformly a *closed
`Z_p[Gal]`-submodule of `U_n`*, and the Iwasawa quotient `U/C` (or `U_∞/C_∞`) is the
object Coleman's theory and the Main Conjecture are about.

Sources agree on the standard form: **yes.** The construction is always "the closure
of the (sub)group of cyclotomic units, taken inside the local units". Two
*independent* standard facts underlie it:
1. (number theory) the cyclotomic units `𝒟_n` are a specific subgroup of `𝒰_n`;
2. (general topology) the topological closure of a subgroup of a topological group
   is again a subgroup — the generic operation, valid in any topological group.

`𝒞_n` is the application of (2) to the input from (1) (with an honest `∩ 𝒰_n` that is
redundant because `𝒰_n` is closed and `𝒟_n ≤ 𝒰_n`).

Most general standard form (of the *operation*): `H.topologicalClosure` for `H` a
subgroup of an arbitrary topological group `G` — mathlib's exact `Subgroup.topologicalClosure`.

Generality dimensions where the literature varies:
- the *group acted on*: `U_n` (local units of `ℚ_p(μ_{p^n})`) here ⊂ any topological
  group (the general closure operation). The number-theoretic content lives entirely
  in the **input** `𝒟_n`, not in "take a closure".
- presentation: `clos(𝒟_n)` (since `𝒰_n` closed and `𝒟_n ≤ 𝒰_n`) vs. the file's
  `clos(𝒟_n) ⊓ 𝒰_n` (the `⊓ 𝒰_n` makes the "inside `𝒰_n`" explicit but is
  mathematically a no-op here).

Disagreement with the literature: **none.** The file's `𝒞_n` is exactly the
standard object. The only divergence from "the cleanest statement" is the redundant
`⊓ localUnits` factor, which is a deliberate presentation choice (RJW writes
"closure *in* `𝒰_n`").

---

## Generality analysis — `cycloClosure` (Phase 4)

Literature-standard form (from Phase 3): the topological closure of a designated
subgroup (the cyclotomic units) inside the topological group of local units —
operationally, `Subgroup.topologicalClosure` applied to `𝒟_n`.

### 4a. Generality status table

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | the ambient group | `ℂ_[p]ˣ` (units of `PadicComplex p`) | any topological group `G` (for the *operation*) | yes, but n/a | The *closure operation* is fully general in mathlib (`Subgroup.topologicalClosure` over any `[TopologicalSpace G] [Group G] [ContinuousMul]`); there is nothing to generalise — the project legitimately *instantiates* the general operation at `G = ℂ_[p]ˣ`. |
| 2 | the input subgroup | `cycloUnits p n` (a project def) | the cyclotomic units `𝒟_n` | no | The number-theoretic content is `𝒟_n` itself (assessed separately — `cycloUnits`/`cycloGenSet`). `cycloClosure` adds nothing to it but a closure + a meet. |
| 3 | the `⊓ localUnits` factor | `⊓ localUnits p n` | `clos(𝒟_n)` (the meet is redundant) | yes | Since `cycloUnits ≤ globalUnits ≤ localUnits` (`cycloUnits_le_globalUnits` ∘ `globalUnits_le_localUnits`) and `localUnits` is **closed** (`isClosed_localUnits`), `clos(𝒟_n) ⊆ localUnits`, so `clos(𝒟_n) ⊓ localUnits = clos(𝒟_n)`. The factor is a presentation device, not extra generality. |

### 4b. Generality verdict

The current form is: **MAXIMALLY GENERAL — at the level of the operation** (the
closure operation it uses, `Subgroup.topologicalClosure`, is already the maximally
general mathlib primitive; the def simply instantiates it at `ℂ_[p]ˣ` with input
`𝒟_n`). There is **no weakening of `cycloClosure` itself to propose** — any
generality lives in the *operation* (already general in mathlib) or in the *input*
`𝒟_n` (a separate decl). Number of weakening opportunities found on `cycloClosure`
qua definition: **0** (the only "simplification" is dropping the redundant
`⊓ localUnits`, which is a project-cleanup nicety, not a generalisation, and not a
mathlib contribution either way).

Proposed restatement: none as a *generalisation*. (Optional project cleanup, not a
mathlib matter: `cycloClosure p n := (cycloUnits p n).topologicalClosure`, dropping
the redundant `⊓ localUnits`, with a lemma `cycloClosure p n = … ⊓ localUnits p n`
if the `⊓` shape is wanted for the consumers that pattern-match on it.)

Cost of restatement: n/a (no generalisation to perform).

This verdict (no generalisation; the operation is already general in mathlib) steers
Phase 7 away from `YES-but-generalise-first` and toward a NO bucket — the right
question is *composition*, not generality.

### 4c. Modern-idiom check (Bourbaki 2.0)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|---|----------|----------|------------------------|---------------------------------|
| 1 | "let X be a foo" preambles → typeclasses/instances? | no | — | It is already a typeclass-driven construction: `Subgroup.topologicalClosure` requires `[TopologicalGroup]`-style instances on `ℂ_[p]ˣ`, all already present. Nothing to bundle. |
| 2 | sequences/metric → filters/topological? | **already done** | — | The def is *already* the filter/topological form: `topologicalClosure` is defined via `_root_.closure` (the topological closure operator), not via sequential limits. This is the modern idiom; the file even proves the density argument (`zpPow_…_topologicalClosure`) using `closure` + `DenseRange`, not sequences. |
| 3 | construct an object → universal-property class? | no | — | `topologicalClosure` already *has* its universal property in mathlib (`Subgroup.topologicalClosure_minimal`: it is the least closed subgroup containing `s`). The def uses the universal construction directly. |
| 4 | set-with-closure-predicate → bundled-substructure type? | **already done** | — | `cycloClosure` returns a bundled `Subgroup`, and `topologicalClosure`/`⊓` are the bundled-lattice operations. This is exactly the idiom; no upgrade available. |
| 5 | field/metric-specific → weaken typeclasses? | no | — | The operation is already typeclass-general; the `ℂ_[p]ˣ` instantiation is intrinsic to the p-adic application. |
| 6 | 1-categorical → higher-categorical? | no | — | Not a categorification target. |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group? | no | — | The `n` indexes the cyclotomic level (the field `ℚ_p(μ_{p^n})`), intrinsic to the Iwasawa tower; not a spurious concrete index. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** — because the declaration is *already written in the
modern mathlib idiom*. It uses `Subgroup.topologicalClosure` (the bundled,
filter/`closure`-based, universal-property-bearing closure operation) and the
bundled lattice meet `⊓`. There is no contemporary reformulation that would be a
real organisational improvement; the def is the composition of two already-idiomatic
primitives. (One-line reason this is not a modernisation move: the only change one
could make — dropping the redundant `⊓ localUnits` — is a *simplification of a
project def*, not a new mathlib idiom, and does not turn `cycloClosure` into a
mathlib contribution.) This confirms Phase 7 should **not** pick
`YES-but-generalise-first` with reason MODERN-IDIOM.

---

## Diamond / defeq risk — `cycloClosure` (Phase 4.5)

(`def`, so the phase runs. It is a *plain* `def`, not an `instance`/`class`/coercion.)

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | none | Returns a `Subgroup ℂ_[p]ˣ`; participates in no typeclass-search path. The `⊓` resolves to mathlib's unique `Min (Subgroup G)` instance. |
| 2 | Reducibility leak | none | No `@[reducible]`. The body is a `⊓` of two subgroups; even if it were semireducible, every consumer explicitly `rw [cycloClosure]` to unfold, so no surprising defeq leak occurs. |
| 3 | Non-canonical unfolding | low | `rw [cycloClosure]` unfolds to `topologicalClosure ⊓ localUnits`, after which `Subgroup.mem_inf` splits membership into the two expected components — this is the intended and uniformly-used API (CyclotomicUnits.lean:488, 679, 693; Generators.lean:1710, 1765). Unsurprising. |
| 4 | Instance priority collision | none | Not an `instance`. |
| 5 | Universe-polymorphism issues | none | All types concrete (`ℂ_[p]ˣ`, `ℕ`); no universe variables. |
| 6 | Coercion ambiguity | none | No `CoeFun`/`CoeSort`; only the standard `Subgroup → Set` from `SetLike`. |

### Risk verdict (Phase 4.5)

Overall risk: **NONE.** Top risks: none. (Recorded for completeness; the verdict is a
NO bucket, so the def is not being added to mathlib anyway.)

---

## Mathlib search-status: `cycloClosure` (Phase 5)

[A] Lean-Finder       — conceptual phrasing "topological closure of a subgroup intersected with a subgroup" folds to `Subgroup.topologicalClosure` + `⊓`; no distinct hit beyond those primitives.
[B] Loogle            `Subgroup ?G → Subgroup ?G` over closure → returns `Subgroup.topologicalClosure`, `Subgroup.normalClosure`, `Subgroup.closure` family; `Subgroup _ → Subgroup _ → Subgroup _` → returns the lattice ops (`⊓`/`Min`, `⊔`, `Subgroup.prod`). Both building blocks present; **no** "closure of cyclotomic units"/"closure ⊓ local units" packaged decl.
[C] LeanSearch        "topological closure of a subgroup of a topological group" → the well-known `Subgroup.topologicalClosure`; "closure of cyclotomic units in local units" → no mathlib object (it is paper-specific Iwasawa theory).
[D] Grep mathlib src  over `.lake/packages/mathlib/Mathlib/`:
  - `Subgroup.topologicalClosure` — **found**, `Mathlib/Topology/Algebra/Group/Basic.lean:674`, with full API: `topologicalClosure_coe` (681), `le_topologicalClosure` (685), `isClosed_topologicalClosure` (689), `topologicalClosure_minimal` (693), `topologicalClosure_mono` (698).
  - `Min (Subgroup G)` / `⊓` — **found**, `Mathlib/Algebra/Group/Subgroup/Lattice.lean:223`, with `coe_inf` (229) and `Subgroup.mem_inf`.
  - cyclotomic-units machinery — `Mathlib/RingTheory/RootsOfUnity/CyclotomicUnits.lean` has only *associatedness / geometric-sum* facts (`associated_sub_one_pow_sub_one_of_coprime`, `geom_sum_isUnit`, …), **no** group of cyclotomic units and **no** closure thereof; `Mathlib/NumberTheory/NumberField/Cyclotomic/*` has the ring-of-integers/ideal theory, not a unit-closure object.
  - `cycloClosure` (the name) — **0 hits** in mathlib.
[E] Name pattern      grep `cycloClosure`, `closureOfCyclotomic`, `cyclotomicUnitsClosure`, `localUnits.*closure` over mathlib → **0 hits**.

Searched for both:
- the user's current form (`topologicalClosure ⊓ localUnits` on project subgroups) — **not in mathlib** (correctly; it is a project-specific instantiation/composition).
- the literature-standard *operation* (topological closure of a subgroup of a topological group) — **in mathlib** as `Subgroup.topologicalClosure`, fully general, with the meet `⊓` for the intersection. The number-theoretic *input* (`𝒟_n`) is project-specific and assessed separately.

Concluded: **"found the building blocks (`Subgroup.topologicalClosure` at
`Mathlib/Topology/Algebra/Group/Basic.lean:674`; the lattice meet `⊓` /
`Min (Subgroup G)` at `Mathlib/Algebra/Group/Subgroup/Lattice.lean:223`, with
`Subgroup.mem_inf` for membership); composition of these two with the project's own
`cycloUnits`/`localUnits` yields `cycloClosure` exactly."** The packaged object
`cycloClosure` is *not* in mathlib, and shouldn't be — it is a two-operation
composition over project-local inputs.

---

## Call sites — `cycloClosure` (Phase 6.0)

Internal use count (within the project, **excluding** the declaring file): **1 real
code use.**
External-to-file callers: **1 file** (`IwasawaProof/Generators.lean`).

| Caller file:line | Usage pattern (one-line excerpt) | Code or comment? |
|------------------|----------------------------------|------------------|
| Iwasawa/CyclotomicUnits.lean:215 | `cycloClosurePlus … := cycloClosure p n ⊓ localUnitsPlus p n` | code (intra-file; suffixed-sibling def builds on it) |
| Iwasawa/CyclotomicUnits.lean:219 | `cycloClosureOne … := cycloClosure p n ⊓ localUnitsOne p n` | code (intra-file; suffixed-sibling def) |
| Iwasawa/CyclotomicUnits.lean:488 | `· rw [cycloClosure, Subgroup.mem_inf]` (inside `cyclo_mem_cycloTower1`) | code (intra-file; **unfolds** the def) |
| Iwasawa/CyclotomicUnits.lean:611,679,693 | `rw [cycloClosureOne, Subgroup.mem_inf, cycloClosure, Subgroup.mem_inf]` | code (intra-file; **unfolds**) |
| IwasawaProof/Generators.lean:1710 | `rw [cycloClosure, Subgroup.mem_inf]` (inside `wGamma_pow_mem_cycloTower1`) | **code (external; unfolds the def on first contact)** |
| IwasawaProof/Generators.lean:1765 | `rw [cycloClosureOne, Subgroup.mem_inf, cycloClosure, Subgroup.mem_inf]` | code (external; **unfolds**) |
| Coleman/ColContinuity.lean:832–841 | `rw [cycloClosureOne, cycloClosure]; rfl` (inside `isClosed_cycloClosureOne`) | code (external; **unfolds** to prove closedness from `isClosed_topologicalClosure.inter isClosed_localUnits`) |
| IwasawaProof/Main.lean:178 | `… 𝒞_{n,1} = clos(𝒟_{n,1}) ⊓ 𝒰_{n,1} (`cycloClosureOne`)` | **comment** |

Inline-derivation grep (was `clos(𝒟_n) ⊓ 𝒰_n` re-derived elsewhere without
`cycloClosure`?): **none** — every site that needs `𝒞_n` goes through `cycloClosure`
(or its suffixed siblings), but **uniformly by unfolding it**, never as an opaque
black box.

What the call-sites pattern tells us: **K = 1 external code use** (Generators.lean:1710,
plus the closedness consumer ColContinuity.lean and the suffixed-sibling defs), and
**every single consumer immediately `rw [cycloClosure]` to unfold it** to
`topologicalClosure ⊓ localUnits` and split with `Subgroup.mem_inf`. No consumer
treats `cycloClosure` as an opaque API; they all destructure the `⊓` composition.
This is the textbook signal of a *thin composition wrapper*: the def names a
2-operation expression that consumers re-expand on contact. Per the Phase-6 signal
table, K = 1 (plus pattern-matching/unfolding usage) leans toward
**NO-composable-from-mathlib** — the def carries no opaque content that a consumer
relies on; it is the composition itself.

### Composition check (Phase 6)

Can `cycloClosure p n` be *defined* by composing mathlib primitives in ≤3 calls?

Attempt 1: `(cycloUnits p n).topologicalClosure ⊓ localUnits p n`.
  - Mathlib decls used: `Subgroup.topologicalClosure` (call 1), `· ⊓ ·` = `Min (Subgroup G)` (call 2).
  - Project inputs used: `cycloUnits p n`, `localUnits p n` (assessed separately — they are the project's number-theoretic content, not mathlib's).
  - Result: **succeeds** — this is *literally the body of the def* (CyclotomicUnits.lean:211). Two mathlib operations, applied to two project subgroups. ≤3 calls.
  - Notes: per the Phase-6 heuristics table, `Foo.topologicalClosure ⊓ Bar` is a one-operation-then-meet composition (analogous to `Foo.bar.trans Bar.baz` / `Foo.bar (Bar.baz hx)`) — a genuine composition, **not** a proof in disguise (no `rw … ring_nf … aesop`, no chain of `have`s with reasoning between).

Attempt 2 (the even-simpler form, given the redundant meet): `(cycloUnits p n).topologicalClosure`.
  - Mathlib decls used: `Subgroup.topologicalClosure` (call 1).
  - Result: **succeeds and is *equal*** to Attempt 1, because `clos(𝒟_n) ⊆ localUnits` (`cycloUnits ≤ globalUnits ≤ localUnits` and `isClosed_localUnits`). So `𝒞_n` is *one* mathlib call on a project subgroup; the `⊓ localUnits` is presentation only.
  - Notes: this strengthens the verdict — the essential content of `cycloClosure` is a *single* mathlib operation (`topologicalClosure`) applied to a project def.

Conclusion: **COMPOSABLE** — `cycloClosure` is the meet of `Subgroup.topologicalClosure`
(of the project's `cycloUnits`) with the project's `localUnits`: 2 mathlib calls (1
if one drops the redundant meet), over project-local inputs. No new mathlib lemma is
justified. (This rules out the YES buckets and `NO-mathlib-has-it` — mathlib does not
have the *packaged* `cycloClosure`, only the *building blocks*. The correct bucket is
`NO-composable-from-mathlib`.)

---

## Verdict: `cycloClosure` (Phase 7)

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): `𝒞_n` (p-adic closure of cyclotomic units in the local
  units) is a standard, named object of cyclotomic Iwasawa theory (Coates–Sujatha,
  Hida, Sharifi, Iwasawa; source paper RJW arXiv:2309.15692 Def. TeX 3090). But its
  *content* splits into (i) the number-theoretic input `𝒟_n` and (ii) the **generic**
  topological-closure-of-a-subgroup operation — the latter being mathlib's
  `Subgroup.topologicalClosure`.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL at the operation level** — the
  closure operation used is already the maximally general mathlib primitive; there is
  no `cycloClosure`-level generalisation to make (Phase 4c confirms it is *already*
  the modern bundled/filter idiom, so no MODERN-IDIOM upgrade either).
- Mathlib search (Phase 5): found the **building blocks** —
  `Subgroup.topologicalClosure` (`Mathlib/Topology/Algebra/Group/Basic.lean:674`) and
  the lattice meet `⊓` / `Min (Subgroup G)` (`Mathlib/Algebra/Group/Subgroup/Lattice.lean:223`,
  with `Subgroup.mem_inf`). The packaged `cycloClosure` is not in mathlib (and the
  closure-of-cyclotomic-units object is paper-specific, absent from
  `RootsOfUnity/CyclotomicUnits.lean`).
- Composition check (Phase 6): **COMPOSABLE** — the def *is* the composition
  `(cycloUnits p n).topologicalClosure ⊓ localUnits p n` (2 mathlib calls; 1 if the
  redundant `⊓ localUnits` is dropped). Call sites: K = 1 external code use, and
  **every consumer unfolds the def on first contact** (`rw [cycloClosure, Subgroup.mem_inf]`),
  the canonical thin-wrapper signature.

**Rationale.**
`cycloClosure p n` is the p-adic closure `𝒞_n` of the cyclotomic units inside the
local units — a genuinely standard object of cyclotomic Iwasawa theory (RJW TeX 3090,
Coates–Sujatha, Hida). The *mathematics* it names is real and important. But the
*declaration* contributes nothing mathlib is missing: it is the composition of two
generic mathlib `Subgroup` operations — `Subgroup.topologicalClosure` (mathlib's
fully-general "closure of a subgroup of a topological group", with the complete
`topologicalClosure_coe`/`le_…`/`isClosed_…`/`minimal`/`mono` API) and the lattice
meet `⊓` (`Min (Subgroup G)`, with `Subgroup.mem_inf`) — applied to the project's own
`cycloUnits` and `localUnits`. The number-theoretic substance lives entirely in those
two *inputs* (`cycloUnits`/`cycloGenSet`/`globalUnits`, assessed in their own reports),
not in the act of taking a closure-and-meet. mathlib already owns both operations;
gluing them is a one- or two-call inline, not a new lemma.

Two independent facts seal `NO-composable` over the YES buckets and over
`NO-mathlib-has-it`. First, Phase 6 shows the body is a textbook ≤3-call composition
(`Foo.topologicalClosure ⊓ Bar`), and indeed reduces to a *single* mathlib call once
one observes the `⊓ localUnits` is mathematically redundant (`clos(𝒟_n) ⊆ localUnits`
because `cycloUnits ≤ globalUnits ≤ localUnits` and `localUnits` is closed via
`isClosed_localUnits`). Second, the call-sites pattern (Phase 6.0) is the diagnostic
fingerprint of a thin wrapper: there is exactly one external code consumer, and every
consumer — internal and external alike — immediately `rw [cycloClosure, Subgroup.mem_inf]`
to re-expand the def into its two components rather than using it opaquely. A name
whose only role is to be unfolded back into its definition adds packaging, not API.
`NO-mathlib-has-it` is wrong because mathlib has no *packaged* `cycloClosure` (only
the primitives); `YES-*` is wrong because there is no missing mathlib content and no
generalisation to make (Phase 4/4c). Cost plays no role here (it is cheap either way),
so this is a clean self-resolving verdict, not a BORDERLINE cost question.

**WHY not (refactor-actionable).** Mathlib has the building blocks; `cycloClosure` is
a 1–2 mathlib-call composition over the project's own subgroups, so no separate def
earns a mathlib PR.

Mathlib building blocks:
- `Subgroup.topologicalClosure` — `Mathlib/Topology/Algebra/Group/Basic.lean:674`
  (topological closure of a subgroup of a topological group; API at lines 681–699).
- `· ⊓ ·` = `Min (Subgroup G)` — `Mathlib/Algebra/Group/Subgroup/Lattice.lean:223`
  (membership via `Subgroup.mem_inf`; underlying-set via `coe_inf`, line 229).

Composition sketch (≤3 lines — it is the def body):
```lean
-- exactly the current body:
example : cycloClosure p n = (cycloUnits p n).topologicalClosure ⊓ localUnits p n := rfl
-- and, because clos(𝒟_n) ⊆ localUnits (cycloUnits ≤ globalUnits ≤ localUnits, isClosed_localUnits):
example : cycloClosure p n = (cycloUnits p n).topologicalClosure := by
  rw [cycloClosure, inf_eq_left.mpr]
  exact (cycloUnits p n).topologicalClosure_minimal (by
    -- clos(𝒟_n) ≤ localUnits, since 𝒟_n ≤ localUnits and localUnits is closed
    exact le_trans (Subgroup.topologicalClosure_mono
      (le_trans (cycloUnits_le_globalUnits p n) (globalUnits_le_localUnits p n)))
      (by simpa using (isClosed_localUnits p n)))  -- sketch; the minimal/closed glue
```

Call sites in the project (from Phase 6.0): **K = 1 external code use**
(`IwasawaProof/Generators.lean:1710`), plus the closedness consumer
(`Coleman/ColContinuity.lean:832`), the two suffixed-sibling defs
(`cycloClosurePlus`/`cycloClosureOne`, same file lines 215/219), and the intra-file
`cyclo_mem_cycloTower1` (line 488) — **all of which already unfold the def**.

Refactor plan — note this is **project-local cleanup, not a mathlib PR** (the def is
fine to *keep* as project notation; the point is only that it must not be upstreamed
as a standalone mathlib def, and could optionally be simplified):
- **Recommended (keep as project notation):** leave `cycloClosure` in the project as
  RJW's `𝒞_n` label. It earns its place *as readable Iwasawa-theory notation* for the
  suffixed family (`cycloClosurePlus`/`Plus`/`One`/`OnePlus`) and the docstrings. Do
  **not** open a mathlib PR for it.
- **Optional simplification (project-internal):** since `⊓ localUnits` is redundant
  (`clos(𝒟_n) ⊆ localUnits`), one *could* define
  `cycloClosure p n := (cycloUnits p n).topologicalClosure` and, if the consumers'
  `rw [cycloClosure, Subgroup.mem_inf]` pattern is to be preserved, add a lemma
  `cycloClosure_eq_inf : cycloClosure p n = (cycloUnits p n).topologicalClosure ⊓ localUnits p n`.
  This is a tidy-up, not required, and out of mathlib scope.
- **If a site ever wants to avoid the wrapper entirely:** at
  `Generators.lean:1710` (and the analogous spots) one can inline
  `(cycloUnits p n).topologicalClosure ⊓ localUnits p n` directly in place of
  `cycloClosure p n` — the `rw [cycloClosure, Subgroup.mem_inf]` already does this in
  spirit. No argument-type adjustment needed (same `Subgroup ℂ_[p]ˣ`).

Next action: do **not** open a mathlib PR for `cycloClosure` — it is a ≤2-call
composition (`Subgroup.topologicalClosure ⊓ localUnits`) of mathlib primitives over
project-local subgroups. Keep it as project-local notation for `𝒞_n` (optionally
simplifying away the redundant `⊓ localUnits`). Reserve any mathlib-upstreaming effort
from this file for the genuinely p-adic results
(`norm_le_one_of_isIntegral_int`, the `zpPow`/density machinery), not this
closure-and-meet definition.

---

## Next step

Do **not** open a mathlib PR for `cycloClosure`. Mathlib already has both building
blocks — `Subgroup.topologicalClosure` (`Mathlib/Topology/Algebra/Group/Basic.lean:674`)
and the lattice meet `⊓` (`Min (Subgroup G)`, `Mathlib/Algebra/Group/Subgroup/Lattice.lean:223`,
membership via `Subgroup.mem_inf`) — and `cycloClosure p n` is precisely their 1–2
call composition over the project's own `cycloUnits`/`localUnits`
(`(cycloUnits p n).topologicalClosure ⊓ localUnits p n`, where the `⊓ localUnits` is
mathematically redundant since `clos(𝒟_n) ⊆ localUnits`). Keep it as project-local
notation for RJW's `𝒞_n` (it reads well and anchors the `cycloClosurePlus/One/OnePlus`
family), optionally simplifying away the redundant meet; the number-theoretic content
to assess for mathlib lives in the *inputs* (`cycloUnits`/`cycloGenSet`), not in this
closure-and-meet wrapper.
