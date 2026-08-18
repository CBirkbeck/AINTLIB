# Mathlibable assessment: `PadicLFunctions.Coleman.cycloTower1Plus`

**Final verdict: `NO-composable-from-mathlib`** — a thin levelwise-membership/inverse-limit
wrapper (`⨅_n comap eval_n (cycloClosureOnePlus n)`) over a *project* structure
(`NormCompatUnits p`) and *project-specific* per-level subgroups; mathlib supplies the generic
scaffolding (`Subgroup.comap`, `Subgroup.iInf`, `Subgroup.pi`) but none of the content.

- **Kind:** `def` (returns data — a `Subgroup (NormCompatUnits p)`), so `lowerCamelCase` is correct.
- **Source:** `projects/PadicLFunctions/PadicLFunctions/Iwasawa/CyclotomicUnits.lean:233`
- **Mode:** A (single declaration), full 10-phase workflow with the exhaustive 9-channel literature search.

```lean
/-- `𝒞⁺_{∞,1} = lim←_{n≥1} 𝒞⁺_{n,1}` (RJW TeX 3092). -/
noncomputable def cycloTower1Plus : Subgroup (NormCompatUnits p) where
  carrier := {u | ∀ n, 1 ≤ n → u.elems n ∈ cycloClosureOnePlus p n}
  mul_mem' hu hv n hn := mul_mem (hu n hn) (hv n hn)
  one_mem' _ _ := one_mem _
  inv_mem' hu n hn := (cycloClosureOnePlus p n).inv_mem (hu n hn)
```

---

## Phase 0 — Doctor / baseline

```
### Baseline (Phase 0)
- lake build:               build NOT re-run; reasoned from source (per task build note — build stale/slow here)
- decl `cycloTower1Plus`:    ✓ resolved at projects/PadicLFunctions/PadicLFunctions/Iwasawa/CyclotomicUnits.lean:233
- kind:                      def (noncomputable; bundled `Subgroup (NormCompatUnits p)` via `where`)
- has sorry:                 no
- module docstring summary:  RJW (arXiv:2309.15692) §11.3 — the global cyclotomic-unit modules 𝒟_n and their local closures 𝒞, all inside ℂ_[p]; the milestone is that the Coleman-map inputs land in 𝒞_{∞,1}.
```

The full dependency chain was read directly from source:

- `cycloTower1Plus` carrier `= {u | ∀ n, 1 ≤ n → u.elems n ∈ cycloClosureOnePlus p n}` (`CyclotomicUnits.lean:233`).
- `cycloClosureOnePlus p n := cycloClosurePlus p n ⊓ localUnitsOne p n` (`CyclotomicUnits.lean:222`).
- `cycloClosurePlus p n := cycloClosure p n ⊓ localUnitsPlus p n` (`CyclotomicUnits.lean:214`).
- `cycloClosure p n := (cycloUnits p n).topologicalClosure ⊓ localUnits p n` (`CyclotomicUnits.lean:210`).
- `cycloUnits p n := Subgroup.closure (cycloGenSet p n) ⊓ globalUnits p n` (`CyclotomicUnits.lean:182`).
- Ambient: `NormCompatUnits p` — a **`structure`** (`Coleman/Tower.lean:650`) carrying `elems : ℕ → ℂ_[p]ˣ`, `mem`, `inv_mem`, and norm-compatibility `compat`; upgraded to `CommGroup` at `LocalUnits.lean:467`. It is the project's realization of the inverse limit `𝒰_∞ = lim←_n 𝒪_n^×`.

All operands are project-defined objects of the RJW §11.3 Iwasawa cyclotomic-unit tower, living inside `ℂ_[p]`.

## Phase 1 — Comprehend

```
### Statement (Phase 1)
```

`cycloTower1Plus p` is a **definition** of the object RJW writes `𝒞⁺_{∞,1}`:

It is the **inverse (projective) limit** `lim←_{n≥1} 𝒞⁺_{n,1}` of the plus-part principal local
closures of the cyclotomic units, realized as a subgroup of the already-constructed inverse-limit
group `𝒰_∞ = NormCompatUnits p`. Concretely: the norm-compatible systems `u = (u_n)_n` of local
units whose level-`n` component `u_n = u.elems n` lies in `𝒞⁺_{n,1} = cycloClosureOnePlus p n` for
every `n ≥ 1`. Mathematically, `𝒞⁺_{n,1}` is the plus part (totally-real part) of the principal-unit
part of the p-adic closure of the cyclotomic units at level `n`; `𝒞⁺_{∞,1}` is its norm-coherent
tower, the plus part of the Coleman-map source in RJW's main Iwasawa diagram.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the prime (section variables; supply the p-adic setting `ℂ_[p]`, `ℚ_[p]`).
- ambient group `NormCompatUnits p` — project structure (inverse limit of local unit groups; `CommGroup`).

Hypotheses (Lean side): none on the def itself; the carrier predicate quantifies `∀ n, 1 ≤ n → …`
(the `n ≥ 1` convention matches `NormCompatUnits.compat`, where the level norm `N_{n+1,n}` carries
the degree-`p` step).

Conclusion (math): the subgroup `𝒞⁺_{∞,1} ⊆ 𝒰_∞` carved out by levelwise membership in `𝒞⁺_{n,1}`.

Conclusion (Lean): `Subgroup (NormCompatUnits p)` — n/a, this is a definition (data).

It is **data** (a bundled `Subgroup`), defined as a **levelwise-membership predicate over an
inverse-limit structure** — the inverse-limit / `Subgroup.pi`-with-`comap` analogue of the finite
`⊓`-meets used for the per-level objects `cycloClosureOne`/`cycloClosurePlus`.

## Phase 2 — Preliminary checks (size + one-line)

```
### Size classification (Phase 2a)
Verdict: SMALL
Reason: it introduces no new mathematical *structure* (the structure is `NormCompatUnits`, already
built); it is a bundled subgroup cut out of an existing group by a levelwise-membership predicate
over project-specific components. It is the plus-tower node, not a primary `## Main results` object
(the milestone `cyclo_mem_cycloTower1`/the §12 Main Conjecture are the named results; this is the
plus-part *carrier* they are stated against).
```

(Note: literature width was EXHAUSTIVE regardless — 9 channels run below.)

```
### One-line check (Phase 2b)
Body line count: 4 substantive lines (carrier + 3 closure-field proofs), but the *content* line is
the single carrier predicate `{u | ∀ n, 1 ≤ n → u.elems n ∈ cycloClosureOnePlus p n}`; the three
group-axiom fields are forced boilerplate (`mul_mem`/`one_mem`/`inv_mem` lifted levelwise).
One-liner verdict: effectively ONE-LINER (one substantive carrier line; the three proofs are
mechanical levelwise lifts of the component subgroup's closure properties — identical in shape to
the twin `unitsTower1Plus` and the sibling `cycloTower1`).

Exemption check (each row required):
| Exemption                        | Applies? | Evidence |
|----------------------------------|----------|----------|
| Avoid defeq abuse               | no       | consumers `rw [cycloClosureOnePlus, …]` / unfold to factors; the def is not a sealed defeq barrier any proof relies on. |
| Avoid typeclass diamonds        | no       | introduces no instance; reuses `NormCompatUnits`'s `CommGroup` and `Subgroup`'s lattice. No `Mul`/`Zero`/`AddCommMonoid` collision. |
| Mark semantic intent / API name | partial  | the name `𝒞⁺_{∞,1}` *is* RJW notation and the object is the subgroup of the **plus-part SES quotient** `unitsTower1Plus / cycloTower1Plus.subgroupOf unitsTower1Plus` (Main.lean:691, 892) — but stability of the *name* is not what makes it mathlib-worthy; the content is project operands. |

Conclusion: ONE-LINER WITHOUT (defeq/diamond) EXEMPTION — biases away from a YES verdict toward
NO-composable / NO-mathlib-has-it (carried into Phase 7). It is a *new project definition that is a
trivial inverse-limit combination of project objects*, not a missing mathlib primitive.
```

## Phase 3 — Literature search (EXHAUSTIVE, 9 channels)

```
### Literature search table — EXHAUSTIVE protocol
```

| # | Channel | Query | Hit? | Standard form found | Notes |
|---|---|---|---|---|---|
| 1 | WebSearch (specific form) | "cyclotomic units norm-compatible system inverse limit principal units plus part Iwasawa C_{∞,1}⁺ projective limit definition" | yes | the **plus part of the projective limit of (semi-)local units / cyclotomic units** in the cyclotomic ℤ_p-tower is standard (Sharifi notes; arXiv:0910.1411 "units generated by Euler systems"; Wikipedia "Cyclotomic unit") | the *ingredients* (cyclotomic units, norm-compatible towers, inverse limits) are canonical; the **`C_{∞,1}⁺` symbol is paper-specific** (RJW) |
| 2 | WebSearch (general / named form) | "'plus part' cyclotomic units totally real subfield projective limit local units Iwasawa module Coleman map maximal real" | yes | JTNB 2024 (jtnb.1284) "**Semi-local units modulo cyclotomic units**" studies `U`= proj. limit semi-local units, `C`= proj. limit cyclotomic units, and `U/C`; Hida's UCLA Iwasawa lectures; **RJW arXiv:2309.15692** itself | confirms the **standard object is the inverse limit `lim←_n C_n` (and its plus part) modulo which `U/C` is studied** — the Coleman-map / Main-Conjecture source; the per-level/plus bookkeeping is internal |
| 3 | WebSearch (aliases / "inverse limit of subgroups") | "Subgroup of inverse limit group cut out by membership in subgroup at each level projective limit of subgroups Lean construction" | yes | the inverse limit of groups **is** the subgroup of the product `{x : ∀ i, F i // compatible}` cut out by compatibility; a subobject defined **levelwise** by membership at each level | the *construction pattern* (levelwise membership inside the product/inverse limit) is the generic categorical one — see Phase 5/6 for the mathlib realization |
| 4 | ChatGPT MCP (standard form + historical evolution) | "What is the standard definition and generality of the plus part of the projective limit of cyclotomic (principal) units in the cyclotomic Z_p-tower? Has the formulation evolved?" | n/a | **n/a: ChatGPT MCP server not configured in this environment.** Substituted by the three WebSearches (≥3, different generality levels) + nLab + the direct mathlib reading below. | recorded `n/a` with reason, not blank |
| 5 | Local references (`refs/PadicLFunctions/`, `.mathlib-quality/references/`) | grep for "cyclotomic", "tower", "plus", "C_{∞,1}" | n/a | **n/a: no `refs/` symlink and no `.mathlib-quality/references/` dir present** (PDFs are local-only and not linked here). Primary source identified from the docstring: RJW arXiv:2309.15692, §11.3, TeX 3092. | dir absent — recorded n/a |
| 6 | nLab | "inverse limit / projective limit", "profinite group" | yes (generic) | nLab: the inverse limit is the **closed subspace of the product** of compatible elements; profinite groups are inverse limits of finite groups — the levelwise/compatibility construction is standard | no nLab page treats *this specific* plus-cyclotomic-unit tower as a named object |
| 7 | nCatLab (if categorical) | inverse limit subobject / limit in Grp | yes (generic) | a limit in `Grp` is computed as a subgroup of the product; the "levelwise membership" pattern is the standard limit construction | not a bespoke categorical object — the categorical content is the generic limit-in-Grp |
| 8 | Stacks Project (if alg geom) | — | n/a | **n/a: not an algebraic-geometry concept.** (Iwasawa-theoretic inverse limit of unit groups; Stacks has valuations/units but no cyclotomic-unit tower.) | recorded n/a with reason |
| 9 | MathOverflow / Math.StackExchange | "semi-local units modulo cyclotomic units", "projective limit of cyclotomic units plus part" | yes | matches channel 2 — the studied object is `U/C` for `U`, `C` the proj. limits; the plus part is `U⁺/C⁺` | confirms the inverse limit (and its plus part) is the standard object, not the per-level intersection bookkeeping |
| 10 | recent arXiv (last 5 years) | "cyclotomic units projective limit plus part Iwasawa 2020.." | yes | jtnb.1284 (2024); arXiv:2410.17458 (2024, cyclotomic ℤ_2 Iwasawa module); RJW arXiv:2309.15692 (2023) | the *operand-level* objects (`C_n`, `C_n⁺`, their inverse limits) are actively used; `𝒞⁺_{∞,1}` notation is RJW-local |

```
### Literature summary (Phase 3)

Concept identified as: the plus part of the (norm-coherent) inverse limit of the principal-unit
p-adic closures of the cyclotomic units in the cyclotomic ℤ_p-tower — RJW's 𝒞⁺_{∞,1}. In the
broader literature this is the plus part `C⁺` of the projective limit of cyclotomic units (the
"semi-local units modulo cyclotomic units" object `U/C`, restricted to the totally-real/plus side).

Sources agree on the standard form: yes (for the *ingredients* and the *inverse-limit construction*).
The inverse limit of groups is universally the subgroup of the product cut out by compatibility +
levelwise membership; the cyclotomic-unit tower and its plus part are standard Iwasawa-theory objects
(Hida, Sharifi, the JTNB semi-local-units line, RJW). The specific symbol `𝒞⁺_{∞,1}` is paper-local.

Most general standard form: the inverse limit `lim←_n A_n` of an inverse system of groups, realized
as `{x ∈ ∏_n G_n | x compatible, x_n ∈ A_n ∀ n}`. Here `G_n = 𝒪_n^×`/its principal units, `A_n =
𝒞⁺_{n,1}`, and the compatibility is the level-norm coherence already baked into `NormCompatUnits`.

Generality dimensions where the literature varies:
  - base field / conductor: RJW fixes ℚ(μ_{p^n}); the literature treats general totally-real /
    abelian base fields. (Operand-level — lives on `cycloClosureOnePlus`/`globalUnits`, not here.)
  - ambient: RJW embeds everything in ℂ_[p]; the abstract object is over the number-field/local
    unit groups. (Operand-level.)
  - "plus": concrete real generator (RJW) vs the abstract complex-conjugation-fixed part. (Operand-level.)

Disagreement with the literature: none on the construction. The literature's *named, reusable*
object is the inverse limit of the unit/cyclotomic-unit tower (and `U/C`); the per-level components
`𝒞⁺_{n,1}` and this particular `ℂ_[p]`-embedded tower are RJW bookkeeping. There is therefore **no
"literature-standard form of `cycloTower1Plus` as a standalone object"** to anchor a generalisation —
its generality questions all live on its operands and on the ambient `NormCompatUnits`, assessed
separately.
```

## Phase 4 — Generality analysis

```
### Generality analysis — `cycloTower1Plus`

Literature-standard form (from Phase 3): the inverse limit `lim←_{n≥1} 𝒞⁺_{n,1}`, i.e. the
levelwise-membership subgroup of the inverse-limit group `𝒰_∞`.
```

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|---|---|---|---|---|
| 1 | ambient `NormCompatUnits p` | bespoke `ℂ_[p]`-embedded inverse limit of local unit groups | inverse limit of an arbitrary inverse system of groups | yes (on the ambient) | weakening means generalising/abstracting `NormCompatUnits` itself (an inverse limit over an arbitrary system) — **operand-level**, out of scope for *this* decl |
| 2 | per-level component `cycloClosureOnePlus p n` | project plus-principal-closure of cyclotomic units in `ℂ_[p]` | abstract `𝒞⁺_{n,1}` over a totally-real base | yes (on the component) | weakening lives on `cycloClosureOnePlus`/`cycloClosurePlus`/`cycloUnits` — **operand-level** |
| 3 | index restriction `1 ≤ n` | quantifier `∀ n, 1 ≤ n → …` | the tower's natural index set | NO | forced by `NormCompatUnits.compat` (norm coherence only imposed for `n ≥ 1`); not a free generality knob |
| 4 | the levelwise-membership construction | `{u | ∀ n ≥ 1, u.elems n ∈ A_n}` | inverse-limit subgroup = `⨅_n comap eval_n A_n` | NO | this *is* the maximally general spelling of "inverse-limit subgroup carved by levelwise membership"; nothing to weaken on the *combinator* |

```
### Generality verdict (Phase 4b)

The current form is: MAXIMALLY GENERAL *for the construction itself* (the inverse-limit /
levelwise-membership combinator cannot be weakened; 0 weakening opportunities on THIS decl).
Number of weakening opportunities found (on this decl): 0.
All generality questions (rows 1, 2) are inherited from the OPERANDS (`NormCompatUnits`,
`cycloClosureOnePlus`) and are those decls' own assessments — they do not make `cycloTower1Plus`
itself "strictly narrower than a standalone literature form", because there is no standalone
literature form of *the combinator* to be narrower than.
Proposed restatement: none for this decl (operand-level only).
Cost of restatement: n/a (no restatement of this decl is proposed).
```

```
### Modern-idiom check (Phase 4c)
```

| # | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|---|---|---|---|---|
| 1 | bundled-hypotheses → typeclasses/instances? | no | the def has no "let X be a foo" preamble; it is data | — |
| 2 | sequences/metric → filters/topological? | no | the `∀ n` is the inverse-system index, not a convergence; topology lives in the operand `topologicalClosure` already | — |
| 3 | construct an object → universal-property class? | partial (but NOT for this decl) | the *inverse limit itself* (`NormCompatUnits`) could be a categorical `limit`/`InverseSystem.limit` with a universal property — a genuine modernisation **of the ambient structure**, not of `cycloTower1Plus`, which is forced to be the levelwise-membership subgroup once the ambient + components are fixed | (operand-level: would let the whole tower compose with mathlib's `CategoryTheory` limit API) |
| 4 | set-with-closure-predicate → bundled substructure? | no | it is **already** a bundled `Subgroup` (the modern idiom), not an ad-hoc set | — |
| 5 | vector-space/field-specific → weaker typeclass? | no | no field-specific structure on the combinator | — |
| 6 | 1-categorical → higher/∞-categorical? | no | a plain inverse limit of groups; no categorification target | — |
| 7 | concrete index (ℕ,ℤ,ℝ) → arbitrary monoid/order? | partial (operand-level) | the index `ℕ` could be an arbitrary directed/inverse system — but again that is the **ambient `NormCompatUnits`** generalisation, not this decl's | (operand-level) |

```
### Modern-idiom verdict (Phase 4c)

Modern idiom available: no — *for this declaration itself*.
The levelwise-membership subgroup of an inverse-limit group is **already** in the modern mathlib
idiom: bundled `Subgroup`, and (Phase 5/6) exactly expressible as `⨅_n comap (eval_n) A_n` /
`Subgroup.pi`-style. A real Bourbaki-2.0 modernisation exists **one level down** — give the ambient
`NormCompatUnits` a categorical `InverseSystem.limit` / `CategoryTheory` home with a universal
property, after which `cycloTower1Plus` would specialise as the levelwise-membership subgroup. But
that restatement is of the **operand** (`NormCompatUnits`), with downstream consequences for the
whole tower, not for `cycloTower1Plus` in isolation. There is no modern-idiom restatement of
`cycloTower1Plus` *itself* with concrete downstream consequences, so the Bourbaki-2.0 YES is
**withheld** for this decl (asserting it would fail the Phase-7 gate's "downstream consequences"
requirement). One-line reason it is not a modernisation move on this decl: once the ambient group and
the per-level subgroups are fixed, the object is forced to be their levelwise-membership inverse-limit
subgroup — there is no freedom left to "modernise".
```

## Phase 4.5 — Diamond / defeq risk (`def`)

```
### Diamond / defeq risk — `cycloTower1Plus`
```

| # | Risk | Verdict | Evidence / rationale |
|---|---|---|---|
| 1 | Typeclass diamond | none | introduces **no instance**; reuses `NormCompatUnits`'s existing `CommGroup` and mathlib's `Subgroup` lattice/`SetLike`. No new typeclass-search path. |
| 2 | Reducibility leak | none | sealed `def` (no `@[reducible]`); the carrier is a `setOf` predicate, not exposed to global defeq. |
| 3 | Non-canonical unfolding | low | consumers explicitly `rw`/unfold via the membership predicate (e.g. Main.lean's `intro n hn` then work levelwise); no surprising `simp`/`rfl` unfolds — same as the twin `unitsTower1Plus`. |
| 4 | Instance priority collision | none | not an `instance`. |
| 5 | Universe-polymorphism issues | none | everything is at a fixed universe (`ℂ_[p]ˣ`, `NormCompatUnits p` are concrete `Type`); no universe annotation forced. |
| 6 | Coercion ambiguity | none | the only coercion is `Subgroup`'s standard `SetLike` `↥`/`mem`; no competing `CoeFun`/`CoeSort`. |

```
### Risk verdict (Phase 4.5)
Overall risk: NONE
Top risks: none
Recommended mitigations: none required.
```

## Phase 5 — Mathlib search (five-method)

```
### Mathlib search-status: `cycloTower1Plus`
```

```
[A] Lean-Finder       (semantic: "subgroup of inverse limit by levelwise membership")   n/a: tool not available in-env — substituted by D + E over the local .lake/packages/mathlib checkout
[B] Loogle            `(∀ i, Subgroup (f i)) → Subgroup (∀ i, f i)` ; `Subgroup _ → (_ →* _) → Subgroup _`   hits on the GENERIC combinators (`Subgroup.pi`, `Subgroup.comap`) — NOT on any cyclotomic/inverse-limit-of-units object
[C] LeanSearch        "inverse limit of subgroups", "projective limit of cyclotomic units plus part"   concept (as a named object) absent from mathlib; generic limit scaffolding present
[D] Grep mathlib src  `cyclotomicunit`, `InverseLimit`/`projective limit`, `Subgroup.pi`, `Subgroup.comap`, `mem_iInf`, `evalMonoidHom`, `ProfiniteGrp`   see hits below
[E] Name pattern      `cycloTower*`, `unitsTower*`, `*Tower1Plus`, `NormCompatUnits`   found ONLY in this project
```

Mathlib hits found by [B]/[D] (the **generic scaffolding**, by qualified name):
- `Subgroup.pi` (`Mathlib/Algebra/Group/Subgroup/Basic.lean:176`) — `pi (I : Set η) (H : ∀ i, Subgroup (f i)) : Subgroup (∀ i, f i)`: subgroup of a **bare product** `∀ i, f i` carved by levelwise membership. Membership `Subgroup.mem_pi` (`:186`): `p ∈ pi I H ↔ ∀ i ∈ I, p i ∈ H i` — the **exact predicate shape** of `cycloTower1Plus`, **but over the product type**, not over the bespoke inverse-limit structure `NormCompatUnits`.
- `Subgroup.comap` (`Mathlib/Algebra/Group/Subgroup/Map.lean:72`), `Subgroup.mem_comap` (`:82`) — pull back a subgroup along a hom.
- `Subgroup.iInf` / `Subgroup.mem_iInf` (`Mathlib/Algebra/Group/Subgroup/Lattice.lean:252`) — `x ∈ ⨅ i, S i ↔ ∀ i, x ∈ S i`.
- `Pi.evalMonoidHom` (`Mathlib/Algebra/Group/Pi/Lemmas.lean:199`) — the per-coordinate evaluation hom, **for the product type only**.
- Inverse-limit infrastructure: `InverseSystem`/`Order.DirectedInverseSystem` (`Mathlib/Order/DirectedInverseSystem.lean`), `CategoryTheory.CofilteredSystem`, `Mathlib/Topology/Algebra/Category/ProfiniteGrp/Limits.lean` — generic inverse-limit-of-groups machinery; **none** instantiated for a cyclotomic-unit tower.
- `Mathlib/RingTheory/RootsOfUnity/CyclotomicUnits` — generic number-field cyclotomic units (per-element associatedness style; **0 group-of-units defs**, no tower, no plus part).

```
Searched for both:
  - the user's current form  (𝒞⁺_{∞,1}, levelwise membership over NormCompatUnits) — absent
  - the literature-standard form (inverse limit / proj. limit of cyclotomic units, plus part) — absent as a named mathlib object; only the GENERIC inverse-limit-of-groups scaffolding exists

Concluded: not in mathlib (all 5 methods exhausted, plus the literature-standard form). Mathlib has
the GENERIC levelwise-membership/inverse-limit-subgroup combinators (`Subgroup.pi` + `Subgroup.mem_pi`
for the product case; `Subgroup.comap` + `Subgroup.iInf` + `Pi.evalMonoidHom` for the general
pulled-back case) and generic inverse-limit-of-groups infrastructure — but NO cyclotomic-unit tower,
NO plus part, and NO eval-homs / subgroups for the project structure `NormCompatUnits`.
```

This is decisive against `NO-mathlib-has-it`: there is no `cycloTower1Plus`-analogue (nor any of its
project operands `cycloClosureOnePlus`/`NormCompatUnits`) in mathlib to cite and specialise from.
The contrast with the twin family is the same as the siblings': mathlib has the *combinator*
(`Subgroup.pi`/`comap`/`iInf`), the project has the *operands*.

## Phase 6 — Composition check (+ call-sites)

### Phase 6.0 — Call sites (composability signal)

```
### Call sites — `cycloTower1Plus`

Internal use count (excl. declaring line): K = 9+ (all within this project)
External-to-file callers: 1 file — `IwasawaProof/Main.lean` (the §12 Main-Conjecture file)
```

| Caller file:line | Usage pattern (one-line excerpt) |
|---|---|
| `IwasawaProof/Main.lean:477` | `(hu : u ∈ cycloTower1Plus p) : Col p u ∈ … zetaIdeal …` — hypothesis of `col_mem_zetaIdeal_of_mem_cycloTower1Plus` |
| `IwasawaProof/Main.lean:523` | `have hplus : u * galNCU p (-1) u ∈ cycloTower1Plus p := by …` |
| `IwasawaProof/Main.lean:609` | `theorem cycloTower1Plus_le_cycloTower1 : cycloTower1Plus p ≤ cycloTower1 p := by …` |
| `IwasawaProof/Main.lean:618` | `theorem cycloTower1Plus_le_unitsTower1Plus : cycloTower1Plus p ≤ unitsTower1Plus p := by …` |
| `IwasawaProof/Main.lean:691` | `(↥(unitsTower1Plus p) ⧸ (cycloTower1Plus p).subgroupOf (unitsTower1Plus p)) →* …` — **the plus-part SES quotient of RJW's main diagram** |
| `IwasawaProof/Main.lean:694` | `QuotientGroup.lift ((cycloTower1Plus p).subgroupOf (unitsTower1Plus p)) …` |
| `IwasawaProof/Main.lean:746-747` | `theorem mem_cycloTower1Plus_of_mem_cycloTower1_unitsTower1Plus … : u ∈ cycloTower1Plus p := by …` |
| `IwasawaProof/Main.lean:852-853` | `have hcycloPlus : … ∈ cycloTower1Plus p := mem_cycloTower1Plus_of_…` |
| `IwasawaProof/Main.lean:892` | `Additive (↥(unitsTower1Plus p) ⧸ (cycloTower1Plus p).subgroupOf (unitsTower1Plus p)) ≃+ …` |

```
Inline-derivation grep (was the equivalent levelwise predicate re-derived elsewhere without using
`cycloTower1Plus`?):
  - (none) — every consumer goes through the def; the membership lemmas
    (`mem_cycloTower1Plus_of_mem_cycloTower1_unitsTower1Plus`) and the `≤` lemmas
    (`cycloTower1Plus_le_cycloTower1`, `cycloTower1Plus_le_unitsTower1Plus`) all `intro n hn` and
    unfold to the per-level component `cycloClosureOnePlus p n`.
```

**Call-sites reading.** K ≥ 9 internal uses, no inline re-derivation → this is **real, load-bearing
project API**, the plus-side carrier of RJW's main Iwasawa SES. By the Phase-6.0.1 table this leans
toward a YES bucket on the *composability* axis. BUT (as with `cycloClosureOne`, K ≥ 3) **every use
either unfolds it levelwise to its component `cycloClosureOnePlus p n`, or treats it as a `Subgroup`
black box for the generic quotient API** (`.subgroupOf`, `QuotientGroup.lift`) — i.e. the consumers
exercise *mathlib's generic subgroup/quotient machinery* applied to a project object, not new facts
about a new abstraction. The signal says "load-bearing project glue", **not** "standalone mathlib
abstraction": the object is needed *here* precisely because its operands (`NormCompatUnits`,
`cycloClosureOnePlus`) are project-local.

### Phase 6a — Composition attempt

```
### Composition check (Phase 6)

Can `cycloTower1Plus` be derived from mathlib in ≤3 chained calls?
```

The carrier `{u | ∀ n, 1 ≤ n → u.elems n ∈ cycloClosureOnePlus p n}` is *exactly* the inverse-limit /
levelwise-membership pattern mathlib bundles, written two equivalent ways:

- **Attempt 1 (`Subgroup.pi`-shape):** mathlib's `Subgroup.pi {n | 1 ≤ n} (fun n => cycloClosureOnePlus p n)`
  has membership `Subgroup.mem_pi`: `p ∈ pi I H ↔ ∀ i ∈ I, p i ∈ H i` — the same predicate. **Mathlib
  decls used:** `Subgroup.pi`, `Subgroup.mem_pi`. **Result: PARTIAL.** `Subgroup.pi` lives over the
  **bare product** `∀ n, ℂ_[p]ˣ`; `cycloTower1Plus` is over `NormCompatUnits p` (the inverse-limit
  *substructure*). To use `Subgroup.pi` one must first transport along the structure-to-product map
  `u ↦ u.elems` — which is itself a **project-defined** monoid hom, not in mathlib.
- **Attempt 2 (`comap`+`iInf`-shape):** `⨅ n, ⨅ (_ : 1 ≤ n), (cycloClosureOnePlus p n).comap (evalₙ)`
  where `evalₙ : NormCompatUnits p →* ℂ_[p]ˣ`, `u ↦ u.elems n`, with membership by
  `Subgroup.mem_iInf` + `Subgroup.mem_comap`. **Mathlib decls used:** `Subgroup.comap`,
  `Subgroup.iInf`, `Subgroup.mem_iInf`, `Subgroup.mem_comap`. **Result: PARTIAL — same gap.** The
  eval homs `evalₙ` are **not in mathlib** for the project structure `NormCompatUnits` (the product's
  `Pi.evalMonoidHom` does not apply to a bespoke structure), and the components `cycloClosureOnePlus p n`
  are project-specific.

```
Conclusion: NOT-COMPOSABLE *from mathlib alone* (in the Case-4 sense), BUT trivially composable from
mathlib's generic combinators ONCE the project objects exist.
```

The precise reading (mirroring the sibling `cycloClosureOne`): mathlib supplies the **generic
levelwise-membership/inverse-limit-subgroup combinator** (`Subgroup.pi`/`mem_pi`, or
`comap`+`iInf`), but the **entire mathematical content** — the inverse-limit structure
`NormCompatUnits`, the per-level evaluation homs, and the per-level components `cycloClosureOnePlus`
— is **project-defined and absent from mathlib**. So this is *not* Case 4 "mathlib's own building
blocks reproduce the object in ≤3 mathlib calls" (mathlib's blocks need the project's operands), and
it is *not* a standalone mathlib-worthy definition: its content is the project operands, glued by a
combinator mathlib already owns. It is the inverse-limit analogue of a thin `⊓`-wrapper.

## Phase 7 — Verdict

```
## Verdict: `cycloTower1Plus`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the *ingredients* (cyclotomic units, their inverse-limit tower, the
  plus part, `U/C`) are standard Iwasawa theory (JTNB semi-local-units line, Hida, Sharifi, RJW);
  the *combinator* (inverse-limit subgroup by levelwise membership) is the generic
  limit-in-Grp/`Subgroup.pi` construction; the specific object `𝒞⁺_{∞,1}` is RJW-local bookkeeping
  with no standalone literature form to anchor a generalisation.
- Generality analysis (Phase 4): MAXIMALLY GENERAL *for the construction* (0 weakenings on this decl;
  all generality lives on the operands `NormCompatUnits`/`cycloClosureOnePlus`). Phase 4c: modern-idiom
  YES **withheld** (already bundled `Subgroup`; the only real modernisation — a categorical `limit`
  home — is the *ambient* `NormCompatUnits`'s, not this decl's).
- Mathlib search (Phase 5): not in mathlib under either form; mathlib has only the generic
  `Subgroup.pi`/`comap`/`iInf` combinators and generic inverse-limit-of-groups infrastructure — no
  cyclotomic tower, no plus part, no eval-homs/subgroups for the project structure `NormCompatUnits`.
- Composition check (Phase 6): NOT-COMPOSABLE in the Case-4 sense (mathlib's combinators need the
  project's operands), trivially composable once the project objects exist — i.e. a thin
  inverse-limit/levelwise-membership wrapper over project objects.
```

**Rationale.**

`cycloTower1Plus p` is `𝒞⁺_{∞,1} = lim←_{n≥1} 𝒞⁺_{n,1}`, the plus part of the norm-coherent tower of
principal-unit p-adic closures of the cyclotomic units — a genuinely central Iwasawa-theory object
(the plus side of the Coleman-map source in RJW's Main-Conjecture diagram; the literature's `C⁺` in
the `U/C` story). But mathlib-worthiness is not "is the object standard"; it is "is *this declaration*
the right thing for mathlib to own." And this declaration is the **inverse-limit analogue of a thin
`⊓`-wrapper**: a `Subgroup (NormCompatUnits p)` whose carrier is the levelwise-membership predicate
`∀ n ≥ 1, u.elems n ∈ cycloClosureOnePlus p n`. That predicate is *exactly* the shape mathlib bundles
as `Subgroup.pi` (membership `Subgroup.mem_pi`: `∀ i ∈ I, p i ∈ H i`), equivalently
`⨅ n, comap (evalₙ) (cycloClosureOnePlus p n)` via `Subgroup.comap` + `Subgroup.iInf`. The *operation*
— carve an inverse-limit subgroup by levelwise membership — is already mathlib's; the **operands are
the project's**: the ambient structure `NormCompatUnits p` (a bespoke inverse limit, not the bare
product, so even `Pi.evalMonoidHom` does not apply — the eval homs would themselves be project
definitions), and every per-level component `cycloClosureOnePlus p n` (itself a project `⊓` of
project objects with no mathlib counterpart). So there is nothing new to *add*: a reader needing
`𝒞⁺_{∞,1}` writes the levelwise-membership subgroup over their inverse limit and reasons with
`Subgroup.mem_pi`/`mem_iInf` — which is exactly what every call site in `Main.lean` already does
(`intro n hn`, then work on the factor `cycloClosureOnePlus p n`, or hand the whole thing to the
generic `.subgroupOf`/`QuotientGroup.lift` API). The decl is a one-liner without a Phase-2b exemption
(no defeq barrier — consumers punch through it; no instance — no diamond; the name is only weak
RJW-source-faithfulness scaffolding), which per the gate forecloses a YES on a one-liner without an
explicit override, and there is none to give: this is **not a missing mathlib primitive**
(`Subgroup.pi`/`comap`/`iInf` already exist), it is a project-local naming of "the inverse-limit
subgroup of these project objects."

This is `NO-composable-from-mathlib` rather than the neighbouring buckets, for precise reasons —
matching its siblings `cycloClosureOne`/`cycloClosurePlus` (also NO-composable) and **deliberately
NOT** matching `cycloUnitsPlus` (BORDERLINE):

- **Not `NO-mathlib-has-it`:** mathlib has no `𝒞⁺_{∞,1}` object, no cyclotomic-unit tower, and not
  even its operands (`NormCompatUnits`, `cycloClosureOnePlus`) — Phase 5 found only the generic
  combinators and generic inverse-limit infrastructure. The "found in mathlib as `<X>`" requirement
  fails. (Contrast the twin `globalUnitsPlus`, whose abstract `realUnits` *does* exist in mathlib.)
- **Not `YES-add-as-is` / `YES-but-generalise-first`:** Phase 4 found 0 weakenings on this decl and
  Phase 4c withheld the modern-idiom YES — the construction is one generic combinator, maximally
  general and already idiomatic, with no new content. Crucially, the contrast with `cycloUnitsPlus`
  (BORDERLINE) is sharp: there, the contributable abstract object (`cyclotomicUnits ⊓ realUnits`)
  required *building a missing mathlib parent group*, a real open question (does mathlib want a
  bundled cyclotomic-units group?). **Here there is no missing combinator to build** — the
  inverse-limit-subgroup-by-levelwise-membership pattern is already `Subgroup.pi`/`comap`/`iInf` in
  mathlib. So `cycloTower1Plus` has *no* "build the absent abstraction and upstream that" pathway and
  therefore *no* BORDERLINE judgment call: the only abstraction it would need (the categorical
  inverse-limit home) belongs to its *operand* `NormCompatUnits`, not to this combinator.
- **Not `BORDERLINE`:** the buckets do not genuinely tie. The only judgment in play — should the
  *project* keep this readability wrapper / does the ambient `NormCompatUnits` deserve a categorical
  `limit` home — is a project-cleanup / operand-level question, not a mathlib-inclusion question
  about `cycloTower1Plus`, and the mathlib-inclusion answer for *this* decl is unambiguous: mathlib
  should not own a named levelwise-membership subgroup of foreign project objects when it already
  owns the combinator.

No cost-based reasoning is used anywhere (cost is not a verdict factor).

**WHY not (refactor-actionable detail).**
Mathlib has the building blocks — the inverse-limit/levelwise-membership *combinator* — but the
operands are the project's, so `cycloTower1Plus` is a project-local naming, not a mathlib
contribution. Concretely:

  Mathlib building blocks (by qualified name + path):
  - `Subgroup.pi` (`Mathlib/Algebra/Group/Subgroup/Basic.lean:176`) + `Subgroup.mem_pi` (`:186`)
  - `Subgroup.comap` (`Mathlib/Algebra/Group/Subgroup/Map.lean:72`) + `Subgroup.mem_comap` (`:82`)
  - `Subgroup.iInf` / `Subgroup.mem_iInf` (`Mathlib/Algebra/Group/Subgroup/Lattice.lean:252`)
  - (`Pi.evalMonoidHom`, `Mathlib/Algebra/Group/Pi/Lemmas.lean:199`, for the bare-product case only —
    the project would need its own `NormCompatUnits.elemsHom n : NormCompatUnits p →* ℂ_[p]ˣ`.)

  Composition sketch (the inverse-limit subgroup, ≤3 mathlib calls *given the project eval homs*):
  ```lean
  -- with `evalₙ : NormCompatUnits p →* ℂ_[p]ˣ := { toFun := (·.elems n), … }` (PROJECT hom)
  example : cycloTower1Plus p
      = ⨅ n, ⨅ (_ : 1 ≤ n), (cycloClosureOnePlus p n).comap (evalₙ p n) := by
    ext u; simp [cycloTower1Plus, Subgroup.mem_iInf, Subgroup.mem_comap]  -- membership predicates coincide
  ```

  Call sites in our project (from Phase 6.0): K ≥ 9 (all in `IwasawaProof/Main.lean`).

  Refactor plan (project-local — this is **NOT** a mathlib PR):
  1. **Keep `cycloTower1Plus` as-is in the project.** It is correct, idiomatically named
     (`lowerCamelCase` for data), and is load-bearing glue — the plus-side carrier of RJW's main SES
     `unitsTower1Plus / cycloTower1Plus.subgroupOf unitsTower1Plus`. There is nothing to fix and no
     consumer that would benefit from inlining the levelwise predicate at K ≥ 9 sites.
  2. **Do not propose `cycloTower1Plus` to mathlib** — a levelwise-membership subgroup of two
     project-local objects (`NormCompatUnits`, `cycloClosureOnePlus`) is not a mathlib contribution;
     mathlib already owns the combinator (`Subgroup.pi`/`comap`/`iInf`).
  3. **If** any mathlib-direction work is wanted from this file, it lives on the **operands**, each
     assessed separately:
     - `NormCompatUnits` (the ambient inverse limit) → the real Bourbaki-2.0 move is to give it a
       categorical `InverseSystem.limit` / `CategoryTheory` limit home with a universal property
       (`Mathlib/Order/DirectedInverseSystem.lean`, `ProfiniteGrp/Limits.lean`); then this tower
       would specialise as a `Subgroup.pi`/`comap` instance. That is the operand's assessment.
     - `cycloClosureOnePlus` / `cycloClosurePlus` / `cycloUnits` → the contributable object (if any)
       is an abstract "cyclotomic units / their local closure / plus part" API, the BORDERLINE
       question already raised for `cycloUnits`/`cycloUnitsPlus`.
  4. Optionally, for *project* readability, the `Subgroup.pi`/`comap`+`iInf` reformulation in the
     sketch above could replace the hand-rolled `where` (giving free `mem_iInf`/`mem_pi` membership
     lemmas) once a `NormCompatUnits.elemsHom` is in the project — but this is a `/cleanup`/`/refactor`
     nicety, **not** a mathlib action, and the current `where` form is perfectly idiomatic.

  Next action: keep project-local; no mathlib PR. (Operand-level mathlib work, if pursued, is the
  separate assessments of `NormCompatUnits` and the `cycloUnits*` family.)

### Verdict gate check
- Phase 6 conclusion was NOT-COMPOSABLE (Case-4 sense) → `NO-composable-from-mathlib` is admissible.
- Phase 5 was NOT "found in mathlib as <X>" → correctly NOT `NO-mathlib-has-it`.
- Phase 4b = MAXIMALLY GENERAL (this decl) and Phase 4c modern-idiom YES withheld → YES buckets correctly excluded.
- The bucket-specific WHY names the concrete mathlib building blocks (`Subgroup.pi`/`mem_pi`,
  `comap`/`mem_comap`, `iInf`/`mem_iInf`, `Pi.evalMonoidHom`) by qualified name + path, includes the
  ≤3-call composition sketch, and gives the refactor plan naming the K ≥ 9 call sites — satisfying the
  NO-verdict refactor-actionable gate.
- No cost-based reasoning used.

---

## Phase 8 — Report (consolidated)

This document is the consolidated Phase-8 artifact (Phases 0–7 above, in order).

### Evidence pointers (for the Phase-7 gate)
- **Phase 3 table:** 10 channels, ≥3 substantive WebSearch channels at different generality levels
  (specific `C_{∞,1}⁺`; general "plus part of proj. limit of cyclotomic units / `U/C`"; the generic
  "inverse-limit-subgroup-by-levelwise-membership" pattern), with sources (jtnb.1284, arXiv:0910.1411,
  RJW 2309.15692, Hida/Sharifi notes, nLab inverse-limit/profinite). ChatGPT-MCP and local-refs
  recorded `n/a: <reason>` (not blank); Stacks recorded `n/a: not alg-geom`.
- **Phase 4:** explicit "0 weakenings on this decl; all generality is operand-level"; Phase 4c
  Bourbaki-2.0 YES **withheld** for this decl (modernisation belongs to the ambient `NormCompatUnits`).
- **Phase 4.5:** six-row risk table, overall NONE (no instance introduced).
- **Phase 5:** five methods (A `n/a` with substitute; B–E run); mathlib combinators cited by
  qualified name + path (`Subgroup.pi`/`mem_pi`, `comap`/`mem_comap`, `iInf`/`mem_iInf`,
  `Pi.evalMonoidHom`, `InverseSystem`); concluded "not in mathlib (both forms)".
- **Phase 6:** composition is the generic inverse-limit/levelwise-membership combinator, but its
  operands (`NormCompatUnits`, `cycloClosureOnePlus`) are project-specific → not Case-4
  mathlib-composable; call-sites table shows K ≥ 9 with no inline re-derivation, every use either
  unfolds levelwise or uses generic subgroup/quotient API.
- **Sibling consistency:** lands `NO-composable-from-mathlib` exactly like `cycloClosureOne` /
  `cycloClosurePlus` (thin lattice/inverse-limit wrappers), and **not** `BORDERLINE` like
  `cycloUnits`/`cycloUnitsPlus` (which need a missing abstract *parent group* built first — a
  judgment call this combinator does not present, since `Subgroup.pi`/`comap`/`iInf` already exist).

## Next step

Keep `cycloTower1Plus` project-local; do **not** open a mathlib PR (mathlib already owns the
inverse-limit/levelwise-membership combinator — `Subgroup.pi`/`comap`/`iInf` — and the operands are
project-specific). Any mathlib-direction work from this file lives on the operands, assessed
separately: a categorical `InverseSystem.limit` home for the ambient `NormCompatUnits`, and the
already-flagged BORDERLINE abstract `cyclotomicUnits`/plus-part API for the `cycloUnits*` family.
