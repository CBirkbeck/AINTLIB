# /mathlibable report — `PadicLFunctions.Coleman.mem_localUnits_iff`

**Mode:** A (single declaration, full 10-phase workflow with exhaustive 9-channel literature search)
**Target:** `PadicLFunctions.Coleman.mem_localUnits_iff`
**Kind:** `lemma` (glue lemma; body is `Iff.rfl`)
**Source:** `projects/PadicLFunctions/PadicLFunctions/Iwasawa/LocalUnits.lean:55`
**Date:** 2026-06-20

---

## FINAL VERDICT: `NO-mathlib-has-it`

> `mem_localUnits_iff` is the `mem_X_iff := Iff.rfl` companion lemma for the project's `def
> localUnits p n : Subgroup ℂ_[p]ˣ`, whose carrier is `{u | (u : ℂ_[p]) ∈ O p n ∧ ((u⁻¹ : ℂ_[p]ˣ)
> : ℂ_[p]) ∈ O p n}`. **Mathlib already has this exact lemma**, at strictly greater generality:
> `Submonoid.mem_units_iff (S : Submonoid M) (x : Mˣ) : x ∈ S.units ↔ ((x : M) ∈ S ∧ ((x⁻¹ : Mˣ)
> : M) ∈ S) := Iff.rfl` (`Mathlib/Algebra/Group/Submonoid/Units.lean:101`), the companion to
> `def Submonoid.units (S : Submonoid M) : Subgroup Mˣ` (`:49`) — "the units of `S`, packaged as
> a subgroup of `Mˣ`". The project's `localUnits p n` **is** `(O p n).toSubmonoid.units` (the
> carriers are definitionally equal: a unit `u` with `u, u⁻¹ ∈ O p n`), and `mem_localUnits_iff`
> **is** `Submonoid.mem_units_iff (O p n).toSubmonoid u` modulo the definitional coercion
> `Subring.mem_toSubmonoid` (`Mathlib/Algebra/Ring/Subring/Defs.lean:405`, itself `Iff.rfl`).
> The user's form therefore follows from the mathlib lemma in **0–1 lines**. This is a
> `NO-mathlib-has-it` of the strongest kind: not only the *lemma* but the *parent construction*
> it unfolds is already upstream — `localUnits`/`mem_localUnits_iff` is a hand-rolled
> re-implementation of mathlib's `Submonoid.units`/`Submonoid.mem_units_iff`.

*(Contrast with the sibling `PadicMeasure.mem_zetaIdeal_iff`, which was `NO-composable-from-mathlib`
**because its parent `zetaIdeal` is absent from mathlib** — there was no upstream decl to cite. Here
the parent `Submonoid.units` **is** in mathlib with its own `mem_units_iff`, so the stronger
`NO-mathlib-has-it` fires: we can name the exact mathlib lemma the user's statement specialises from.)*

*(Why not `BORDERLINE`: the only judgment call — "should `localUnits` itself be re-expressed as
`(O p n).toSubmonoid.units`?" — is a refactor question about the **parent def**, and it has a clean
answer (yes; they are defeq). It does not make *this `Iff.rfl` lemma's* verdict ambiguous. The lemma's
verdict is unambiguous: mathlib has it as `Submonoid.mem_units_iff`.)*

---

## Phase 0 — Doctor / baseline

### Baseline (Phase 0)
- **lake build:** **not re-run** (worktree build is stale/slow per the task's build note). **Reasoned from source** — read the target lemma, its parent `def localUnits` (`LocalUnits.lean:39`), the type dependencies `O` (`Coleman/Tower.lean:331`), `integerRing` (`Coefficients.lean:41`), `K` (`Tower.lean:98`), all 5 call sites, and the mathlib search surface (`Submonoid.units`/`mem_units_iff`, `ValuationSubring.unitGroup`, `Subring.mem_toSubmonoid`) directly from `.lake/packages/mathlib`. The skill's Phase-0 fallback explicitly permits this.
- **decl `PadicLFunctions.Coleman.mem_localUnits_iff`:** ✓ resolved at `LocalUnits.lean:55` (unique match; the qualified-aware grep for `lemma mem_localUnits_iff` returns exactly one declaration).
- **kind:** `lemma` (an `Iff`, proved by `Iff.rfl`).
- **has sorry:** **no.** The lemma body is `Iff.rfl`; `LocalUnits.lean` is sorry-free; the parent `def localUnits` and all 5 consumers are complete proofs.
- **module docstring summary:** "Local unit groups of the cyclotomic tower (RJW §9, TeX 2471–2505)" — `𝒰_n = 𝒪_{K_n}^×` and principal units `𝒰_{n,1}` as subgroups of `ℂ_[p]ˣ`, the `+`-subfield `K_n⁺`, and the `ℤ_p`-power structure on principal units. The lemma is the membership criterion for the first object, `localUnits`.

## Phase 1 — Comprehend

### Statement (Phase 1)

```lean
lemma mem_localUnits_iff {n : ℕ} {u : ℂ_[p]ˣ} :
    u ∈ localUnits p n
      ↔ (u : ℂ_[p]) ∈ O p n ∧ ((u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ∈ O p n :=
  Iff.rfl
```
with `variable (p : ℕ) [hp : Fact p.Prime]`.

`mem_localUnits_iff` is **a theorem stating** the following (read mathematically):

A unit `u ∈ ℂ_p^×` lies in the local unit group `𝒰_n = 𝒪_{K_n}^×` **iff** both `u` and `u⁻¹`
(as elements of `ℂ_p`) lie in the integer ring `O_n = O_{K_n}` of the `n`-th layer of the
cyclotomic tower. That is: membership in `𝒰_n` unfolds to "`u` is a unit of the subring `O_n`",
spelled out as "`u ∈ O_n` and `u⁻¹ ∈ O_n`."

**Crucially**, the right-hand side is **verbatim** the defining `carrier` of the parent
`def localUnits` (`LocalUnits.lean:39–53`):
```lean
def localUnits (n : ℕ) : Subgroup ℂ_[p]ˣ where
  carrier := {u | (u : ℂ_[p]) ∈ O p n ∧ ((u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ∈ O p n}
  mul_mem' := …; one_mem' := …; inv_mem' := …
```
So `u ∈ localUnits p n` is **definitionally** `u ∈ carrier`, i.e. the RHS predicate; hence the
proof is `Iff.rfl`.

**Dependency unfolding (Lean side):**
- `ℂ_[p]` = `Completion (PadicAlgCl p)` — the completed algebraic closure `ℂ_p` of `ℚ_p` (a `NormedField`).
- `localUnits p n : Subgroup ℂ_[p]ˣ` (`LocalUnits.lean:39`) — `𝒰_n = 𝒪_{K_n}^×` (RJW TeX 2474), defined by the carrier predicate above.
- `O p n : Subring ℂ_[p]` := `(K p n).toSubring ⊓ integerRing ℂ_[p]` (`Tower.lean:331`) — the integer ring `O_{K_n}` (the norm-unit-ball of `K_n`).
- `K p n : IntermediateField ℚ_[p] ℂ_[p]` (`Tower.lean:98`) — the `n`-th layer `K_n = ℚ_p(ξ_{p^n})`.
- `integerRing L : Subring L` (`Coefficients.lean:41`) — the closed unit ball `{x | ‖x‖ ≤ 1}` as a subring.

**Variables / typeclasses involved (Lean side):**
- `p : ℕ`, `[Fact p.Prime]` — the prime; fixes `ℚ_[p]`, `ℂ_[p]`.
- `{n : ℕ}` — implicit; the tower layer.
- `{u : ℂ_[p]ˣ}` — implicit; the unit whose membership is tested.

**Hypotheses (math):** none.

**Conclusion (math):** `u ∈ 𝒰_n ⟺ u ∈ O_n ∧ u⁻¹ ∈ O_n` — the definition of "unit of the subring `O_n`".

**Conclusion (Lean):** an `Iff` between `u ∈ localUnits p n` and the carrier predicate; proved by `Iff.rfl`.

## Phase 2 — Preliminary checks

### Size classification (Phase 2a)

**Verdict: SMALL.** It is a `mem_X_iff` glue lemma — the definitional-membership companion to
`def localUnits`. It introduces **no** new structure (the structure is `localUnits`, a *different*
declaration), is not itself a "Main result" (the module docstring's headline objects are the
*subgroups* `𝒰_n`, `𝒰_{n,1}`, the `ℤ_p`-module structure, the towers `𝒰_∞`, not their `mem_*_iff`
lemmas), and is not named after a person/place. It is a helper/restatement.
*(Literature width is EXHAUSTIVE regardless; recorded for framing.)*

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure`, so the formal one-liner check is **n/a**.
For the record, the body **is** a single token (`Iff.rfl`) — the lemma-analogue of a one-liner.
This reinforces the "glue, not content" reading but does not trigger the def exemption table.
**Conclusion: n/a (kind is lemma); body is the trivial `Iff.rfl`.**

## Phase 3 — EXHAUSTIVE literature search (9+ channels)

The literature question is two-pronged: (a) the *mathematical concept* it unfolds — the local
unit group `𝒰_n = 𝒪_{K_n}^×` of a cyclotomic tower, and more abstractly "the unit group of a
subring / submonoid, characterised by `u` and `u⁻¹` both lying in it"; and (b) the *idiom* it
embodies — a `mem_X_iff := Iff.rfl` restatement for a `SetLike` carrier. Both are searched. The
`ℂ_p`/cyclotomic-tower lineage (RJW arXiv:2309.15692) is the project's source and is established
across the sibling reports; this report aims the channels at the *unit-group-of-a-subring* concept
and the *unfolding* nature of the lemma.

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
|  1 | WebSearch (specific form) | "unit group of a subring as subgroup of units, u and u inverse both in subring, principal units local field" | **yes** | *verbatim:* "The group of units in `L` is `U_L := O_L^×`"; principal units `U_L^n := 1 + 𝔓_L^n`; "`K^* ⊇ O^* ⊇ U_1(K) = 1 + m`" | Crew, *Local Class Field Theory* (UF notes); W&M *Local Fields and p-adic Groups*. Confirms `𝒪_K^×` (= the user's `localUnits`) and `1 + 𝔪` (= `localUnitsOne`) are the **completely standard** objects. The unit group is `O^×`; the *defining property* is exactly "`u, u⁻¹ ∈ O`". |
|  2 | WebSearch (general / named form) | "local units cyclotomic tower 𝒪_{K_n}^× principal units Iwasawa theory Coleman map definition" | **yes** | the Coleman map is "equivariant w.r.t. the action of the Iwasawa algebra `Λ(Γ)` on local units"; `K_n = ℚ_p(ε_n)`; `U` = local units, `C` = cyclotomic units in the tower | top hit is **arXiv:2309.15692 (RJW, the project's source)**; Sharifi notes; Hida notes. Confirms "local units `U`" / `𝒰_n = 𝒪_{K_n}^×` is standard Coleman-map / Iwasawa terminology — but it is *uncontested textbook bookkeeping*, not a named theorem. |
|  3 | WebSearch (idiom / Lean convention) | "mathlib SetLike mem_carrier Iff.rfl convention membership subobject defined by carrier setOf pattern simp lemma" | **yes** | *verbatim:* "`mem_carrier` … `x ∈ p.carrier ↔ x ∈ (p : Set X) := Iff.rfl` … standard boilerplate provided by SetLike for algebraic subobjects (Submonoid, Submodule)"; "membership in a carrier set is definitionally equal … making the proof trivial" | **Decisive idiom hit.** `Mathlib.Data.SetLike.Basic` documents the `mem_*_iff := Iff.rfl` companion pattern for `Submonoid`/`Subgroup`/`Submodule` carriers. The target is a textbook instance shipped with its parent subobject. |
|  4 | ChatGPT MCP (codex) | "Is the membership criterion for `O_K^×` substantive or a definitional unfolding? Is there an abstract 'unit group of a submonoid' construction?" | **n/a** | (MCP tool not available in this environment — `ToolSearch` for `mcp__chatgpt__*` returned no matches) | Channel unavailable; **compensated** by an extra WebSearch (#3 idiom) and the direct mathlib-source reads in Phase 5 (`Submonoid.units`/`mem_units_iff` found verbatim), which answer the same questions the codex consult would: the unfolding is definitional, and the abstract construction *does* exist in mathlib. |
|  5 | Local references (`refs/PadicLFunctions/`, `.mathlib-quality/references/`) | listed both dirs | **n/a** | (the shared `refs/PadicLFunctions/` store is empty; `.mathlib-quality/references/` absent — PDFs are local-only and not in this checkout) | In-file docstring cites **RJW TeX 2474** for `localUnits`; the lemma itself is uncommented glue. Recorded n/a with reason. |
|  6 | nLab | `ncatlab.org/nlab/show/group+of+units` (WebFetch) | **partial** | defines `R× = GL₁(R)` "elements of `R` invertible under the product"; extends to monoids; the p-adic example mentions principal units `1 + p𝔸_p` in an exact sequence | nLab has the group-of-units concept (the parent of `localUnits`) but **no** abstract "unit group of a submonoid" construction and **no** membership-unfolding lemma. The categorical view (units via an equaliser) is not what this lemma is about. |
|  7 | nCatLab (categorical) | (same fetch as #6) | **n/a** | — | a `mem_X_iff := Iff.rfl` is a Lean proof-engineering artifact with no categorical content; the underlying object is commutative-algebra / number-theory, not categorical. |
|  8 | Stacks Project | "units of a ring", "local ring units", valuation-ring units | **n/a** | Stacks has units of rings and valuation rings throughout (e.g. tag 00I3, 052H) but states `u ∈ R^× ⟺ ∃ v, uv = 1`; it has **no** "`u, u⁻¹` both in subring `O`" membership-unfolding lemma packaged as a named result | Stacks is alg-geom/comm-alg; the units notion is there, the *Lean glue lemma* form is not (it is below the granularity of a Stacks tag). |
|  9 | MathOverflow / Math.SE | covered by #1/#2 result sets (`O_L^×`, principal units `1+𝔪`) | **n/a-as-search** | — | The definitions are uncontested textbook local field theory; the *lemma* (a definitional `Iff.rfl` unfolding) is far below the threshold of an MO question — no thread to resolve. |
| 10 | recent arXiv (≤5 yr) | (search #2 surfaced arXiv:2309.15692, 2310.06813, 1511.06986) | **yes (for the concept)** | modern Iwasawa/Coleman-map work uses `𝒰_n = 𝒪_{K_n}^×` and principal units identically; notation/hypotheses vary by application | confirms `𝒰_n` is recurring standard bookkeeping in the area; **none** isolates "membership of `𝒰_n` is the `u,u⁻¹∈O` conjunction" as a *result* — it is always a definitional triviality. |

### Literature summary (Phase 3)

- **Concept identified as:** the **local unit group `𝒰_n = 𝒪_{K_n}^×`** of the cyclotomic tower (RJW arXiv:2309.15692 §9, TeX 2474; Crew LCFT; Coleman; Hida; Sharifi) — standard analytic/algebraic number theory. Abstractly, it is **"the unit group of the subring `O_n`"**, i.e. the units of `ℂ_p^×` both of whose value and inverse-value lie in `O_n`. The *lemma* embodies the mathlib **`mem_X_iff := Iff.rfl` SetLike-carrier idiom** (`Mathlib.Data.SetLike.Basic`).
- **Sources agree on the standard form:** **yes** — on both prongs. (a) `𝒰_n = 𝒪_{K_n}^×` and `𝒰_{n,1} = 1+𝔪` are universally the local-units / principal-units objects (channel 1 verbatim). (b) The membership-unfolding `u ∈ 𝒪_K^× ⟺ u, u⁻¹ ∈ 𝒪_K` is **definitional, not a theorem** (channel 1 gives the definition; channel 3 documents the mathlib idiom).
- **Most general standard form (of the membership fact):** for *any* monoid `M` and *any* submonoid `S ⊆ M`, the unit group of `S` is `{u ∈ Mˣ | u ∈ S ∧ u⁻¹ ∈ S}`, and "`u ∈ S.units ↔ u ∈ S ∧ u⁻¹ ∈ S`" holds by `Iff.rfl`. This abstract form is **exactly mathlib's `Submonoid.units` / `Submonoid.mem_units_iff`** (found in Phase 5). The project's `ℂ_p`/`O_n` instance is a *specialisation* of it.
- **Generality dimensions where the literature varies:** the ambient object: a specific local/global field's ring of integers (the project's `O_n ⊆ ℂ_p`) vs. an arbitrary submonoid of an arbitrary monoid (mathlib's `Submonoid.units`). The literature uses the concrete number-theoretic instance; the maximally-general abstraction is the submonoid one — **and mathlib already has it**.
- **Disagreement with the literature:** **none.** The lemma faithfully unfolds the project's `localUnits`; the unfolding coincides exactly with mathlib's general `Submonoid.mem_units_iff`.

The search did **not** come up empty — it pinned the concept (`𝒪_K^×` local units, RJW source confirmed) and, decisively, identified that the membership-unfolding is the *definition* of "unit group of a subring", whose maximally-general form is mathlib's `Submonoid.units`/`mem_units_iff`. This drives the verdict to `NO-mathlib-has-it`.

## Phase 4 — Generality analysis

### Generality analysis — `mem_localUnits_iff`

Literature-standard / mathlib-standard form (from Phase 3 + Phase 5): the membership fact is the
**definition of the unit group of a submonoid**, captured maximally-generally by mathlib's
`Submonoid.mem_units_iff (S : Submonoid M) (x : Mˣ) : x ∈ S.units ↔ (x : M) ∈ S ∧ (x⁻¹ : Mˣ) ∈ S`.

| # | Parameter / hypothesis | Current Lean form | Literature/mathlib-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|----------------------------------|---------------------|----------------------------------|
| 1 | ambient monoid hard-coded `ℂ_[p]` | the specific field `ℂ_p` | arbitrary `[Monoid M]` | **yes — already realised upstream** | `Submonoid.units`/`mem_units_iff` is stated for any `[Monoid M]`. `ℂ_[p]` is one instance. |
| 2 | subring hard-coded `O p n` | the specific integer ring `O_n` | arbitrary `(S : Submonoid M)` | **yes — already realised upstream** | The mathlib lemma quantifies over all submonoids `S`. `O p n` is a `Subring`, hence `(O p n).toSubmonoid` is one such `S`. |
| 3 | the statement = the parent's `carrier` predicate | byte-identical to `localUnits.carrier` | (definitional) | no | By construction the RHS *is* the carrier; there is no "more general statement" of a definitional unfolding — it is fixed by the def, and that def *is* `Submonoid.units` specialised. |
| 4 | proof method `Iff.rfl` | reflexivity of definitional membership | the only possible proof (mathlib's is also `Iff.rfl`) | no | A `mem_X_iff` for a `carrier := {x | P x}` literal is `Iff.rfl` in every generality. |

### Generality verdict (Phase 4b)

**The current form is: STRICTLY NARROWER THAN STANDARD — but the more general form already exists
in mathlib.** The maximally-general statement (arbitrary monoid `M`, arbitrary submonoid `S`) is
**not a generalisation we should *add*** — it is **already present** as `Submonoid.mem_units_iff`.
The project's lemma is the `M := ℂ_[p]`, `S := (O p n).toSubmonoid` specialisation of it.
**Number of weakening opportunities found that are *not already in mathlib*: 0.** (The two
generality axes — ambient monoid, ambient submonoid — are both already maximised upstream.)
Because the general form is already in mathlib, this is a `NO-mathlib-has-it` situation, **not** a
`YES-but-generalise-first` one (there is nothing new to contribute by generalising — the general
form exists).

### Phase 4c — Modern-mathlib-idiom restatement (Bourbaki 2.0 check)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preamble → typeclass / abstract parameter? | **already done upstream** | `Submonoid.mem_units_iff` quantifies over `[Monoid M]` and `(S : Submonoid M)` | n/a — the abstraction exists; the project just hasn't used it |
|  2 | sequences/metric → filters/topological? | no | — | purely algebraic definitional unfolding; no metric/sequence content. |
|  3 | construct an object → universal-property class? | no | — | nothing constructed; it restates `∈ carrier`. |
|  4 | set-with-closure-predicate → bundled substructure? | **already done by the parent, but re-implemented** | `localUnits p n` should be `(O p n).toSubmonoid.units` (mathlib's bundled construction) instead of a hand-rolled `Subgroup` carrier | reuse of all `Submonoid.units` API: `units_mono`, `ofUnits_units_gci`, `Submonoid.mem_units_of_val_mem_inv_val_mem`, etc. |
|  5 | vector-space/field-specific → weaken typeclasses? | **already done upstream** | the field `ℂ_p` → arbitrary `[Monoid M]` (mathlib's lemma) | n/a — exists |
|  6 | 1-categorical → higher-categorical? | no | — | no categorification target. |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary structure? | no (for this lemma) | — | the `n` indexes the tower layer via `O p n`; it is not a generality axis of the *membership* fact. |

**Modern-idiom verdict (Phase 4c): no new modernisation to contribute** — the modern idiom (a
bundled `Submonoid.units` subgroup with a `mem_units_iff := Iff.rfl` companion) **already exists in
mathlib**, and the project simply re-implements it by hand. The actionable consequence is a
*project-side refactor* (`localUnits p n := (O p n).toSubmonoid.units`; delete `mem_localUnits_iff`
in favour of `Submonoid.mem_units_iff`), **not** a mathlib contribution. One-line reason this is not
a modernisation *move for mathlib*: **mathlib is already in the modern form; the divergence is on
the project side and is fixed by *using* mathlib, which is precisely the `NO-mathlib-has-it`
refactor.**

## Phase 4.5 — Diamond / defeq risk

**n/a — declaration kind is `lemma`** (a `Prop`-valued `Iff`, proved `Iff.rfl`). Lemmas introduce
no definitional equalities on algebraic structures and no typeclass-search paths, so the six-row
risk table is skipped. (For completeness: the lemma carries **no** `@[simp]`/`@[reducible]`/instance
attribute — it is a bare `lemma`. The mathlib analog `Submonoid.mem_units_iff` is *also* a plain
lemma — note it is *not* `@[simp]`-tagged upstream — so adopting it introduces no new simp behaviour.)

## Phase 5 — Mathlib five-method search

Searched on (a) the user's form (`localUnits` membership; `u, u⁻¹ ∈ O p n`); (b) the
maximally-general form (unit group of an arbitrary submonoid / subring; valuation-subring unit
group); and (c) the **idiom** (mathlib's `mem_X_iff := Iff.rfl` companions for `SetLike` carriers).

### Mathlib search-status: `PadicLFunctions.Coleman.mem_localUnits_iff`

| Method | Query | Result |
|---|---|---|
| **[A] Lean-Finder (AI/NL)** | "membership in unit group of a subring iff element and its inverse lie in the subring", "units of valuation integers" | **hit** — surfaces `Submonoid.units` / `Submonoid.mem_units_iff` and `ValuationSubring.unitGroup` / `mem_unitGroup_iff` as the canonical "unit group of a subobject" API. |
| **[B] Loogle (type pattern)** | `_ ∈ _ ↔ (_ ∈ _ ∧ _ ∈ _)` over `Subgroup Mˣ`; `mem_*_iff` with a `u` / `u⁻¹` conjunction; grep proxy `mem_units_iff` over `Mathlib/` | **hit** — `Submonoid.mem_units_iff (S : Submonoid M) (x : Mˣ) : x ∈ S.units ↔ ((x : M) ∈ S ∧ ((x⁻¹ : Mˣ) : M) ∈ S) := Iff.rfl` (`Algebra/Group/Submonoid/Units.lean:101`). **Byte-for-byte the user's RHS.** |
| **[C] LeanSearch (NL)** | "the unit group of a submonoid as a subgroup of the units of the monoid", "a unit lies in the unit group of a subring iff it and its inverse are in the subring" | **hit** — returns `Submonoid.units` and the `Submonoid.units`/`Subgroup.ofUnits` Galois coinsertion as the matching construction. |
| **[D] Grep mathlib src** | `grep -rni "localUnits\|local_units" Mathlib/` → **0**; `Submonoid.units\|mem_units_iff` → **hit (Units.lean:49/101)**; `ValuationSubring.unitGroup\|mem_unitGroup_iff` → **hit (ValuationSubring.lean:492/496)** | **hit.** The project's *name* `localUnits` is absent (it is the project's own), but the *construction and its mem-lemma* are present **twice**: the general `Submonoid.units`/`mem_units_iff`, and the valuation-specific `ValuationSubring.unitGroup`/`mem_unitGroup_iff`. |
| **[E] Name pattern (idiom)** | `mem_localUnits_iff`; the idiom `(theorem\|lemma) mem_[A-Za-z]+_iff … := Iff.rfl`; `mem_units_iff`, `mem_unitGroup_iff` | `localUnits`: project-only. The **idiom** `mem_*_iff` is abundant in mathlib (**794** `mem_X_iff` lemmas; the `:= Iff.rfl` SetLike-carrier sub-pattern documented in `Mathlib.Data.SetLike.Basic`). The specific `mem_units_iff`/`mem_unitGroup_iff` exist and are the targets. |

**Searched for both forms:** yes — the user's `localUnits`-membership form, the maximally-general
submonoid form, the valuation-subring form, *and* the mathlib idiom. **Mathlib has the exact
content** as `Submonoid.mem_units_iff` (general) — and additionally `ValuationSubring.mem_unitGroup_iff`
(a valuation-tinted variant whose RHS is `A.valuation x = 1`, equivalent for valuation rings).

**Concluded:** **found in mathlib as `Submonoid.mem_units_iff`** (`Mathlib/Algebra/Group/Submonoid/Units.lean:101`),
the companion to `def Submonoid.units` (`:49`). The statement is **identical** (same `Iff.rfl`, same
RHS predicate `(x : M) ∈ S ∧ (x⁻¹ : M) ∈ S`) at **strictly greater generality** (any `[Monoid M]`,
any `Submonoid S`). The user's `mem_localUnits_iff` is the `M := ℂ_[p]`, `S := (O p n).toSubmonoid`
specialisation. The re-aim target (the parent def) is **also** in mathlib (`Submonoid.units`), so this
is `NO-mathlib-has-it`, not `NO-composable`.

**Derivation that the user's form follows from the mathlib lemma (≤1 line):**
```lean
example {n : ℕ} {u : ℂ_[p]ˣ} :
    u ∈ localUnits p n ↔ (u : ℂ_[p]) ∈ O p n ∧ ((u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ∈ O p n :=
  -- localUnits p n is defeq to (O p n).toSubmonoid.units; Submonoid.mem_units_iff is Iff.rfl;
  -- Subring.mem_toSubmonoid (Iff.rfl) bridges `∈ (O p n).toSubmonoid` and `∈ O p n`.
  (O p n).toSubmonoid.mem_units_iff u
```
(If `localUnits` is left defined by its hand-rolled carrier, the two `Iff.rfl`s compose; if `localUnits`
is refactored to `(O p n).toSubmonoid.units`, the lemma *becomes* `Submonoid.mem_units_iff` outright
and is deleted.)

## Phase 6 — Composition check (+ call-sites signal)

### Call sites — `mem_localUnits_iff`

Grep `mem_localUnits_iff` over `projects/`, excluding the declaring line (`LocalUnits.lean:55`):

- **Internal use count: 5** (within the project, excluding the declaring file/line; all are uses of the lemma in tactic/term proofs).
- **External-to-file callers: 3 files** (`Iwasawa/CyclotomicUnits.lean`, `Iwasawa/ResidueField.lean`, `IwasawaProof/Generators.lean`).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| `Iwasawa/CyclotomicUnits.lean:159` | `rw [mem_localUnits_iff]` — inside `globalUnits_le_localUnits`, then `refine ⟨?_, ?_⟩` to supply `u ∈ O_n` and `u⁻¹ ∈ O_n`. |
| `Iwasawa/ResidueField.lean:164` | `((mem_localUnits_iff p).2 ⟨u.mem (n+1), …inv_mem…⟩)` — builds `𝒰_{n+1}`-membership to feed `norm_eq_one_of_mem_localUnits`. |
| `Iwasawa/ResidueField.lean:282` | `((mem_localUnits_iff p).2 ⟨u.mem n, by rw [Units.val_inv_eq_inv_val]; exact u.inv_mem n⟩)` — same construction at level `n`. |
| `Iwasawa/ResidueField.lean:344` | `(mem_localUnits_iff p).2 ⟨w.mem n, …inv_mem…⟩` — inside a `localUnitsOne` membership proof. |
| `IwasawaProof/Generators.lean:1024` | `(mem_localUnits_iff p).2 ⟨(galNCU p a u).mem n, …inv_mem…⟩` — `σ_a u_n ∈ 𝒰_n` from the `NormCompatUnits` fields. |

Inline-derivation grep (was the `u,u⁻¹∈O` conjunction re-spelled elsewhere without `mem_localUnits_iff`?):
**(none material)** — every `∈ localUnits` construction/destruction routes through this lemma. (Other
`∈ localUnits` facts are obtained via the `Subgroup` API — `mul_mem`, `inv_mem` — on already-established
memberships, which is correct.)

**What the call-sites pattern tells you.** K = 5 internal uses across 3 files, all the *same* two
gestures: `rw [mem_localUnits_iff]` to unfold the goal, and `(mem_localUnits_iff p).2 ⟨val, inv_val⟩`
to construct membership. This is a genuinely-used *local* convenience — **not dead code** (K = 5 ≫ 1).
But K ≥ 3 here does **not** argue for mathlib-worthiness: it argues that the project leans on a
membership lemma it *re-implemented*, when **the identical mathlib lemma `Submonoid.mem_units_iff`
(and its helper `Submonoid.mem_units_of_val_mem_inv_val_mem`) would serve every one of these 5 sites**.
The call-site evidence thus *strengthens* the `NO-mathlib-has-it` refactor: there are 5 concrete sites
to redirect to the existing mathlib API.

### Composition check (Phase 6)

Can `mem_localUnits_iff` be **derived** from mathlib? **It is not merely composable — mathlib has the
lemma outright.** Per Phase 5, `Submonoid.mem_units_iff (O p n).toSubmonoid u` is the user's exact
statement (modulo the `Iff.rfl` coercion `Subring.mem_toSubmonoid`). This is **`NO-mathlib-has-it`**,
the bucket above `NO-composable-from-mathlib`: there is a *single existing mathlib decl* (not just
building blocks) that *is* the lemma. Recorded for completeness:

- **Attempt 1 — cite the mathlib lemma directly.** `(O p n).toSubmonoid.mem_units_iff u` has type
  `u ∈ (O p n).toSubmonoid.units ↔ (u : ℂ_[p]) ∈ (O p n).toSubmonoid ∧ ((u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ∈ (O p n).toSubmonoid`.
  Since `localUnits p n` is defeq to `(O p n).toSubmonoid.units` (same carrier) and `∈ (O p n).toSubmonoid`
  is `Iff.rfl`-equal to `∈ O p n`, this **is** the user's statement. **Result: succeeds (0–1 calls).**

**Conclusion: the lemma is in mathlib (NO-mathlib-has-it).** Mathlib's `Submonoid.mem_units_iff`
is the exact, more-general statement; the user's form is a definitional specialisation. (This is a
*stronger* finding than COMPOSABLE — we are not assembling from primitives, we are citing one decl.)

## Phase 7 — Verdict synthesis (gate)

### Verdict: `PadicLFunctions.Coleman.mem_localUnits_iff`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- **Literature search (Phase 3):** the concept is the standard local-unit group `𝒪_{K_n}^×` (RJW arXiv:2309.15692 §9, confirmed; Crew LCFT verbatim "`U_L := O_L^×`"); abstractly "the unit group of the subring `O_n`", whose maximally-general form is "unit group of a submonoid". The membership-unfolding is **definitional**, and the `mem_X_iff := Iff.rfl` form is the documented `Mathlib.Data.SetLike.Basic` idiom.
- **Generality analysis (Phase 4):** STRICTLY NARROWER than the maximally-general form — **but the general form already exists in mathlib** (Phase 4b), so this is `NO-mathlib-has-it`, not `YES-but-generalise-first`. Phase 4c: no *new* modernisation to contribute; the modern bundled form (`Submonoid.units` + `mem_units_iff`) is already upstream, and the project merely re-implements it.
- **Mathlib search (Phase 5):** **found in mathlib as `Submonoid.mem_units_iff`** (`Mathlib/Algebra/Group/Submonoid/Units.lean:101`), companion to `def Submonoid.units` (`:49`) — identical statement, strictly more general. (Plus the valuation-specific `ValuationSubring.mem_unitGroup_iff`, `ValuationSubring.lean:496.`) The user's form is the `M := ℂ_[p]`, `S := (O p n).toSubmonoid` specialisation.
- **Composition check (Phase 6):** beyond composable — a single mathlib decl *is* the lemma. Call-sites: K = 5 internal uses across 3 files (`CyclotomicUnits.lean`, `ResidueField.lean` ×3, `Generators.lean`), all redirectable to `Submonoid.mem_units_iff` / `Submonoid.mem_units_of_val_mem_inv_val_mem`.

**Rationale.**
`mem_localUnits_iff` carries **no mathematical content that mathlib lacks**. Its body is `Iff.rfl`
and its right-hand side is byte-for-byte the `carrier` predicate of `def localUnits`
(`LocalUnits.lean:39`), which is the unit group of the subring `O p n` — i.e. `{u ∈ ℂ_p^× | u ∈ O_n ∧
u⁻¹ ∈ O_n}`. Mathlib already provides this construction in full generality as
`Submonoid.units (S : Submonoid M) : Subgroup Mˣ` (`Algebra/Group/Submonoid/Units.lean:49`), together
with **the very lemma at hand**: `Submonoid.mem_units_iff (S : Submonoid M) (x : Mˣ) : x ∈ S.units ↔
(x : M) ∈ S ∧ (x⁻¹ : Mˣ) ∈ S := Iff.rfl` (`:101`). The project's `localUnits p n` is definitionally
`(O p n).toSubmonoid.units` (`O p n` is a `Subring`, hence a `Submonoid` of `ℂ_p`; the carriers
coincide), and `mem_localUnits_iff` is `Submonoid.mem_units_iff (O p n).toSubmonoid u` bridged only by
the definitional coercion `Subring.mem_toSubmonoid` (`Subring/Defs.lean:405`, itself `Iff.rfl`). So the
user's statement follows from the existing mathlib lemma in **0–1 lines** — the signature of
`NO-mathlib-has-it`.

This is a **stronger** NO than the sibling `PadicMeasure.mem_zetaIdeal_iff` (which was
`NO-composable-from-mathlib` precisely because its parent `zetaIdeal` is *absent* from mathlib, leaving
no decl to cite). Here, not only the lemma but the **parent construction** `Submonoid.units` is
upstream — so we can name the exact mathlib lemma the user's form specialises from, and the verdict is
`NO-mathlib-has-it`. The genuinely-actionable conclusion is a project-side refactor: redefine
`localUnits p n := (O p n).toSubmonoid.units` (inheriting all of mathlib's `Submonoid.units` API —
`units_mono`, `Submonoid.mem_units_of_val_mem_inv_val_mem`, `val_mem_of_mem_units`, the Galois
coinsertion with `Subgroup.ofUnits`), and delete `mem_localUnits_iff` in favour of
`Submonoid.mem_units_iff`, redirecting its 5 call sites. (The `Subgroup`-instance proofs `mul_mem'`,
`one_mem'`, `inv_mem'` currently hand-proved in `localUnits` are then free.) Note the mathematical
*object* `𝒰_n` is of course kept — only its hand-rolled membership lemma is redundant.

**WHY not (REQUIRED — refactor-actionable detail).**
Mathlib **already has this lemma**, more generally. There is therefore nothing to contribute to
mathlib; the action is to *use* the existing mathlib decl and delete the local re-implementation.
Concretely:

  - **Existing mathlib decl:** `Submonoid.mem_units_iff`
  - **Located at:** `Mathlib/Algebra/Group/Submonoid/Units.lean:101`
    ```lean
    lemma Submonoid.mem_units_iff (S : Submonoid M) (x : Mˣ) :
        x ∈ S.units ↔ ((x : M) ∈ S ∧ ((x⁻¹ : Mˣ) : M) ∈ S) := Iff.rfl
    ```
    (companion to `def Submonoid.units` at `:49`; constructor helper
    `Submonoid.mem_units_of_val_mem_inv_val_mem` at `:105`, destructors
    `val_mem_of_mem_units`/`inv_val_mem_of_mem_units` at `:109`/`:112`).
  - **Our form follows in ≤1 line:**
    ```lean
    example {n : ℕ} {u : ℂ_[p]ˣ} :
        u ∈ localUnits p n ↔ (u : ℂ_[p]) ∈ O p n ∧ ((u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ∈ O p n :=
      (O p n).toSubmonoid.mem_units_iff u   -- defeq via Subring.mem_toSubmonoid
    ```

**Call sites in our project (from Phase 6.0): K = 5** —
`Iwasawa/CyclotomicUnits.lean:159`, `Iwasawa/ResidueField.lean:164`, `:282`, `:344`,
`IwasawaProof/Generators.lean:1024`.

**Refactor plan (refactor-actionable, two stages):**
  1. **Preferred — redefine the parent, delete the lemma.** Replace
     `def localUnits (n : ℕ) : Subgroup ℂ_[p]ˣ := …carrier…` with
     `def localUnits (n : ℕ) : Subgroup ℂ_[p]ˣ := (O p n).toSubmonoid.units` (the three `Subgroup`
     field-proofs `mul_mem'`/`one_mem'`/`inv_mem'` are then provided by `Submonoid.units` for free).
     Delete `mem_localUnits_iff`. At each of the 5 call sites:
       - **`rw [mem_localUnits_iff]`** (`CyclotomicUnits.lean:159`) → `rw [Submonoid.mem_units_iff]`
         (or `show (u:ℂ_[p]) ∈ O p n ∧ …`; the goal is defeq).
       - **`(mem_localUnits_iff p).2 ⟨h₁, h₂⟩`** (`ResidueField.lean:164/282/344`,
         `Generators.lean:1024`) → `(O p n).toSubmonoid.mem_units_of_val_mem_inv_val_mem h₁ h₂`
         (or `(Submonoid.mem_units_iff _ _).2 ⟨h₁, h₂⟩`). The `h₁ = …mem`, `h₂ = …inv_mem` arguments
         are unchanged; only the head lemma name changes. Verify the `Subring.mem_toSubmonoid` coercion
         resolves automatically (it is `Iff.rfl`, so `exact`/`refine` accept it; a stray `simp only
         [Subring.mem_toSubmonoid]` is the fallback if elaboration needs the nudge).
  2. **Minimal — keep `localUnits` as-is, retire only the lemma.** If touching the parent `def` is
     out of scope, keep `localUnits` by its carrier but **replace the body of `mem_localUnits_iff`'s
     consumers** with `Submonoid.mem_units_iff`-style calls is not possible without the defeq; in that
     case simply **leave `mem_localUnits_iff` as a one-line local alias documented as "= `Submonoid.mem_units_iff`
     for `(O p n).toSubmonoid.units`"**. This is the *acceptable* fallback (the lemma is then a thin,
     correctly-attributed local wrapper), but stage 1 is preferred because it removes the duplicated
     construction entirely.

**Next action:** **do not open a mathlib PR** (mathlib has the lemma). Refactor the project to use
`Submonoid.units` / `Submonoid.mem_units_iff`: redefine `localUnits p n := (O p n).toSubmonoid.units`,
delete `mem_localUnits_iff`, and redirect the 5 call sites to `Submonoid.mem_units_iff` /
`Submonoid.mem_units_of_val_mem_inv_val_mem` (argument-for-argument identical). Consider doing the
same for the sibling `localUnitsOne` against mathlib's `ValuationSubring.principalUnitGroup` *only if*
`O p n` can be exhibited as a `ValuationSubring` — otherwise `localUnitsOne` stays project-local (its
`‖u−1‖<1` carrier is not the generic submonoid-units shape).

### Verdict gate self-check
- Bucket is `NO-mathlib-has-it` and **Phase 5 concluded "found in mathlib as `Submonoid.mem_units_iff`"** ✓ (the gate's requirement for this bucket — the decl is cited by full qualified name with file:line).
- The user's form follows in ≤1 line, with the `example := (O p n).toSubmonoid.mem_units_iff u` derivation shown ✓.
- Phase 6.0 call-sites table present (K = 5, all 5 rows, inline-derivation grep) ✓.
- For the NO verdict, the WHY paragraph names the K = 5 sites and the concrete redirect at refactor-actionable detail (per-site head-lemma replacement) ✓.
- Not `YES-add-as-is`/`YES-but-generalise-first`: Phase 4b found the user's form strictly narrower, but the **more general form already exists in mathlib** (Phase 5), so YES is forbidden — there is nothing new to add or generalise ✓.
- Not `NO-composable-from-mathlib`: Phase 5 found a *single existing decl* that *is* the lemma (stronger than "building blocks compose"), so the correct bucket is `NO-mathlib-has-it` ✓.
- Not `BORDERLINE`: the lemma's verdict is unambiguous (mathlib has it); the only judgment call (refactor the parent def?) is a clear yes and is spelled out, not deferred ✓.

## Phase 8 — Report (this document)

**Five-bucket verdict (final): `NO-mathlib-has-it`**

- **What it is:** the `mem_X_iff := Iff.rfl` companion to `def localUnits p n` (`𝒰_n = 𝒪_{K_n}^×`), unfolding membership to "`u` and `u⁻¹` both lie in the integer ring `O_n`".
- **Why NO-mathlib-has-it:** mathlib has the **identical, more general** lemma `Submonoid.mem_units_iff` (`Algebra/Group/Submonoid/Units.lean:101`), companion to `def Submonoid.units` (`:49`). `localUnits p n` is defeq to `(O p n).toSubmonoid.units`, and the user's lemma is its `M := ℂ_[p]`, `S := (O p n).toSubmonoid` specialisation (bridged by the `Iff.rfl` coercion `Subring.mem_toSubmonoid`). The user's form follows in 0–1 lines.
- **Why not NO-composable (cf. the `mem_zetaIdeal_iff` sibling):** there, the parent `zetaIdeal` was absent from mathlib so only "building blocks" existed → NO-composable. Here the parent construction `Submonoid.units` **is** upstream with its own `mem_units_iff`, so a single decl can be cited → the stronger NO-mathlib-has-it.
- **Why not a YES:** the maximally-general form (unit group of an arbitrary submonoid) is already in mathlib; there is nothing new to add or generalise.
- **Risk:** Phase 4.5 n/a (a `lemma`, not a `def`).
- **Recommended action:** refactor the project — redefine `localUnits p n := (O p n).toSubmonoid.units`, delete `mem_localUnits_iff`, redirect its 5 call sites to `Submonoid.mem_units_iff` / `Submonoid.mem_units_of_val_mem_inv_val_mem`. No mathlib PR.

---

## Next step

Delete `PadicLFunctions.Coleman.mem_localUnits_iff` from the project and use mathlib's
`Submonoid.mem_units_iff` (`Mathlib/Algebra/Group/Submonoid/Units.lean:101`) instead. Preferably
also redefine the parent `def localUnits p n := (O p n).toSubmonoid.units` so it inherits mathlib's
`Submonoid.units` API and the three subgroup-closure proofs become free. Redirect the 5 call sites
(`CyclotomicUnits.lean:159`, `ResidueField.lean:164/282/344`, `Generators.lean:1024`) to
`Submonoid.mem_units_iff` / `Submonoid.mem_units_of_val_mem_inv_val_mem` — argument-for-argument
identical. Do **not** open a mathlib PR: the lemma already exists upstream, more generally.
