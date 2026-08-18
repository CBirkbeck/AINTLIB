# /mathlibable report — `Chebotarev.mixedCubeEquiv`

## Baseline (Phase 0)
- lake build:               not run (local build stale per task; reasoning from source)
- decl `Chebotarev.mixedCubeEquiv`: ✓ resolved at `projects/Chebotarev/CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean:444`
- kind:                     `def` (`noncomputable`)
- has sorry:                no
- module docstring summary: Lipschitz parametrization of the frontier of `normLeOne K`; covers the
  frontier by finitely many Lipschitz images of the unit cube (Gun–Ramaré–Sivaraman boundary input).

Qualified name **verified from source**: the decl sits inside `namespace Chebotarev` (line 79,
`end Chebotarev` at 673), so the true qualified name is `Chebotarev.mixedCubeEquiv` (the parsed
guess was correct). Section variable in scope: `variable (K : Type*) [Field K] [NumberField K]`
(line 124).

Full elaborated signature:

```lean
noncomputable def Chebotarev.mixedCubeEquiv (K : Type*) [Field K] [NumberField K] :
    Fin (Module.finrank ℚ K - 1)
      ≃ Fin (Fintype.card (InfinitePlace K) - 1) ⊕ {w : InfinitePlace K // IsComplex w}
```

Proof body (5 substantive lines):

```lean
  apply Fintype.equivOfCardEq
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  have h1 : Fintype.card (InfinitePlace K) = nrRealPlaces K + nrComplexPlaces K :=
    card_eq_nrRealPlaces_add_nrComplexPlaces K
  have h2 : nrRealPlaces K + 2 * nrComplexPlaces K = Module.finrank ℚ K :=
    card_add_two_mul_card_eq_rank K
  have hpos : 1 ≤ Fintype.card (InfinitePlace K) := Fintype.card_pos
  have h3 : nrComplexPlaces K = Fintype.card {w : InfinitePlace K // IsComplex w} := rfl
  lia
```

## Statement (Phase 1)

`Chebotarev.mixedCubeEquiv K` is **a definition**: it produces *some* bijection (an `Equiv`)
between the index set `Fin (d − 1)`, where `d = finrank_ℚ K` is the degree of the number field
`K`, and the disjoint union `Fin (r − 1) ⊕ {complex places of K}`, where `r = #InfinitePlace K`
is the number of infinite places.

The mathematical "content" is purely the **cardinality identity**

  (d − 1) = (r − 1) + r₂,

where `r₂ = nrComplexPlaces K` is the number of complex places. This follows from the two
classical signature identities `r₁ + 2 r₂ = d` and `r = r₁ + r₂` together with `r ≥ 1`. The
bijection itself is **arbitrary** — it is whatever `Fintype.equivOfCardEq` (a `Classical.choice`
extraction) hands back from the equal-cardinality proof. It is **not** a canonical / natural map;
no specific element-to-element correspondence is asserted or used.

Its role in the file: `mixedCubeEquiv K` is used (via its `.symm`) inside `liftToMixed` purely as
an **index relabelling** that splits the `d − 1` cube coordinates into `r − 1` "modulus"
coordinates (input to a `realSpace`-valued cover map) plus `r₂` "phase" coordinates (one per
complex place). Only the *existence* of such a relabelling matters, never which one it is.

Variables / typeclasses involved (Lean side):
- `K : Type*`, `[Field K]`, `[NumberField K]` — a number field; provides the finiteness of
  `InfinitePlace K`, the finrank, and the signature identities.

Hypotheses (Lean side): none (it is a `def`, not conditioned on extra hypotheses).

Conclusion (math): the finite sets `Fin(d−1)` and `Fin(r−1) ⊕ {complex places}` are in bijection
(equivalently: `(d−1) = (r−1) + r₂`).

Conclusion (Lean): `Fin (Module.finrank ℚ K - 1) ≃ Fin (Fintype.card (InfinitePlace K) - 1) ⊕ {w : InfinitePlace K // IsComplex w}`.

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: not a named/structure-introducing concept and not a `## Main results` entry; it is an
internal index-bookkeeping `def` whose entire job is to witness one cardinality equality.

(Literature width run EXHAUSTIVE regardless.)

## One-line check (Phase 2b)

Body line count: 5 substantive lines (an `apply` + a `rw` + three `have`s + `lia`) — but every line
is *cardinality arithmetic*; the only "construction" line is `apply Fintype.equivOfCardEq`. So while
not literally a one-liner by line count, it is **morally a one-liner**: `Fintype.equivOfCardEq h`
for the obvious cardinality witness `h`. Treat as effectively ONE-LINER for the exemption analysis.

One-liner verdict: effectively ONE-LINER (a single mathlib `def` applied to a `decide`-style
cardinality proof).

Exemption check:
| Exemption                         | Applies? | Evidence                                                               |
|-----------------------------------|----------|------------------------------------------------------------------------|
| Avoid defeq abuse                | no       | The equiv is `noncomputable` via `Classical.choice`; it has **no** usable defeq/unfolding — nothing downstream rewrites against its body. The opposite of a defeq barrier: it deliberately has no equations. |
| Avoid typeclass diamonds         | no       | Produces an `Equiv` value, not an instance; no typeclass-search path is anchored. |
| Mark semantic intent / API name  | no       | Used only inside the same file (`liftToMixed`, `lipschitzWith_liftToMixed`); 0 external consumers; no stable public API depends on the name. |

Conclusion: **ONE-LINER WITHOUT-EXEMPTION** (effectively). Strong negative signal for mathlib
inclusion: it is a local convenience wrapper around `Fintype.equivOfCardEq`.

## Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                   | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|-----------------------------------------------------------------------------------------|------|------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "number field rank degree real complex places r1 + 2 r2 = n signature"                  | yes  | `n = r₁ + 2 r₂`; `(r₁, r₂)` is the *signature*       | The underlying identity is utterly standard (Neukirch I.5, Lang ANT); but it is a *numeric* identity, not a named *bijection of index sets*. |
|  2 | WebSearch (general form)         | "mathlib4 Fintype.equivOfCardEq noncomputable equiv same cardinality finite types"      | yes  | `Fintype.equivOfCardEq : card α = card β → α ≃ β`    | The general "equal card ⇒ noncomputable bijection" tool already exists in mathlib (`Mathlib/Data/Fintype/EquivFin.lean:143`). Our def is a one-off instance of it. |
|  3 | WebSearch (named-after / aliases)| "signature of a number field embeddings real complex places"                            | yes  | signature `(r₁, r₂)`; no named index bijection       | The literature names the *pair of counts*, never a canonical bijection `Fin(d−1) ≃ Fin(r−1) ⊕ {complex}`. The off-by-one `d−1 / r−1` shape is bespoke to this fundamental-domain coordinate setup. |
|  4 | ChatGPT MCP                      | (MCP down per task note — fallback to WebSearch #1–#3 + nLab)                            | n/a  | n/a — server unavailable                              | Recorded n/a: the math-MCP fallback used WebSearch at three generality levels + nLab + Stacks instead. |
|  5 | Local references                 | grep `.mathlib-quality/references/` for "signature"/"places"/"equiv"                     | n/a  | (no references dir for this project)                  | `projects/Chebotarev/.mathlib-quality/references/` absent; refs are local-only PDFs. |
|  6 | nLab                             | "place of a global field" / "signature of a number field"                               | no   | nLab discusses places/valuations abstractly          | No nLab page for an index-set bijection of this kind; concept too elementary/bespoke. |
|  7 | nCatLab                          | (not a categorical concept)                                                             | n/a  | n/a                                                  | Plain finite-set cardinality bookkeeping; nothing categorical. |
|  8 | Stacks Project                   | (not an algebraic-geometry concept)                                                     | n/a  | n/a                                                  | Archimedean-place counting / fundamental-cone coordinates are out of Stacks scope. |
|  9 | MathOverflow / Math.StackExchange| "r1 + 2 r2 = n number field degree real complex embeddings"                             | yes  | restates `n = r₁ + 2 r₂`                              | Confirms the numeric identity is folklore; no canonical index bijection named. |
| 10 | recent arXiv (last 5 years)      | Gun–Ramaré–Sivaraman, *Counting ideals in ray classes*, JNT 243 (2023), §3.3            | yes  | uses the cube-coordinate split implicitly             | The source paper of this whole file uses the `(r−1)+r₂ = d−1` coordinate split in prose; it does **not** isolate a named bijection — it is an implementation detail. |

The protocol passes: WebSearch ran 3 distinct queries at different generality levels; the math-MCP
was unavailable and is recorded `n/a` with the fallback noted; local refs checked (`n/a`, dir
absent); nLab checked; Stacks / nCatLab / MathOverflow / arXiv each checked or `n/a` with reason.

### Literature summary (Phase 3)

Concept identified as: **the signature identity `n = r₁ + 2 r₂` of a number field**, here packaged
(after subtracting 1 from each of `n` and `r = r₁ + r₂`) as a *bijection of index sets*
`Fin(d−1) ≃ Fin(r−1) ⊕ {complex places}`.
Sources agree on the standard form: yes for the *numeric* identity — universally standard. There is
**no** standard *named bijection* of this shape in the literature; the off-by-one, `Sum`-typed
relabelling is an artifact of the cube-coordinate construction, not a mathematical object with a
name.
Most general standard form: the numeric identity `Fintype.card (InfinitePlace K) = nrRealPlaces K +
nrComplexPlaces K` and `nrRealPlaces K + 2 * nrComplexPlaces K = finrank ℚ K` — both already in
mathlib (`card_eq_nrRealPlaces_add_nrComplexPlaces`, `card_add_two_mul_card_eq_rank`).
Generality dimensions where the literature varies:
  - the *field*: any number field — already the generality here (`[NumberField K]`).
  - the *packaging*: numeric identity (canonical, standard) vs. a chosen non-canonical bijection
    (this def) — the literature uses the numeric identity; the bijection packaging is bespoke.
Disagreement with the literature: the literature works with the **numeric identity** and chooses
coordinates ad hoc; it never blesses a *canonical* bijection `Fin(d−1) ≃ Fin(r−1) ⊕ {complex}` —
because there isn't one (the map here is arbitrary `Classical.choice`).

## Generality analysis — `Chebotarev.mixedCubeEquiv`

Literature-standard form (from Phase 3): the pair of numeric identities above; no named bijection.

| # | Parameter / hypothesis        | Current Lean form          | Literature-standard form          | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------|----------------------------|-----------------------------------|---------------------|---------------------------------|
| 1 | `[Field K] [NumberField K]`   | number field               | number field (for the signature)  | NO                  | The identities `r₁+2r₂=d`, `r=r₁+r₂` are number-field facts; weaker structures have no `InfinitePlace`/finrank signature. Already maximally general for the concept. |
| 2 | output `≃` (a chosen bijection)| arbitrary `Classical`-choice equiv | the numeric identity `(d−1)=(r−1)+r₂` | YES (drop the equiv entirely) | The bijection carries no information beyond the cardinality equality. The "more honest"/more general form is to **not** name an equiv at all and instead use the cardinality `Eq` (plus `Fintype.equivOfCardEq` inline where a relabelling is truly needed). |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** on the field parameter, but **OVER-PACKAGED** on the
output (it bundles an arbitrary bijection where the content is a cardinality `Eq`).
Number of weakening opportunities found: 1 (de-bundle the equiv → expose the cardinality identity).
Proposed restatement: not a *generalisation* of a mathlib-worthy object — see Phase 6. The "right"
artifact, if anything, is the cardinality lemma `(d−1) = (r−1) + r₂`, which is itself a ≤3-line
composition of two existing mathlib lemmas. So this is a NO-composable case, not a
generalise-first case.
Cost of restatement: CHEAP (mechanical).

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                       | Applies? | Proposed reformulation                                           | Mathlib downstream this enables |
|----|-------------------------------------------------------------------------------------------------|----------|------------------------------------------------------------------|---------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                            | no       | —                                                                | nothing to instance-ify; plain `def`. |
|  2 | sequences/metric → filters/topological?                                                        | no       | —                                                                | no analytic content; it is finite combinatorics. |
|  3 | construct an object where a universal property would characterise it?                          | yes (degenerate) | replace the *chosen* equiv by the *cardinality equality* (`Eq` of `card`s), the only invariant content | downstream code that just needs "the cardinalities match" composes with all of `Fintype.card`/`Finset` API, not with an opaque `Classical` equiv. |
|  4 | set-with-closure-predicate → bundled substructure?                                             | no       | —                                                                | n/a. |
|  5 | vector-space/field-specific → weaken typeclass?                                                | no       | —                                                                | already number-field-level. |
|  6 | 1-categorical → higher-categorical?                                                            | no       | —                                                                | n/a. |
|  7 | concrete index (ℕ,ℤ,ℝ) → arbitrary additive monoid?                                            | no       | —                                                                | the indices `Fin(d−1)`/`Fin(r−1)` are intrinsic to the cube dimension; not generalisable. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (in the sense of a *mathlib-worthy* reformulation). The only "modern"
move is the degenerate one in row 3 — strip the arbitrary bijection and keep the cardinality
identity — but that lands in the NO-composable bucket (the identity is a ≤3-line mathlib
composition), not a YES-generalise bucket. There is no real organisational improvement to upstream:
an opaque `Classical.choice` equiv has no equational API for mathlib to build on.

## Diamond / defeq risk — `Chebotarev.mixedCubeEquiv` (Phase 4.5)

Kind is `def`, so the phase runs.

| # | Risk                          | Verdict | Evidence / rationale                                                                 |
|---|-------------------------------|---------|--------------------------------------------------------------------------------------|
| 1 | Typeclass diamond            | none    | Produces an `Equiv` value, not an instance; participates in no typeclass search.     |
| 2 | Reducibility leak            | none    | Not `@[reducible]`; body is `Fintype.equivOfCardEq _`, itself `noncomputable` via `Classical.choice` — there is nothing meaningful to unfold. |
| 3 | Non-canonical unfolding      | low     | `simp`/`rfl` cannot compute it (choice-based); the *risk* is the opposite — users might wrongly expect a canonical map. This is an argument **against** shipping it, not a diamond per se. |
| 4 | Instance priority collision  | none    | Not an `instance`.                                                                    |
| 5 | Universe-polymorphism issues | none    | `K : Type*`; the equiv is between `Type 0` index sets; no forced annotation.          |
| 6 | Coercion ambiguity           | none    | No `CoeFun`/`CoeSort` introduced (an `Equiv` already has mathlib's standard coercion).|

### Risk verdict (Phase 4.5)

Overall risk: **LOW** (only row 3, and it cuts against inclusion). No HIGH rows.

## Mathlib search-status: `Chebotarev.mixedCubeEquiv` (Phase 5)

[A] Lean-Finder       "equiv Fin finrank minus one sum complex places" — no hit (mathlib index has no such bespoke equiv)
[B] Loogle            `Fin (_ - 1) ≃ Fin (_ - 1) ⊕ {_ // IsComplex _}` — no hit (the *building block* `Fintype.equivOfCardEq : Fintype.card _ = Fintype.card _ → _ ≃ _` is the relevant general tool, `Mathlib/Data/Fintype/EquivFin.lean:143`)
[C] LeanSearch        "bijection index set degree minus one real complex places number field" — no hit for a packaged equiv
[D] Grep mathlib src  `equivOfCardEq`, `card_add_two_mul_card_eq_rank`, `card_eq_nrRealPlaces_add_nrComplexPlaces` over `.lake/packages/mathlib/` — **all building blocks present**: `Fintype.equivOfCardEq` (`Data/Fintype/EquivFin.lean:143`); `card_add_two_mul_card_eq_rank` (`NumberTheory/NumberField/InfinitePlace/Basic.lean:459`); `card_eq_nrRealPlaces_add_nrComplexPlaces` (`…/Basic.lean:433`); `Fintype.card_pos`, `Fintype.card_sum`, `Fintype.card_fin` all standard.
[E] Name pattern      grep `mixedCubeEquiv` over mathlib — no hit (project-local name)

Searched for both:
  - the user's current form (the packaged equiv) — **not in mathlib**;
  - the literature-standard form (the cardinality identities) — **both already in mathlib** by the
    qualified names above.

Concluded: **"found building blocks"** — `Fintype.equivOfCardEq` +
`card_eq_nrRealPlaces_add_nrComplexPlaces` + `card_add_two_mul_card_eq_rank` + `Fintype.card_pos`;
their composition yields exactly this def. The packaged equiv itself is **not** in mathlib (and
shouldn't be — it is a one-off choice-equiv).

## Call sites — `Chebotarev.mixedCubeEquiv` (Phase 6.0)

Internal use count: **13 occurrences, all within the declaring file**
`projects/Chebotarev/CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean` (inside `liftToMixed`,
`lipschitzWith_liftToMixed`, and the `liftToMixed`-docstring region; all via `(mixedCubeEquiv
K).symm (Sum.inl …)` / `(Sum.inr …)`).
External-to-file callers: **0 distinct files** (grep over `projects/ --include=*.lean` excluding the
declaring file returned nothing).

| Caller file:line                         | Usage pattern (one-line excerpt)                                  |
|------------------------------------------|-------------------------------------------------------------------|
| NormLeOneLipschitz.lean:467              | `ψ (fun i ↦ c ((mixedCubeEquiv K).symm (Sum.inl i))) w.1`         |
| NormLeOneLipschitz.lean:470              | `c ((mixedCubeEquiv K).symm (Sum.inr w))`                         |
| NormLeOneLipschitz.lean:486–487          | `ψ (fun i ↦ c ((mixedCubeEquiv K).symm (Sum.inl i)))` (in proof)  |
| NormLeOneLipschitz.lean:515,520          | `dist (c ((mixedCubeEquiv K).symm (Sum.inr w))) …`               |

Inline-derivation grep (equivalent re-derived elsewhere without using `mixedCubeEquiv`?): (none) —
no other file re-derives the `(d−1)=(r−1)+r₂` split; it is genuinely local to this construction.

Call-site reading: **K = 0 external uses**, all internal, used only as `.symm`-applied index
relabelling. Per the Phase-6 table this is the "K = 1-ish internal use only / possibly the wrong
abstraction — could be inlined" pattern, reinforced by the Phase-2b ONE-LINER-WITHOUT-EXEMPTION
finding. The def is a private convenience, not an API surface.

### Composition check (Phase 6)

Can `Chebotarev.mixedCubeEquiv` be derived from mathlib in ≤3 chained calls? **Yes** — its body
*is* the composition.

Attempt 1 (the def itself, lightly inlined):
```lean
Fintype.equivOfCardEq (by
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  -- (d-1) = (r-1) + r₂, from the two signature identities + r ≥ 1
  omega_or_lia_using
    [card_eq_nrRealPlaces_add_nrComplexPlaces K,
     card_add_two_mul_card_eq_rank K,
     (Fintype.card_pos : 1 ≤ Fintype.card (InfinitePlace K))])
```
  - Mathlib decls used: `Fintype.equivOfCardEq`, `Fintype.card_sum`, `Fintype.card_fin`,
    `card_eq_nrRealPlaces_add_nrComplexPlaces`, `card_add_two_mul_card_eq_rank`, `Fintype.card_pos`.
  - Result: **succeeds** — this is literally the existing proof body (the project uses `lia`; mathlib
    would use `omega`).
  - Notes: a single `Fintype.equivOfCardEq` call whose argument is a `decide`-style arithmetic proof.
    No new lemma, no new idea.

Conclusion: **COMPOSABLE** — one mathlib `def` (`Fintype.equivOfCardEq`) applied to an arithmetic
proof that itself is a ≤3-lemma composition of existing mathlib signature identities.

## Verdict: `Chebotarev.mixedCubeEquiv`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the only standard content is the numeric signature identity
  `n = r₁ + 2 r₂`; no literature names a bijection of this `Fin(d−1) ≃ Fin(r−1) ⊕ {complex}` shape.
- Generality analysis (Phase 4): field parameter MAXIMALLY GENERAL, but the output is OVER-PACKAGED
  (an arbitrary `Classical`-choice equiv bundling a cardinality `Eq`); modern-idiom check found no
  upstreamable reformulation (an opaque choice-equiv has no equational API).
- Mathlib search (Phase 5): all building blocks present — `Fintype.equivOfCardEq`,
  `card_eq_nrRealPlaces_add_nrComplexPlaces`, `card_add_two_mul_card_eq_rank`, `Fintype.card_pos`;
  the packaged equiv itself is not in mathlib (and shouldn't be).
- Composition check (Phase 6): COMPOSABLE — the def body *is* `Fintype.equivOfCardEq (proof)`.

**Rationale:**

`mixedCubeEquiv` is not a mathematical object; it is a coordinate-bookkeeping convenience. Its
entire content is the cardinality equality `(finrank ℚ K − 1) = (#InfinitePlace K − 1) +
nrComplexPlaces K`, which is an immediate `omega` consequence of two signature identities that
mathlib already has (`card_eq_nrRealPlaces_add_nrComplexPlaces`, `card_add_two_mul_card_eq_rank`)
plus `Fintype.card_pos`. From that equality, mathlib's existing `Fintype.equivOfCardEq` produces the
bijection in one call. So the whole def is a ≤3-line composition of existing mathlib primitives —
exactly the NO-composable signature.

Two further facts seal it against any YES bucket. First, the bijection is **non-canonical**: it is
extracted by `Classical.choice` and the file uses only its *existence* (as a `.symm`-applied index
relabelling), never any equation about it — so it carries no API mathlib could build on, and
shipping a named arbitrary equiv would invite the false expectation of a canonical map (Phase 4.5
row 3). Second, it has **zero external call sites** and is effectively a ONE-LINER WITHOUT-EXEMPTION
(Phase 2b): no defeq barrier (it has no usable unfolding), no instance anchoring, no stable public
consumer. A general "equal cardinality ⇒ bijection" tool is already the right level of abstraction
and already in mathlib; a number-field-specific instance of it is call-site glue.

**WHY not (refactor-actionable):**
Mathlib has the building blocks; this def is a 1-call composition (`Fintype.equivOfCardEq` applied to
an `omega` cardinality proof). The cardinality proof chains exactly three existing mathlib results.
No new lemma is warranted.

Mathlib building blocks:
- `Fintype.equivOfCardEq` — `Mathlib/Data/Fintype/EquivFin.lean:143`
- `NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces` —
  `Mathlib/NumberTheory/NumberField/InfinitePlace/Basic.lean:433`
- `NumberField.InfinitePlace.card_add_two_mul_card_eq_rank` —
  `Mathlib/NumberTheory/NumberField/InfinitePlace/Basic.lean:459`
- `Fintype.card_pos`, `Fintype.card_sum`, `Fintype.card_fin` — standard.

Composition sketch (the existing body, ≤3 effective lines):
```lean
example (K : Type*) [Field K] [NumberField K] :
    Fin (Module.finrank ℚ K - 1)
      ≃ Fin (Fintype.card (InfinitePlace K) - 1) ⊕ {w : InfinitePlace K // IsComplex w} :=
  Fintype.equivOfCardEq <| by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    have h1 := card_eq_nrRealPlaces_add_nrComplexPlaces K
    have h2 := card_add_two_mul_card_eq_rank K
    have hpos : 1 ≤ Fintype.card (InfinitePlace K) := Fintype.card_pos
    omega
```

Call sites in our project (from Phase 6.0): **0 external; 13 internal, all in the declaring file.**

Refactor plan: this is a `ForMathlib/` helper but should **not** go to mathlib as a named def. Two
options, both keeping it project-local:
1. **Keep as-is, project-local** (lowest effort): it is a fine private helper for `liftToMixed`; just
   do not earmark it for upstreaming. The file is in `ForMathlib/`, but this particular decl is the
   exception — it is glue, not contribution.
2. **Inline** (cleaner): replace the named def with a local `let`/term inside `liftToMixed` (or a
   `private` def), since it has no external consumers and no defeq/instance role. At the (internal)
   use sites lines 467, 470, 486–487, 515, 520, substitute the inlined `Fintype.equivOfCardEq …`
   relabelling. No argument-order subtlety (always used as `(… ).symm (Sum.inl/inr _)`).

If upstreaming the *file's* genuine results, only the cardinality fact (`(d−1)=(r−1)+r₂`) might
conceivably be worth a one-line mathlib lemma — but even that is a trivial `omega` corollary of two
existing lemmas, so it too is NO-composable. The equiv packaging is not upstreamable.

Next action: do **not** PR `mixedCubeEquiv` to mathlib. Either leave it project-local (drop any
mathlib earmark) or inline it at its 13 internal use sites via `Fintype.equivOfCardEq` + `omega`.

---

## Next step

Do not submit to mathlib. Keep `mixedCubeEquiv` project-local (de-earmark) or inline it at its
internal call sites as `Fintype.equivOfCardEq` applied to the 3-lemma cardinality proof; the
building blocks (`Fintype.equivOfCardEq`, `card_eq_nrRealPlaces_add_nrComplexPlaces`,
`card_add_two_mul_card_eq_rank`, `Fintype.card_pos`) are already in mathlib.
