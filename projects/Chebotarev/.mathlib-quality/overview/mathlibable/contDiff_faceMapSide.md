# /mathlibable report — `Chebotarev.contDiff_faceMapSide`

## Baseline (Phase 0)
- lake build:               ✗ STALE (incompatible olean headers from a partial mathlib rebuild;
                            `Mathlib/Order/Filter/Interval.olean` header mismatch). Per the task
                            brief, the local build is known stale → reasoning from source + the
                            mathlib index, which is the sanctioned fallback.
- decl `Chebotarev.contDiff_faceMapSide`:  ✓ resolved at
                            `projects/Chebotarev/CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean:159`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Lipschitz parametrization of the frontier of `normLeOne K` — the
                            quantitative-regularity (Lipschitz-boundary) input to the effective
                            lattice-point count `Chebotarev.exists_card_inter_smul_lattice_sub_volume_mul_pow_le`.
- namespace:                 `Chebotarev` (verified: single `namespace Chebotarev … end Chebotarev`
                            block, lines 79/673; the parsed qualified name was correct).

## Statement (Phase 1)

`Chebotarev.contDiff_faceMapSide` states: for a number field `K`, a place index
`i : {w : InfinitePlace K // w ≠ w₀}` and a real constant `a : ℝ`, the side-face
parametrization map `faceMapSide K i a : ({w // w ≠ w₀} → ℝ) → realSpace K` is
continuously differentiable (`ContDiff ℝ 1`).

Here `faceMapSide` (defined at line 146, **project-local**) is the cube-parametrization of the
`expMapBasis`-image of a side face `{x | x i = a}` of the box `paramSet K`:

  `faceMapSide i a c  =  c i • expMapBasis (fun w ↦ if w = w₀ then 0 else if ⟨w,_⟩ = i then a else c ⟨w,_⟩)`.

It pins the `w₀`-coordinate to `0`, pins the `i`-coordinate to the constant `a`, fills the other
coordinates from the cube point `c`, applies the mathlib map `expMapBasis`, and scales by `c i`
(the scaling encodes the substitution `t = exp(x w₀) ∈ (0,1]` that linearizes the unbounded
`w₀`-direction of the face).

Variables / typeclasses (Lean side):
- `K : Type*` `[Field K] [NumberField K]` — the number field.
- `i : {w : InfinitePlace K // w ≠ w₀}` — the pinned coordinate (a non-distinguished infinite place).
- `a : ℝ` — the pin value (used at `a ∈ {0,1}`, the two box endpoints).

Hypotheses (Lean side): none beyond the parameters.

Conclusion (math): the bespoke map `faceMapSide K i a` is C¹ on `({w // w ≠ w₀} → ℝ)`.
Conclusion (Lean): `ContDiff ℝ 1 (faceMapSide K i a)`.

Proof body (3 lines):
```lean
refine (contDiff_apply ℝ ℝ i).smul ((contDiff_expMapBasis K).comp (contDiff_pi.mpr fun w ↦ ?_))
by_cases hw : w = w₀
· simpa only [dif_pos hw] using contDiff_const
· simp only [dif_neg hw]; by_cases hi : … = i
  · simpa only [if_pos hi] using contDiff_const
  · simpa only [if_neg hi] using contDiff_apply ℝ ℝ _
```
i.e. `ContDiff.smul` of (the `i`-projection `contDiff_apply`) and (`contDiff_expMapBasis` composed
with a pi-map whose every coordinate is `contDiff_const` or a projection `contDiff_apply`).

## Size classification (Phase 2a)

Verdict: SMALL
Reason: a `ContDiff` (smoothness) bookkeeping lemma about a project-local definition `faceMapSide`;
it is a stepping-stone helper feeding `exists_lipschitzWith_comp_clampUnit`, not a `## Main results`
entry and not named after a person/place. (Literature width run EXHAUSTIVE regardless.)

## One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure` → one-line definition check is **n/a**.
(Note: the proof is a 3-call composition; this is itself a strong NO-composable signal, carried to
Phase 6/7.)

## Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                               | Hit? | Standard form found | Notes |
|----|----------------------------------|-----------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | smoothness of exponential map Minkowski embedding fundamental domain unit lattice number field regulator C¹ | partial | exp map is smooth; Minkowski fundamental domain | No named "C¹ of a side-face parametrization"; only generic "exp map is smooth" + Minkowski-domain facts |
|  2 | WebSearch (high-level concept)   | Lipschitz parametrization boundary fundamental domain counting ideals number field Widmer Debaene smooth boundary | yes | boundary is `(n-1)`-Lipschitz parametrizable (Masser–Vaaler / Widmer) | The literature standard is the **Lipschitz** boundary cover; C¹-ness of individual maps is a route to it, not itself named (arXiv:1611.10103 Debaene; Widmer) |
|  3 | WebSearch (named-after / mathlib)| expMap expMapBasis number field NormLeOne mathlib smooth ContDiff fundamental cone canonical embedding | partial | mathlib `CanonicalEmbedding`/`FundamentalCone`; `ContDiff` defn | Confirms `expMapBasis`/`NormLeOne` are a mathlib-internal construction; no smoothness lemma surfaced for them |
|  4 | WebSearch (Lipschitz-from-C¹)    | "continuously differentiable" boundary map parametrization restricted to compact set Lipschitz lattice point counting error term standard | yes | `S ∈ Lip(D,M,L)`: M maps `[0,1]^{D-1}→ℝ^D`, each L-Lipschitz | Literature packages the boundary as **finitely many Lipschitz maps**; "C¹ then Lipschitz on a compact cube" is the routine bridge, not a named theorem |
|  5 | ChatGPT MCP                      | (asked: is face-map C¹-ness named vs implementation detail; is `contDiff_expMapBasis` mathlib-worthy; is `faceMapSide` C¹ a routine `fun_prop`-style composition) | n/a  | — | MCP **down** (Codex exec error). Documented fallback used: reasoned from source + WebSearch + mathlib grep, per the task brief. |
|  6 | Local references                 | grep `projects/Chebotarev/.mathlib-quality/references/`                                              | n/a  | — | references/ directory absent for this project → recorded n/a |
|  7 | nLab                             | "exponential map smooth" / "Lipschitz boundary lattice point counting"                               | n/a  | — | Not a categorical/nLab concept; it is an analytic-NT estimate. The smoothness of `exp`/products is elementary calculus, not an nLab entry. |
|  8 | nCatLab                          | —                                                                                                   | n/a  | — | Not a categorical concept. |
|  9 | Stacks Project                   | —                                                                                                   | n/a  | — | Not an algebraic-geometry / scheme-theoretic concept. |
| 10 | MathOverflow / Math.SE           | (covered by #2/#4 web hits)                                                                          | yes  | Lipschitz/Schanuel boundary principle | The "Principle of Lipschitz" (Schanuel) is the named tool; C¹-ness of a specific map is below its granularity. |
| 11 | recent arXiv (last 5 yrs)        | Gun–Ramaré–Sivaraman §3.3; Debaene 2017 (arXiv:1611.10103); o-minimality + lattice counting (2503.01731) | yes  | finitely-many-Lipschitz-maps boundary | The exact source the module cites (Gun–Ramaré–Sivaraman, after Debaene) speaks of the Lipschitz cover, never the per-map C¹ lemma |

The protocol passes: WebSearch ran 4 distinct queries at different generality levels (specific
smoothness / high-level Lipschitz-boundary / mathlib-internal / C¹→Lipschitz bridge); ChatGPT MCP
attempted and recorded down with the sanctioned fallback; local refs n/a (absent); nLab / nCatLab /
Stacks / arXiv each checked or n/a-with-reason.

## Literature summary (Phase 3)

Concept identified as: **C¹-smoothness of a coordinate face-parametrization of the boundary of the
`normLeOne` fundamental region**, an intermediate lemma toward the **Lipschitz-parametrizable
boundary** of the lattice-point-counting machinery (Masser–Vaaler / Widmer / Debaene /
Gun–Ramaré–Sivaraman / Schanuel's Principle of Lipschitz).

Sources agree on the standard form: yes — for the **high-level** object (the boundary is covered by
finitely many `L`-Lipschitz maps `[0,1]^{D-1}→ℝ^D`). They are **silent** on the granular object in
this lemma (the C¹-ness of one specific `expMapBasis`-based side-face map): that map is a Lean
construct (`faceMapSide`) with no literature name. The literature gets Lipschitz boundaries by
whatever means (often directly), without isolating a per-face C¹ statement.

Most general standard form: "the boundary of the fundamental domain is `(n−1)`-Lipschitz
parametrizable" — i.e. the conclusion of the *whole file*
(`normLeOne_frontier_lipschitz_cover`), not of this individual smoothness lemma.

Generality dimensions where the literature varies:
  - regularity used to obtain Lipschitz: C¹/piecewise-smooth/`o`-minimal cell — the literature uses
    whatever is convenient; mathlib's chosen route here is C¹-on-a-compact-cube ⇒ Lipschitz.
  - the bespoke `faceMapSide` itself has no literature analog — it is a formalization device.

Because the granular concept returns **no named literature object**, this is a NO/NOT-novel signal
for *this specific lemma* (it is plumbing), per the verdicts-doc "treating literature absence as
YES is an anti-pattern": absence here means too-specific/plumbing, not novel.

## Generality analysis — `Chebotarev.contDiff_faceMapSide`

Literature-standard form (from Phase 3): there is none for this granular object; the relevant
standard object is the file-level Lipschitz boundary cover, which this lemma only feeds.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[Field K] [NumberField K]` | number field | number field (intrinsic to `expMapBasis`/`InfinitePlace`) | NO | the statement is *about* `expMapBasis K`, a number-field object; cannot be weakened without dissolving the statement |
| 2 | `i : {w // w ≠ w₀}`, `a : ℝ` | a place index + a real pin | n/a (bespoke) | NO | these are the defining data of `faceMapSide`; not a generality axis |
| 3 | regularity `ContDiff ℝ 1` (C¹) | C¹ | the map is in fact C^∞ (`exp` and powers of positive constants are smooth) | yes — could state `ContDiff ℝ ⊤`/`∞` | the proof uses only generic `ContDiff` lemmas that hold for any `n`; `1` is what downstream needs (`ContDiff.locallyLipschitz`). Strengthening to `⊤` is mechanical but does not make the lemma any more mathlib-worthy — it is still about a bespoke def. |

### Generality verdict (Phase 4b)

The current form is: NARROW BY SUBJECT (it is maximally general *given its subject*, the project-
local `faceMapSide`; the only mechanical strengthening is `1 → ⊤` in the regularity, which is
cosmetic). The narrowness that matters is not a missing typeclass weakening — it is that the
**subject of the lemma (`faceMapSide`) is not a mathlib object**, so there is nothing to generalise
*toward* mathlib; the lemma is intrinsically project-scoped.
Number of weakening opportunities found: 1 (cosmetic: `ContDiff ℝ 1` → `ContDiff ℝ ⊤`).
Proposed restatement: none worth doing — the lemma cannot escape its bespoke subject.
Cost of `1→⊤`: CHEAP, but irrelevant to the verdict (does not change that `faceMapSide` is local).

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Reformulation | Downstream |
|---|----------|----------|---------------|------------|
| 1 | bundled hypotheses → typeclasses/instances? | no | — | already typeclass-driven (`NumberField`) |
| 2 | sequences/metric → filters/topology? | no | — | this is a `ContDiff` statement; no sequential content |
| 3 | construction → universal-property class? | no | — | nothing to characterise universally |
| 4 | set-with-closure-pred → bundled substructure? | no | — | no substructure here |
| 5 | vector-space/metric/field-specific → weaken typeclasses? | no | — | `ℝ`-smoothness of a number-field map; the `ℝ` is essential |
| 6 | 1-categorical → higher-categorical? | no | — | not categorical |
| 7 | concrete index → arbitrary monoid/group? | no | — | the index set is `InfinitePlace K`, intrinsic |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. This is an elementary C¹ composition; there is no contemporary
mathlib reformulation that improves its organisation — its subject is a bespoke face map, and the
mathlib-idiomatic way to discharge such a goal is exactly the composition already used (or
`fun_prop`), not a new named lemma.

## Diamond / defeq risk — n/a (Phase 4.5)

n/a — declaration kind is `theorem` (no definitional equalities / typeclass-search paths introduced).

## Mathlib search-status: `Chebotarev.contDiff_faceMapSide`

Note: the lean_loogle / lean_leansearch MCP tools were not available in this environment (only
WebSearch, the ChatGPT MCP — down — and LSP surfaced). Method [D] (direct grep of the pinned mathlib
source tree at `.lake/packages/mathlib/`) was used as the authoritative substitute, supplemented by
WebSearch over the mathlib4 docs site ([A]/[C] proxy).

[A] Lean-Finder       (via mathlib4-docs WebSearch) "expMapBasis ContDiff", "faceMapSide"   → no hits for any smoothness lemma on `expMapBasis`; no `faceMap*` at all
[B] Loogle            tool unavailable; pattern intent `ContDiff ℝ _ (faceMapSide _ _ _)` and `ContDiff _ _ ⇑expMapBasis` → covered by [D] grep: no such lemma in mathlib
[C] LeanSearch        (via WebSearch) "continuously differentiable expMapBasis number field" → only generic ContDiff defn + CanonicalEmbedding/FundamentalCone pages; no smoothness API for the exp-basis map
[D] Grep mathlib src  `expMapBasis`, `faceMap`, `frontierCover`, `ContDiff.smul`, `contDiff_pi`, `contDiff_apply`, `contDiff_exp`, `contDiff_const`, `ContDiff.exp`
      → `expMapBasis` lives ONLY in `Mathlib/NumberTheory/NumberField/CanonicalEmbedding/NormLeOne.lean`.
        Mathlib proves for it: `continuous_expMapBasis`, `injective_expMapBasis`, an open-map
        (`OpenPartialHomeomorph`), and **`hasFDerivAt_expMapBasis` (line 581)** with explicit
        derivative `fderiv_expMapBasis` (line 576) — i.e. mathlib proves it is *Fréchet-differentiable
        everywhere*, but does **NOT** state `ContDiff`/`contDiff_expMapBasis`.
      → `faceMap*` / `faceMapSide` / `frontierCover*` / "Lipschitz cube cover": **absent** from mathlib
        (the only `FaceMap` hits are simplicial `AlternatingFaceMapComplex` and Čech — unrelated).
      → building blocks all present: `ContDiff.smul` (Operations.lean:574), `contDiff_pi`
        (Operations.lean:112), `contDiff_apply` (Operations.lean:145), `ContDiff.comp` (Comp.lean:155),
        `contDiff_const` (Basic.lean:103), `contDiff_exp` / `ContDiff.exp` (ExpDeriv.lean).
[E] Name pattern      `contDiff_faceMapSide` / `faceMapSide` → exists ONLY in the project file; not in mathlib.

Searched for both:
  - the user's current form (`ContDiff ℝ 1 (faceMapSide K i a)`): not in mathlib — `faceMapSide` is
    project-local, so it cannot be.
  - the nearest mathlib-relevant general form (`ContDiff` of `expMapBasis`): also NOT in mathlib;
    mathlib stops at `HasFDerivAt expMapBasis`.

Concluded: **not in mathlib** (the lemma's subject `faceMapSide` is a project-local definition, so
no mathlib decl can match). The closest mathlib API is `hasFDerivAt_expMapBasis` (differentiability,
not C¹) plus the generic `ContDiff` composition lemmas — i.e. mathlib has the **building blocks**,
not this packaged statement.

## Call sites — `Chebotarev.contDiff_faceMapSide`

Internal use count: **2** (within the project, excluding the declaring lemma) — but both are **in the
same declaring file** `NormLeOneLipschitz.lean`; external-to-file callers: **0**.

| Caller file:line | Usage pattern |
|------------------|---------------|
| NormLeOneLipschitz.lean:300 | `exists_lipschitzWith_comp_clampUnit (contDiff_faceMapSide K p.1 (if p.2 then 1 else 0))` — feeds the per-face Lipschitz constant in `exists_lipschitzWith_frontierCoverFamily` |
| NormLeOneLipschitz.lean:542 | `hbd _ (contDiff_faceMapSide K p.1 (if p.2 then 1 else 0)).continuous` — uses only `.continuous` (the C¹ is overkill at this site; continuity would suffice) |

Inline-derivation grep (re-derived elsewhere without this lemma?): (none) — it is the single source
of the face-map smoothness fact, but only because the fact is needed in exactly one local
construction. The file `NormLeOneLipschitz.lean` is imported by `CebotarevDensity.lean`,
`ZetaProduct.lean`, and `IdealCongruenceCount.lean`, but **none of them reference
`contDiff_faceMapSide`** — they consume the file-level results (`normLeOne_frontier_lipschitz_cover*`),
not this internal helper.

Call-sites signal: K = 2, both same-file, 0 external, one site needing only `.continuous`. This is a
**file-internal plumbing lemma** — companion to `contDiff_faceMapZero` and `contDiff_expMapBasis`,
all three existing purely to drive `exists_lipschitzWith_comp_clampUnit`. Per the call-sites table
("K small, same-file, internal helper"), this leans NO-composable / inline.

## Composition check (Phase 6)

Can `Chebotarev.contDiff_faceMapSide` be derived from mathlib in ≤3 chained calls?

The lemma's subject `faceMapSide` is project-local, so "deriving it from mathlib" means: is the
*proof* a routine composition of mathlib `ContDiff` lemmas (given the project's own
`contDiff_expMapBasis`)? It is — verbatim, the existing 3-line proof:

Attempt 1 (the actual proof):
```lean
(contDiff_apply ℝ ℝ i).smul
  ((contDiff_expMapBasis K).comp
    (contDiff_pi.mpr fun w ↦ <const-or-projection>))
```
  - Mathlib decls used: `contDiff_apply`, `ContDiff.smul`, `ContDiff.comp`, `contDiff_pi`,
    `contDiff_const` — all standard.
  - Plus the **one non-mathlib input** `contDiff_expMapBasis K` (the project's C¹-ness of
    `expMapBasis`, itself NOT in mathlib).
  - Result: succeeds — it is exactly a `ContDiff.smul`/`comp`/`pi` composition; the coordinatewise
    `by_cases` is just selecting `contDiff_const` vs `contDiff_apply`. This is the kind of goal
    `fun_prop` discharges once `expMapBasis` is registered C¹ (note `contDiff_expMapBasis` itself is
    proved by `fun_prop`).

Conclusion: **COMPOSABLE** — from mathlib's generic `ContDiff` API **plus** the project's
`contDiff_expMapBasis`. There is no new *mathematics* here; the lemma is glue. (The only reason it
is not purely mathlib-composable is that `contDiff_expMapBasis` is not yet in mathlib — and that is
the lemma that would carry any genuine value, not this face-map wrapper.)

## Verdict: `Chebotarev.contDiff_faceMapSide`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the granular object (C¹-ness of a specific `expMapBasis` side-face
  parametrization) has **no named form**; the literature standard is the *file-level* Lipschitz
  boundary cover (Widmer/Debaene/Masser–Vaaler/Schanuel), which this lemma merely feeds.
- Generality analysis (Phase 4): NARROW BY SUBJECT — its subject `faceMapSide` is project-local; the
  only weakening is the cosmetic `ContDiff 1 → ⊤`. No modern-idiom improvement (Phase 4c: all no).
- Mathlib search (Phase 5): not in mathlib; `faceMapSide` is project-local; the closest mathlib API
  is `hasFDerivAt_expMapBasis` (differentiability, not C¹) + generic `ContDiff` composition lemmas.
- Composition check (Phase 6): COMPOSABLE — the proof is a 3-call `ContDiff.smul`/`comp`/`pi`
  composition (plus the project's own `contDiff_expMapBasis`); `fun_prop`-grade glue.

**Rationale:**

`contDiff_faceMapSide` is a file-internal smoothness bookkeeping lemma about a bespoke definition
(`faceMapSide`) that exists only inside this Chebotarev development. Its conclusion is not a named
mathematical object: the literature on counting ideals/lattice points (Gun–Ramaré–Sivaraman §3.3
after Debaene; Widmer; Masser–Vaaler; Schanuel's Principle of Lipschitz) cares about the *boundary
being covered by finitely many Lipschitz maps* — the conclusion of the whole file
(`normLeOne_frontier_lipschitz_cover*`), not the C¹-ness of any individual face parametrization. The
C¹ statement here is purely the Lean route to "Lipschitz on the compact cube" via
`ContDiff.locallyLipschitz` + `LocallyLipschitzOn.exists_lipschitzOnWith_of_compact`. Both call sites
are in the declaring file; one of them only needs `.continuous`. No external file references it.

Mathlib already has every primitive the proof uses (`ContDiff.smul`, `ContDiff.comp`, `contDiff_pi`,
`contDiff_apply`, `contDiff_const`, `contDiff_exp`), and the proof is a clean ≤3-call composition of
them — exactly a `fun_prop`-discharged goal once `expMapBasis` is known C¹. There is therefore no new
lemma to ship: the smoothness of a *specific* bespoke face map should be derived inline at its (few,
local) use sites, not upstreamed as standalone API. The one piece in this neighbourhood that *would*
be worth mathlib is **`contDiff_expMapBasis`** — the C¹-ness of the genuinely-mathlib map
`expMapBasis` — which mathlib is currently missing (it stops at `hasFDerivAt_expMapBasis`); but that
is a *different declaration* and is tracked separately. This wrapper lemma is not it.

**WHY not (refactor-actionable):**
Mathlib has the building blocks; `contDiff_faceMapSide` is a ≤3-call composition of them over the
project-local `faceMapSide`. No new mathlib lemma is justified — keep it project-local (it is fine as
a ForMathlib helper *for this project's* Lipschitz-cover assembly), or inline the composition at its
two sites.

Mathlib building blocks: `ContDiff.smul` (`Mathlib/Analysis/Calculus/ContDiff/Operations.lean:574`),
`ContDiff.comp` (`…/ContDiff/Comp.lean:155`), `contDiff_pi` (`…/ContDiff/Operations.lean:112`),
`contDiff_apply` (`…/ContDiff/Operations.lean:145`), `contDiff_const`
(`…/ContDiff/Basic.lean:103`) — together with the project's `Chebotarev.contDiff_expMapBasis`
(NOT mathlib; the real upstreaming candidate in this area).

Composition sketch (the existing proof, ≤3 mathlib calls + 1 project input):
```lean
example (K) [Field K] [NumberField K] (i : {w : InfinitePlace K // w ≠ w₀}) (a : ℝ) :
    ContDiff ℝ 1 (faceMapSide K i a) :=
  (contDiff_apply ℝ ℝ i).smul
    ((contDiff_expMapBasis K).comp (contDiff_pi.mpr fun w ↦ by
      by_cases hw : w = w₀ <;> simp only [dif_pos hw, dif_neg hw] <;>
        first | exact contDiff_const | (split_ifs <;> [exact contDiff_const; exact contDiff_apply ℝ ℝ _])))
```
(Equivalently, once `expMapBasis` carries a `@[fun_prop]` C¹ lemma, the whole goal is `by fun_prop` —
this is already how `contDiff_expMapBasis` itself is proved.)

Call sites in our project (from Phase 6.0): K = 2 (lines 300, 542), both in the declaring file;
0 external callers.

Refactor plan: **no mathlib action.** This lemma stays project-local. If a future cleanup wants to
shrink the file's API surface, the two uses (lines 300, 542) can each inline the composition above
(at line 542 only `.continuous` is needed, so `(… ).continuous` of the inlined `ContDiff` term, or
even a direct `Continuous` composition, suffices). The genuinely-upstreamable neighbour
`Chebotarev.contDiff_expMapBasis` should be assessed/【PR'd】 on its own (it fills a real mathlib gap:
mathlib has `hasFDerivAt_expMapBasis` but no `ContDiff` for `expMapBasis`).

---

## Next step

No mathlib PR for `contDiff_faceMapSide`. It is `NO-composable-from-mathlib`: a ≤3-call
`ContDiff.smul`/`comp`/`pi` composition over the project-local `faceMapSide`, used twice in-file and
nowhere else. Keep it project-local (or inline at the two sites). Separately, consider
`/mathlibable Chebotarev.contDiff_expMapBasis` — that is the lemma in this cluster that fills a real
mathlib gap (`expMapBasis` has `HasFDerivAt` but no `ContDiff` in mathlib).
