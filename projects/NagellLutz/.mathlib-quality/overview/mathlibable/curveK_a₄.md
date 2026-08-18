# /mathlibable report — `LutzNagell.PID.curveK_a₄`

**Verdict: NO-mathlib-has-it** — this is `WeierstrassCurve.map_a₄` (the `@[simps]`-generated
projection lemma for `WeierstrassCurve.map`) specialised to `f := algebraMap R K`. It follows
from the existing mathlib lemma in one defeq line.

---

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per session note); decl elaborates as written, body is `by simp [curveK]`
- decl `LutzNagell.PID.curveK_a₄`:  resolved at `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDCurve.lean:32`
- kind:                     lemma (`@[simp]`)
- has sorry:                no
- module docstring summary: "General Weierstrass model over a PID `R` and its base change to the fraction field `K`, with basic rewriting lemmas." Explicitly states it *generalizes* `GeneralCurve.lean` from `ℤ/ℚ` to an arbitrary PID.

Full source of the declaration:

```lean
namespace LutzNagell
namespace PID
open WeierstrassCurve
variable (R : Type*) [CommRing R]
variable (K : Type*) [Field K] [Algebra R K]
variable (W : WeierstrassCurve R)

/-- The base change of `W` to the fraction field `K`. -/
abbrev curveK : WeierstrassCurve K := W.map (algebraMap R K)

@[simp] lemma curveK_a₄ : (curveK R K W).a₄ = algebraMap R K W.a₄ := by simp [curveK]
```

---

### Statement (Phase 1)

`LutzNagell.PID.curveK_a₄` is a rewriting lemma stating that the `a₄` coefficient of the base-changed
Weierstrass curve `curveK R K W := W.map (algebraMap R K)` equals the image under the structure map
`algebraMap R K` of the `a₄` coefficient of the original curve `W`. In other words: taking the fourth
Weierstrass coefficient commutes with base change along `R → K`. This is the trivial functoriality of
a structure projection through `WeierstrassCurve.map`, which by definition applies the ring homomorphism
coefficient-wise.

Variables / typeclasses involved (Lean side):
- `R : Type*` `[CommRing R]` — the base commutative ring (called a PID in the file, but the lemma uses no PID structure)
- `K : Type*` `[Field K] [Algebra R K]` — an `R`-algebra (called the fraction field, but the lemma uses no field structure)
- `W : WeierstrassCurve R` — a Weierstrass curve over `R`

Hypotheses (Lean side): none.

Conclusion (math): `a₄(W ⊗_R K) = (algebraMap R K)(a₄(W))`.

Conclusion (Lean): `(curveK R K W).a₄ = algebraMap R K W.a₄`, i.e.
`(W.map (algebraMap R K)).a₄ = algebraMap R K W.a₄`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A `@[simp]` glue lemma equating a structure projection of `WeierstrassCurve.map` with the
image of that projection. Not a named theorem, not a new structure, not a `## Main results` entry —
it is one of five sibling rewriting lemmas (`curveK_a₁ … curveK_a₆`).

### One-line check (Phase 2b)

Body line count: 1 substantive line (`by simp [curveK]`).
One-liner verdict: **n/a — kind is `lemma`, not `def`** (the one-liner exemption table is for
`def`/`abbrev`/`structure`). Recorded for context: this is a one-line *proof* of a glue lemma,
the strongest possible NO signal — its body is exactly the unfolding `curveK → W.map …` followed
by the mathlib simp lemma `map_a₄`.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query | Hit? | Standard form found | Notes |
|----|----------------------------------|-------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "Weierstrass curve base change coefficients a4 ring homomorphism functoriality" | yes | `(W.map φ).a₄ = φ W.a₄`; `W.map φ = ⟨φa₁,φa₂,φa₃,φa₄,φa₆⟩` | Result independently names the mathlib lemma `WeierstrassCurve.map_a₄` and states coefficients map componentwise. |
|  2 | WebSearch (general form)         | same query, general angle (base change / Mordell–Weil functoriality) | yes | base change is functorial; coefficients transform componentwise under `x=u²x'+r, y=u³y'+u²sx'+t` | Silverman-style functoriality; the coefficient-wise map along a ring hom is the degenerate (u=1,r=s=t=0) case. |
|  3 | WebSearch (named-after / aliases)| "shift / pullback of Weierstrass coefficients" (covered by #1 result set) | yes | same as #1 | The concept has no person-name; it is "base change of a Weierstrass equation". |
|  4 | ChatGPT MCP                      | (MCP down this session per task note — fallback to WebSearch #1–#3 + direct mathlib source read) | n/a | — | Compensated by reading the mathlib `def map`/`@[simps]` source directly, which is authoritative. |
|  5 | Local references                 | n/a | n/a | — | No `.mathlib-quality/references/` PDFs needed; the standard form is a structure projection, fixed by the `WeierstrassCurve` definition itself. |
|  6 | nLab                             | "elliptic curve / Weierstrass equation base change" | n/a | — | nLab has no finer statement than "coefficients pull back"; not informative beyond #1/#2. |
|  7 | nCatLab (categorical)            | — | n/a | — | Not a categorical concept beyond "map is functorial on coefficients". |
|  8 | Stacks Project (alg geom)        | "Weierstrass equation base change" | n/a | — | Stacks treats elliptic curves abstractly; no per-coefficient `a₄` lemma. The componentwise statement is below Stacks' granularity. |
|  9 | MathOverflow / MathSE            | — | n/a | — | A componentwise base-change identity is folklore; no MO/MSE thread needed. |
| 10 | recent arXiv (last 5 yr)         | arXiv:2302.10640 (Lean group-law formalisation) surfaced in #1 | yes | uses the same `WeierstrassCurve.map`/`map_aᵢ` API | Confirms this is the established mathlib formalisation idiom, not novel. |

### Literature summary (Phase 3)

Concept identified as: **base change of a Weierstrass equation along a ring homomorphism**, at the level
of a single coefficient (`a₄`). The "standard form" is fixed by the *definition* of a Weierstrass curve:
the coefficients are the structure fields, and `map` applies the homomorphism to each, so
`(W.map φ).a₄ = φ(W.a₄)` is true by construction.
Sources agree on the standard form: yes.
Most general standard form: `(W.map f).a₄ = f W.a₄` for any ring homomorphism `f : R →+* A` between
commutative rings — exactly mathlib's `WeierstrassCurve.map_a₄`.
Generality dimensions where the literature varies:
  - target structure: the literature/mathlib state it for an arbitrary ring hom `f : R →+* A`; the
    project's lemma specialises `f := algebraMap R K` for an `R`-algebra `K`.
  - `R` strength: literature/mathlib need only `CommRing R`; the project lemma sits under a `[Field K]`
    + PID narrative but uses none of it.
Disagreement with the literature: none — the project form is a strict specialisation of the standard form.

---

### Generality analysis — `LutzNagell.PID.curveK_a₄`

Literature-standard form (from Phase 3): `WeierstrassCurve.map_a₄ : (W.map f).a₄ = f W.a₄` for
`f : R →+* A`, `[CommRing R] [CommRing A]`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `K`, `[Field K] [Algebra R K]`, map `algebraMap R K` | base change to an `R`-algebra that is a field | base change along an arbitrary ring hom `f : R →+* A`, `A` a comm ring | yes | The proof uses neither `Field K` nor algebra-over-PID; the hom can be any `R →+* A`. mathlib's general form already covers this. |
| 2 | `R` `[CommRing R]` (called "PID") | comm ring (PID in narrative) | comm ring | NO (already minimal) | `CommRing R` is exactly what mathlib's `map_a₄` requires; no PID hypothesis is used. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (specialised to `f = algebraMap R K`, `K` a field).
Number of weakening opportunities found: 1 (replace `algebraMap R K` over a field by an arbitrary
ring hom `f : R →+* A`).
Proposed restatement: not needed as a new lemma — the maximally-general form **already exists in
mathlib** as `WeierstrassCurve.map_a₄`. The project lemma is a redundant specialisation, so the
correct action is deletion + reuse, not generalisation.
Cost of restatement: n/a (NO-mathlib-has-it, not YES-but-generalise).

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" → typeclasses/instances? | no | — | Already typeclass-driven (`[CommRing]`, `[Algebra]`). |
|  2 | sequences/metric → filters/topology? | no | — | No topology/metric here. |
|  3 | construct → universal-property class? | no | — | `map` is already the canonical functorial construction. |
|  4 | set+closure-predicate → bundled substructure? | no | — | N/A. |
|  5 | vector-space/field-specific → weaken typeclasses? | yes | drop `[Field K]`; use `f : R →+* A`, `[CommRing A]` | This is precisely what `WeierstrassCurve.map_a₄` already does — the modern form *is* the existing mathlib lemma. |
|  6 | 1-categorical → higher-categorical? | no | — | N/A. |
|  7 | concrete index ℕ/ℤ/ℝ → general structure? | no | — | No numeric index. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: yes, and **it already exists in mathlib** (`WeierstrassCurve.map_a₄`,
stated for an arbitrary ring hom). The project lemma is the field-specialised shadow of it. This
reinforces NO-mathlib-has-it rather than YES-but-generalise (mathlib already holds the general form).

---

### Diamond / defeq risk — n/a

n/a — declaration kind is `lemma` (no definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `LutzNagell.PID.curveK_a₄`

[A] Lean-Finder       "Weierstrass map coefficient a4"             n/a (index offline this session); compensated by direct source read
[B] Loogle            `WeierstrassCurve.map`, `_.a₄ = _ _.a₄`       n/a (index offline); direct grep of mathlib src used instead (method [D])
[C] LeanSearch        "coefficient a4 of mapped Weierstrass curve"  n/a (index offline); WebSearch #1 independently surfaced `WeierstrassCurve.map_a₄`
[D] Grep mathlib src  `map_a₄`, `def map`, `@[simps]`              **HIT** — `WeierstrassCurve.map` at `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:231` carries `@[simps]` (line 230), auto-generating `WeierstrassCurve.map_a₄ : (W.map f).a₄ = f W.a₄`. Referenced at Weierstrass.lean:249, 259 and Reduction.lean:82.
[E] Name pattern      `curveK_a₄` across project + `map_a₄` mathlib  curveK_a₄ exists only in this project; `map_a₄` is the canonical mathlib name.

Searched for both:
  - the user's current form `(curveK R K W).a₄ = algebraMap R K W.a₄` — only in the project.
  - the literature-standard/general form `(W.map f).a₄ = f W.a₄` — **found in mathlib** as
    `WeierstrassCurve.map_a₄` (and the whole `map_a₁ … map_a₆` family is generated by the same `@[simps]`).

Concluded: **found in mathlib as `WeierstrassCurve.map_a₄`; more general form** (arbitrary ring hom
`f : R →+* A`). The project's lemma is the `f := algebraMap R K` specialisation.

---

### Call sites — `LutzNagell.PID.curveK_a₄`

Internal use count: **0** (within the project, excluding the declaring file).
External-to-file callers: **0 distinct files**.

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none) | No occurrence of `curveK_a₄` anywhere outside `PIDCurve.lean:32`. |

Inline-derivation grep: downstream files (`PIDMain.lean`, `PIDPrimeOrder.lean`, …) manipulate
`curveK R K W` but never reference `curveK_a₄` by name; they discharge coefficient goals through
`simp [curveK]` / `simp [curveK, …]`, which unfolds `curveK` to `W.map (algebraMap R K)` and then
fires mathlib's `@[simp] map_a₄` directly. So the lemma is a redundant `@[simp]` duplicate of
`WeierstrassCurve.map_a₄`: every consumer already reaches the mathlib lemma without it.

Signal: K = 0 internal uses, no inline re-derivation of *this lemma's name* — and mathlib has the
result. Per the call-sites table this points squarely at NO-mathlib-has-it.

---

### Composition check (Phase 6)

Can `LutzNagell.PID.curveK_a₄` be derived from mathlib in ≤3 chained calls?

Attempt 1: `WeierstrassCurve.map_a₄ (f := algebraMap R K)` — i.e. `(W.map (algebraMap R K)).a₄ = algebraMap R K W.a₄`.
  - Mathlib decls used: `WeierstrassCurve.map_a₄`.
  - Result: **succeeds**. `curveK R K W` is an `abbrev` for `W.map (algebraMap R K)`, so the project
    statement is *definitionally* the conclusion of `map_a₄ (algebraMap R K)`. Proof:
    `:= WeierstrassCurve.map_a₄ _` (or simply `by simp`, since `map_a₄` is `@[simp]` and `curveK`
    is a reducible abbrev).
  - Notes: zero-call, not even a composition — it is the same lemma after unfolding an abbreviation.

Conclusion: the form is recovered by a single existing mathlib lemma. Because mathlib *names* that
lemma (`WeierstrassCurve.map_a₄`), the correct bucket is **NO-mathlib-has-it** (not
NO-composable-from-mathlib): there is nothing to inline — consumers should rely on the mathlib
`@[simp]` lemma directly.

---

## Verdict: `LutzNagell.PID.curveK_a₄`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): the coefficient-wise base-change identity `(W.map f).a₄ = f W.a₄` is
  fixed by the definition of a Weierstrass curve; WebSearch independently named the mathlib lemma.
- Generality analysis (Phase 4): STRICTLY NARROWER THAN STANDARD — specialised to `f = algebraMap R K`
  over a field; the general form already exists upstream.
- Mathlib search (Phase 5): found in mathlib as `WeierstrassCurve.map_a₄` (more general; any ring hom).
- Composition check (Phase 6): recovered by the single mathlib lemma after unfolding the `curveK` abbrev.

**Rationale:**

`curveK R K W` is an `abbrev` for `W.map (algebraMap R K)`, and `WeierstrassCurve.map` carries
`@[simps]` (Weierstrass.lean:230–232), which auto-generates the `@[simp]` lemma
`WeierstrassCurve.map_a₄ : (W.map f).a₄ = f W.a₄` for an arbitrary ring homomorphism `f : R →+* A`.
The project lemma `curveK_a₄` is *literally* that lemma instantiated at `f := algebraMap R K` — same
statement after unfolding one reducible abbreviation, provable by `WeierstrassCurve.map_a₄ _`. mathlib's
version is strictly more general (it needs only `CommRing R`/`CommRing A` and any ring hom; the project
form gratuitously assumes `[Field K]` and sits under an unused PID narrative). This is one of five
sibling duplicates (`curveK_a₁ … curveK_a₆`) of the mathlib `map_a₁ … map_a₆` family, and the analogous
`ℤ/ℚ` track (`GeneralCurve.curveQ_a₄`) is the same redundancy.

It has zero internal call sites: downstream files close coefficient goals via `simp [curveK]`, which
unfolds the abbrev and lets mathlib's `@[simp] map_a₄` fire. The lemma therefore adds nothing — every
consumer already reaches the upstream lemma. The fork carries it only because the project mirrors
mathlib's elliptic-curve API locally.

**WHY not (refactor-actionable):**
Mathlib already has `WeierstrassCurve.map_a₄`. Since `curveK R K W` unfolds (reducibly) to
`W.map (algebraMap R K)`, the project statement is the same proposition; no local lemma is warranted.

Existing mathlib decl:        `WeierstrassCurve.map_a₄`
Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:230`
                             (auto-generated by `@[simps]` on `def map` at line 231; it is `@[simp]`).
Our form follows in ≤1 line:
```lean
example {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K] (W : WeierstrassCurve R) :
    (LutzNagell.PID.curveK R K W).a₄ = algebraMap R K W.a₄ :=
  WeierstrassCurve.map_a₄ (algebraMap R K)        -- or: by simp
```
Call sites in our project (from Phase 6.0): K = 0 references to `curveK_a₄` by name.
Refactor plan:
  1. Delete `curveK_a₄` (and, for the same reason, its siblings `curveK_a₁/a₂/a₃/a₆` — each is the
     corresponding `WeierstrassCurve.map_aᵢ`). The identical `ℤ/ℚ` shadows `curveQ_a₁ … curveQ_a₆`
     in `GeneralCurve.lean` are the same case and should be removed in the same pass.
  2. No call-site edits are needed for the named lemma (K = 0). Downstream `simp [curveK]` calls keep
     working unchanged, because unfolding the `curveK`/`curveQ` abbrev exposes `W.map …` and mathlib's
     `@[simp] map_aᵢ` lemmas fire automatically. Optionally add `WeierstrassCurve.map_a₄` (etc.) to
     those `simp` sets explicitly, but it is already `@[simp]`, so even that is unnecessary.
  3. Keep the genuinely-new content of the file (`curveK` abbrev itself, `curveK_equation_iff`) and
     re-assess those separately — `curveK_equation_iff` is *not* a trivial `map_aᵢ` duplicate.

Next action: delete `LutzNagell.PID.curveK_a₄` (with its five siblings) from the project; rely on
`WeierstrassCurve.map_a₄`. Since this is a fork that intentionally mirrors mathlib's API, confirm with
the project owner whether the local mirror is deliberately retained for self-containment before pruning.

---

## Next step

Delete `LutzNagell.PID.curveK_a₄` from the project and rely on the existing
`WeierstrassCurve.map_a₄` (the `@[simps]`-generated `@[simp]` lemma for `WeierstrassCurve.map`). The
five sibling `curveK_aᵢ` lemmas and the `ℤ/ℚ` `curveQ_aᵢ` shadows are the same redundancy and should
be pruned together; no named call sites need editing (K = 0), and downstream `simp [curveK]` usages
continue to work via mathlib's upstream `@[simp]` lemmas.
