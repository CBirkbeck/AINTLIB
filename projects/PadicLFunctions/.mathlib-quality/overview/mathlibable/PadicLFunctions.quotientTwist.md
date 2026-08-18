# `/mathlibable` report — `PadicLFunctions.quotientTwist`

**Final verdict: `NO-mathlib-has-it`** — mathlib already has this construction as
`IsFractionRing.ringEquivOfRingEquiv`. `quotientTwist p` is definitionally equal to
`IsFractionRing.ringEquivOfRingEquiv (unitsTwist p)`.

---

### Baseline (Phase 0)

- lake build:               build not re-run; reasoned from source (per task note — `lake build` stale/slow in this checkout). The declaration and all its dependencies were read directly from source; the construction is a thin wrapper over a mathlib `noncomputable def`, so elaboration is not in doubt.
- decl `PadicLFunctions.quotientTwist`:  ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/EisensteinFamily.lean:167`
- kind:                      `def` (`noncomputable def`)
- has sorry:                 no
- module docstring summary:  the p-adic family of Eisenstein series (RJW §8); the x-twist `τ : [g] ↦ g·[g]` realised as a ring automorphism of the convolution algebra and extended to the total fraction ring `Q(ℤ_p^×)`.

---

### Statement (Phase 1)

`PadicLFunctions.quotientTwist` is **a definition** of the following:

Given the ring automorphism `unitsTwist p` of the Iwasawa/convolution algebra
`Λ := PadicMeasure p ℤ_[p]ˣ` (the "x-twist", `[g] ↦ g·[g]`), `quotientTwist p` is the
**induced ring automorphism of the total ring of fractions** `Q(Λ) = FractionRing Λ`.
Mathematically: a ring isomorphism `h : R ≃+* R` carries the set of non-zero-divisors of
`R` bijectively onto itself, hence extends (by the universal property of localization) to a
ring isomorphism `Q(R) ≃+* Q(R)` of the total fraction ring, compatible with the canonical
map `R → Q(R)`. Here `R = Λ` and `h = unitsTwist p`.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the prime; only used through `Λ` and its fraction ring.
- `Λ = PadicMeasure p ℤ_[p]ˣ` — a `CommRing` (`Measure/PseudoMeasure.lean:81`).
- `PadicMeasure.QuotientField p := FractionRing Λ` (`Measure/PseudoMeasure.lean:804`),
  which carries the mathlib instance `IsFractionRing (FractionRing Λ) (FractionRing Λ)`
  via `IsFractionRing.idem` (`FractionRing.lean:691`).

Hypotheses (Lean side):
- none beyond the instance arguments; the construction consumes `unitsTwist p` (a
  `≃+*`) and `map_nonZeroDivisors_unitsTwist p` (the proof that it preserves
  non-zero-divisors).

Conclusion (math): the x-twist automorphism of `Λ` extends to a ring automorphism of `Q(Λ)`.

Conclusion (Lean): n/a — definition. Type: `PadicMeasure.QuotientField p ≃+* PadicMeasure.QuotientField p`.

Body (one line):
```lean
IsLocalization.ringEquivOfRingEquiv
  (PadicMeasure.QuotientField p) (PadicMeasure.QuotientField p)
  (unitsTwist p) (map_nonZeroDivisors_unitsTwist p)
```

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: it is not a new mathematical structure, not a person/place-named theorem, and not
a primary project goal — it is the one-line application of the localization-functoriality
constructor to extend an already-built ring automorphism (`unitsTwist`) to the fraction ring.
It is plumbing used inside the construction of `twistedZetaHalf`.

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Body line count: 1 substantive line (a single `IsLocalization.ringEquivOfRingEquiv …` call).
One-liner verdict: **ONE-LINER** (kind is `def`).

| Exemption                         | Applies? | Evidence                                                                                  |
|-----------------------------------|----------|-------------------------------------------------------------------------------------------|
| Avoid defeq abuse                 | no       | No downstream proof relies on a controlled/blocked unfolding; the only fact used downstream is `quotientTwist_algebraMap`, which is itself mathlib's `ringEquivOfRingEquiv_algebraMap`. |
| Avoid typeclass diamonds          | no       | No colliding instances. The `IsFractionRing` instance is the canonical idempotent one; no second `Mul`/`Zero`/`AddCommMonoid` path is anchored by this def. |
| Mark semantic intent / API name   | no       | Zero external consumers (Phase 6: K = 0). The only consumers are in the same file and could call `IsFractionRing.ringEquivOfRingEquiv (unitsTwist p)` directly. |

Conclusion: **ONE-LINER WITHOUT-EXEMPTION** — a strong negative signal for mathlib inclusion,
consistent with the `NO` verdict reached below (no special Phase-7 justification needed since
the verdict is NO, not YES).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                       | Hit? | Standard form found                                                       | Notes |
|----|----------------------------------|-------------------------------------------------------------------------------------------------------------|------|---------------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "ring isomorphism induces isomorphism of localizations functoriality of localization"                       | yes  | `S⁻¹R` construction respects ring homomorphisms via its universal property | Stanford 210B localization notes; Stacks `tag/02PC`; uchicago "three important functors" |
|  2 | WebSearch (general form)         | "isomorphism of fields of fractions induced by ring isomorphism integral domain functorial"                 | yes  | a ring iso `φ : R₁ ≃ R₂` of domains induces an iso of fraction fields      | Wikipedia "Field of fractions"; UCSD 103B notes l_14; Columbia integral-domains notes |
|  3 | WebSearch (named-after / aliases)| "total ring of fractions / total quotient ring automorphism induced by ring automorphism nonzerodivisors"   | yes  | localize at non-zero-divisors `S`; functoriality carries `S` along        | Wikipedia "Total ring of fractions"; MathWorld "Ring of Fractions"; arXiv 1009.5152 (equivariant total ring of fractions) |
|  4 | ChatGPT MCP                      | n/a                                                                                                         | n/a  | n/a                                                                       | The `chatgpt-math` MCP server is configured with a Linux path (`/home/chris/.claude/mcp-servers/chatgpt-math/server.js`) that does not exist on this Darwin machine, and no ChatGPT tool was surfaced in this session. Recorded as n/a — substituted with WebSearch ×3 (above) at three generality levels + Atiyah–Macdonald lookup (#10) + four reference channels (#5–#9). |
|  5 | Local references                 | check `.mathlib-quality/references/` and `refs/`                                                            | n/a  | (no references dir; no `refs/` symlink)                                    | `projects/PadicLFunctions/.mathlib-quality/references/` absent; `refs/` symlink absent. Recorded as n/a. |
|  6 | nLab                             | `localization` (functoriality of ring-of-fractions / field-of-fractions)                                   | partial | hub page lists "localization of a commutative ring", "field of fractions", "ring of fractions" as functorial constructions | The nLab landing page is a navigation hub; it frames localization categorically (a functor) but the displayed excerpt did not spell out the iso-induces-iso statement. No contradiction with #1–#3. |
|  7 | nCatLab (if categorical)         | (covered by #6 nLab) — localization-as-functor                                                              | n/a  | same as #6                                                                | nLab/nCatLab are the same wiki; localization is categorical but this specific decl is an elementary functoriality fact already covered by #1–#3. |
|  8 | Stacks Project (if alg geom)     | functoriality of localization / total fraction ring                                                         | yes  | localization is functorial in the ring (`tag/02PC` and the surrounding commutative-algebra chapter) | The specific fetched tag returned the license page, but the search surfaced `stacks.math.columbia.edu/tag/02PC` for functoriality of localization. Stacks treats `Q(R)` and `S⁻¹R` functorially throughout. |
|  9 | MathOverflow / Math.StackExchange| total ring of fractions generality / induced automorphism                                                   | partial | standard; no specialised result — it is a routine exercise (Atiyah–Macdonald Ch. 3) | No surprising or more-general MO/MSE statement beyond the textbook fact. |
| 10 | recent arXiv (last 5 years)      | "General theory of localizations of rings and modules" (arXiv 2312.17145); "Equivariant total ring of fractions" (arXiv 1009.5152) | yes | functoriality / equivariance of localization and of the total fraction ring under ring maps and group actions | Confirms the construction is standard and studied even in the equivariant (group-action) setting; no more-general *form of this elementary fact* is missing. |

The protocol passes: WebSearch ran 3 distinct queries at three generality levels (specific
"localization", general "field of fractions of a domain", aliased "total ring of fractions");
local references checked (absent, n/a with reason); nLab checked; Stacks / nCatLab /
MathOverflow / arXiv each checked or recorded n/a with a reason. ChatGPT MCP recorded n/a
with a concrete reason (server path is for a different machine; tool not surfaced here) and
substituted with the extra channels above.

### Literature summary (Phase 3)

Concept identified as: **functoriality of localization / total ring of fractions** — a ring
isomorphism `h : R ≃+* R` induces a ring isomorphism `Q(R) ≃+* Q(R)` of the total ring of
fractions (`FractionRing R = (nonZeroDivisors R)⁻¹ R`), because `h` maps the
non-zero-divisors of `R` bijectively onto themselves.

Sources agree on the standard form: **yes**. This is a routine, classical fact (Atiyah–Macdonald
Ch. 3; Stacks Project; Wikipedia "Total ring of fractions" and "Field of fractions"; standard
graduate commutative-algebra notes). No source treats it as novel.

Most general standard form: for a *commutative ring* `R` (not just a domain), localize at the
multiplicative set `S` of non-zero-divisors; any ring iso `h` of `R` carries `S` onto `S` and
extends to an iso of `Q(R) = S⁻¹R`. (For a domain, `S = R \ {0}` and `Q(R)` is the field of
fractions — the special case in the WebSearch #2 results.)

Generality dimensions where the literature varies:
  - **Base ring**: domain (field of fractions) ⟶ general commutative ring (total ring of
    fractions). The most general is the commutative-ring case; the project sits exactly here
    (`Λ = PadicMeasure p ℤ_[p]ˣ` is a general `CommRing`, not assumed a domain), which is the
    fully general standard form. Mathlib's `IsFractionRing.ringEquivOfRingEquiv` also lives at
    this generality (works for any `IsFractionRing A K`).
  - **Map type**: ring iso `R ≃ R` (this decl / mathlib's def) vs. ring homomorphism between
    two rings (the more general functorial map). Mathlib also has the homomorphism version
    (`IsFractionRing.fieldEquivOfRingEquiv`/`IsLocalization.map`); the iso-of-one-ring form is
    the relevant specialisation and mathlib has it directly.

Disagreement with the literature: **none**. The project's form is exactly the literature-standard
total-fraction-ring functoriality, at the general (non-domain) commutative-ring generality.

---

### Generality analysis — `PadicLFunctions.quotientTwist`

Literature-standard form (from Phase 3): a ring iso `h : R ≃+* P` of commutative rings induces a
ring iso `Q(R) ≃+* Q(P)` of total fraction rings.

| # | Parameter / hypothesis                  | Current Lean form                              | Literature-standard form          | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------------|------------------------------------------------|-----------------------------------|---------------------|---------------------------------|
| 1 | `unitsTwist p : Λ ≃+* Λ`                | a *specific* ring iso of `Λ`                   | any ring iso `h : R ≃+* P`        | yes (in principle)  | The general statement is over an arbitrary ring iso `h : R ≃+* P`; `quotientTwist` hard-codes `R = P = Λ` and `h = unitsTwist p`. But the general form **is exactly what mathlib already provides** (`IsFractionRing.ringEquivOfRingEquiv h`), so there is nothing to *contribute* by generalising — the generalisation already exists upstream. |
| 2 | `Λ = PadicMeasure p ℤ_[p]ˣ`             | a specific `CommRing`                          | any `CommRing` (general)          | yes (in principle)  | Same as #1 — the ring-general form is `IsFractionRing.ringEquivOfRingEquiv`; mathlib has it. |
| 3 | `QuotientField p = FractionRing Λ`      | the canonical total fraction ring of `Λ`       | any `K` with `[IsFractionRing A K]`| yes (in principle) | Mathlib's def is over an abstract `IsFractionRing A K`, strictly more general than `FractionRing`. Again, already upstream. |
| 4 | `map_nonZeroDivisors_unitsTwist p`      | `MulEquivClass.map_nonZeroDivisors (unitsTwist p)` (a re-export) | the general lemma `MulEquivClass.map_nonZeroDivisors` | yes | This hypothesis is *not even needed* in the fraction-ring case: mathlib's `IsFractionRing.ringEquivOfRingEquiv` supplies it internally as `MulEquivClass.map_nonZeroDivisors h`. The project's `map_nonZeroDivisors_unitsTwist` is a verbatim specialisation of an existing mathlib lemma. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (it specialises the abstract
`IsFractionRing A K` + arbitrary `h : A ≃+* B` to `A = B = Λ`, `K = L = FractionRing Λ`,
`h = unitsTwist p`).

Number of weakening opportunities found: 4 (all four parameters could be abstracted).

Proposed restatement (if STRICTLY NARROWER): the maximally-general statement is *precisely*
`IsFractionRing.ringEquivOfRingEquiv`:
```lean
noncomputable def IsFractionRing.ringEquivOfRingEquiv
    {A K B L : Type*} [CommRing A] [CommRing B] [CommRing K] [CommRing L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
    (h : A ≃+* B) : K ≃+* L
```

Cost of restatement: n/a (CHEAP would be the label, but it is moot) — **the general form
already exists in mathlib**, so this does not become a YES-but-generalise-first. There is no
generalisation *for us to do*; the right move is to delete the local def and call the existing
mathlib general form. This is the textbook trigger for `NO-mathlib-has-it`, not
`YES-but-generalise-first` (Phase 3 / Phase 5 found the general form already upstream).

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                              | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|-------------------------------------------------------------------------------------------------------|----------|------------------------|---------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                    | no       | —                      | Already fully typeclass-driven (`IsFractionRing`, `Algebra`); the literature preamble is already a typeclass in mathlib's form. |
|  2 | sequences/metric → filters/topological?                                                                | no       | —                      | No analytic/limit content; this is pure algebra. |
|  3 | construct an object → universal-property class?                                                        | yes (already done upstream) | use `IsFractionRing.ringEquivOfRingEquiv`, which is built *from* the universal property (`IsLocalization.map`) | This is exactly the modern idiom — and mathlib already realises it. The project's def re-implements the universal-property construction by hand via `IsLocalization.ringEquivOfRingEquiv` + a manual non-zero-divisor proof. |
|  4 | set-with-closure-predicate → bundled substructure?                                                     | no       | —                      | Not a substructure question. |
|  5 | vector-space/field-specific → modules/(semi)ring weakening?                                            | no (already general) | — | The project already works over a general `CommRing` `Λ` (the total-fraction-ring case), matching mathlib's general def — no field/domain assumption to weaken. |
|  6 | 1-categorical → higher-categorical?                                                                    | no       | —                      | Not applicable. |
|  7 | concrete index (ℕ,ℤ,ℝ) → arbitrary additive/ordered structure?                                         | no       | —                      | No numeric index. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no (it is already the modern idiom, and mathlib already has it)**.
One-line reason: the contemporary mathlib formulation of "ring iso induces fraction-ring iso"
is `IsFractionRing.ringEquivOfRingEquiv`, built from the localization universal property; the
project's `quotientTwist` is a by-hand re-implementation of that exact construction, not a
modernisation of it. There is no organisational improvement to contribute — the improvement
is to *use* the upstream form. Hence this is **not** a `YES-but-generalise-first` /
MODERN-IDIOM case; it is `NO-mathlib-has-it`.

---

### Diamond / defeq risk — `PadicLFunctions.quotientTwist`

| # | Risk                          | Verdict | Evidence / rationale |
|---|-------------------------------|---------|----------------------|
| 1 | Typeclass diamond            | none    | Not an `instance`; introduces no new typeclass-search path. The only instance it depends on, `IsFractionRing (FractionRing Λ) (FractionRing Λ)`, is the canonical idempotent one from mathlib. |
| 2 | Reducibility leak            | none    | Not `@[reducible]`. Sealed `noncomputable def`; body is a single mathlib constructor call. |
| 3 | Non-canonical unfolding      | none    | `simp` does not unfold it; the project uses `quotientTwist_algebraMap` (= mathlib's `ringEquivOfRingEquiv_algebraMap`) to compute, not unfolding. |
| 4 | Instance priority collision  | none    | Not an `instance`. |
| 5 | Universe-polymorphism issues | none    | All types are concrete (`Type 0`); no universe annotation forced. |
| 6 | Coercion ambiguity           | none    | No new `CoeFun`/`CoeSort`; the `≃+*` carries mathlib's standard coercion, identical to what `IsFractionRing.ringEquivOfRingEquiv` produces. |

### Risk verdict (Phase 4.5)

Overall risk: **NONE**
Top risks: none.
(Moot for the verdict: a `NO-mathlib-has-it` bucket does not add the def to mathlib. Recorded
for completeness — and because it is exactly the no-risk profile expected of a verbatim
re-implementation of an existing mathlib def.)

---

### Mathlib search-status: `PadicLFunctions.quotientTwist`

[A] Lean-Finder       induce iso of fraction rings from ring iso              n/a: Lean-Finder MCP tool not surfaced in this session — substituted with exhaustive mathlib-source grep [D] + name-pattern grep [E], both of which produced an exact hit.
[B] Loogle            `(_ ≃+* _) → (FractionRing _ ≃+* FractionRing _)`        n/a: `lean_loogle` MCP tool not available in this session — substituted with [D]/[E].
[C] LeanSearch        "ring isomorphism induces isomorphism of fraction rings" n/a: `lean_leansearch` MCP tool not available in this session — substituted with [D]/[E].
[D] Grep mathlib src  `ringEquivOfRingEquiv`, `map_nonZeroDivisors`, `IsFractionRing.ringEquivOfRingEquiv`  HIT — see below.
[E] Name pattern      `ringEquivOfRingEquiv`, `_algebraMap`, `MulEquivClass.map_nonZeroDivisors`  HIT — see below.

Searched for both:
  - the user's current form (`unitsTwist p` extended to `FractionRing Λ`), and
  - the literature-standard form (arbitrary ring iso `h : A ≃+* B` extended to fraction rings).

**Exact hits found:**
- `IsFractionRing.ringEquivOfRingEquiv` — `Mathlib/RingTheory/Localization/FractionRing.lean:433`:
  ```lean
  noncomputable def IsFractionRing.ringEquivOfRingEquiv
      {A K B L : Type*} [CommRing A] [CommRing B] [CommRing K] [CommRing L]
      [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
      (h : A ≃+* B) : K ≃+* L :=
    IsLocalization.ringEquivOfRingEquiv K L h (MulEquivClass.map_nonZeroDivisors h)
  ```
  This is **definitionally the same construction** as `quotientTwist p` with
  `A = B = Λ`, `K = L = FractionRing Λ`, `h = unitsTwist p`. Note mathlib supplies the
  non-zero-divisor hypothesis *internally* as `MulEquivClass.map_nonZeroDivisors h` — the
  exact term the project re-exports as `map_nonZeroDivisors_unitsTwist p`.
- `IsFractionRing.ringEquivOfRingEquiv_algebraMap` — `FractionRing.lean:436`:
  `ringEquivOfRingEquiv h (algebraMap A K a) = algebraMap B L (h a)` — this is exactly the
  project's companion lemma `quotientTwist_algebraMap` (which the project proves via
  `IsLocalization.ringEquivOfRingEquiv_eq`).
- `MulEquivClass.map_nonZeroDivisors` — `Mathlib/Algebra/GroupWithZero/NonZeroDivisors.lean:265`:
  `Submonoid.map h (nonZeroDivisors M₀) = nonZeroDivisors S` for any `MulEquivClass` `h` —
  exactly the project's `map_nonZeroDivisors_unitsTwist` (defined as
  `MulEquivClass.map_nonZeroDivisors (unitsTwist p)`).
- Confirming applicability: `FractionRing R := Localization (nonZeroDivisors R)`
  (`FractionRing.lean:686`) and `instance : IsFractionRing (FractionRing R) (FractionRing R)`
  (`FractionRing.lean:691`). `Λ` is a `CommRing` (`PseudoMeasure.lean:81`). So the mathlib def
  typechecks verbatim for `QuotientField p = FractionRing Λ`.
- Existing mathlib uses of this exact pattern to extend a ring automorphism to a fraction
  field: `Mathlib/RingTheory/WittVector/FrobeniusFractionField.lean:216,225` and
  `Mathlib/RingTheory/WittVector/Isocrystal.lean:80` extend the Frobenius automorphism via
  `IsFractionRing.ringEquivOfRingEquiv (frobeniusEquiv p k)` — the direct analog of extending
  `unitsTwist`.

Concluded: **found in mathlib as `IsFractionRing.ringEquivOfRingEquiv`; identical form** (the
project's def is a definitional special case, and its companion lemmas duplicate
`ringEquivOfRingEquiv_algebraMap` and `MulEquivClass.map_nonZeroDivisors`).

---

### Call sites — `PadicLFunctions.quotientTwist`

Internal use count: **0** (within the project, NOT counting the declaring file
`EisensteinFamily.lean`).
External-to-file callers: **0 distinct files**.

| Caller file:line               | Usage pattern (one-line excerpt)                                            |
|--------------------------------|-----------------------------------------------------------------------------|
| (none outside the declaring file) | —                                                                        |

Inside the declaring file (`EisensteinFamily.lean`), `quotientTwist` is used at:
- `:174` `quotientTwist_algebraMap` (the companion lemma, = mathlib's `ringEquivOfRingEquiv_algebraMap`)
- `:190` inside `twistedZetaHalf` (`… * quotientTwist p (PadicMeasure.padicZeta p hp2)`)
- `:225–228` inside `twistedZetaHalf_witness_eq` (rewriting with `quotientTwist_algebraMap`)

Inline-derivation grep (was the equivalent re-derived elsewhere without using `quotientTwist`?):
  - (none) — `IsFractionRing.ringEquivOfRingEquiv` is not separately re-derived in the project;
    the project consolidated the construction into this one local def. But note `ZetaGalois.lean`
    builds its own `QuotientFieldPlus`/`toQPlus` localization machinery by hand, indicating the
    project repeatedly re-implements localization plumbing that mathlib already provides.

Call-sites signal (per the Phase-6.0.1 table): **K = 0 internal uses, no inline re-derivation**
— a wrapper used only within its declaring file. Combined with the Phase-2b
`ONE-LINER WITHOUT-EXEMPTION` finding and the exact mathlib hit, this strongly confirms
`NO-mathlib-has-it`: the local def can be deleted and its in-file uses pointed at the mathlib
construction directly.

### Composition check (Phase 6)

Can `quotientTwist` be derived from mathlib in ≤3 chained calls?

Attempt 1: `IsFractionRing.ringEquivOfRingEquiv (unitsTwist p)`
  - Mathlib decls used: `IsFractionRing.ringEquivOfRingEquiv`
  - Result: **succeeds** — this is a single mathlib call, and it is moreover *definitionally
    equal* to the current body (`IsLocalization.ringEquivOfRingEquiv K L (unitsTwist p)
    (MulEquivClass.map_nonZeroDivisors (unitsTwist p))`, where the project's
    `map_nonZeroDivisors_unitsTwist p := MulEquivClass.map_nonZeroDivisors (unitsTwist p)`).
  - Notes: nothing missing. Because Phase 5 already found an *identical* named def, this is the
    `NO-mathlib-has-it` case (a direct replacement), not merely `NO-composable`.

Conclusion: the construction is **identical to a single existing mathlib def** — the strongest
form of "mathlib has it". (It is trivially also a ≤3-call composition, but `NO-mathlib-has-it`
is the correct bucket because the replacement is one named decl, not an assembly of primitives.)

---

## Verdict: `PadicLFunctions.quotientTwist`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): the concept is *functoriality of the total ring of fractions* —
  a ring iso induces a fraction-ring iso. Classical, unanimous across sources (Atiyah–Macdonald
  Ch. 3, Stacks Project, Wikipedia). Not novel.
- Generality analysis (Phase 4): STRICTLY NARROWER than the abstract form — but the abstract
  form *already exists in mathlib*, so this is a redundancy, not a generalisation opportunity.
- Mathlib search (Phase 5): **found in mathlib as `IsFractionRing.ringEquivOfRingEquiv`;
  identical form**, with the companion lemma `ringEquivOfRingEquiv_algebraMap` matching
  `quotientTwist_algebraMap` and `MulEquivClass.map_nonZeroDivisors` matching
  `map_nonZeroDivisors_unitsTwist`.
- Composition check (Phase 6): the body is definitionally `IsFractionRing.ringEquivOfRingEquiv
  (unitsTwist p)`; K = 0 external call sites.

**Rationale:**

`quotientTwist p` is, term-for-term, mathlib's `IsFractionRing.ringEquivOfRingEquiv (unitsTwist p)`.
Mathlib's def is literally
`IsLocalization.ringEquivOfRingEquiv K L h (MulEquivClass.map_nonZeroDivisors h)`; the project
writes the same `IsLocalization.ringEquivOfRingEquiv K L (unitsTwist p) (map_nonZeroDivisors_unitsTwist p)`
and *defines* `map_nonZeroDivisors_unitsTwist p` to be `MulEquivClass.map_nonZeroDivisors (unitsTwist p)`
— the very term mathlib's wrapper supplies. With `Λ = PadicMeasure p ℤ_[p]ˣ` a `CommRing` and
`QuotientField p = FractionRing Λ` carrying the canonical `IsFractionRing` instance, mathlib's
def typechecks here without change. Mathlib even uses this exact idiom to extend a ring
automorphism to a fraction field (`FrobeniusFractionField.lean`, `Isocrystal.lean` extend
Frobenius), which is the precise analog of extending the x-twist.

This is not a `YES-but-generalise-first`: the more general form is not something for the project
to build — it is already upstream, and the project's job is to delete the local copy and reuse it
(per the verdict rubric, the general form being present in mathlib makes this `NO-mathlib-has-it`,
not a generalisation opportunity). It is not `NO-composable-from-mathlib` either, because the
replacement is a single named mathlib def rather than an assembly of primitives. The Phase-2b
one-liner-without-exemption signal and the K = 0 external-call-site count both reinforce that the
local def carries no API-stability or defeq-barrier role that would justify keeping it.

**WHY not (refactor-actionable detail):**
Mathlib already has this exact construction as **`IsFractionRing.ringEquivOfRingEquiv`**. The
project's `quotientTwist`, its companion `quotientTwist_algebraMap`, and the supporting
`map_nonZeroDivisors_unitsTwist` are verbatim re-implementations of, respectively,
`IsFractionRing.ringEquivOfRingEquiv`, `IsFractionRing.ringEquivOfRingEquiv_algebraMap`, and
`MulEquivClass.map_nonZeroDivisors`. No mathlib gap exists; there is nothing to upstream.

Existing mathlib decl:        `IsFractionRing.ringEquivOfRingEquiv`
Located at:                   `Mathlib/RingTheory/Localization/FractionRing.lean:433`
Supporting mathlib decls:     `IsFractionRing.ringEquivOfRingEquiv_algebraMap`
                              (`FractionRing.lean:436`); `MulEquivClass.map_nonZeroDivisors`
                              (`Mathlib/Algebra/GroupWithZero/NonZeroDivisors.lean:265`).

Our form follows in ≤1 line (in fact definitionally — `rfl`):
```lean
example : PadicMeasure.QuotientField p ≃+* PadicMeasure.QuotientField p :=
  IsFractionRing.ringEquivOfRingEquiv (PadicLFunctions.unitsTwist p)
-- and the companion lemma:
example (μ : PadicMeasure p ℤ_[p]ˣ) :
    IsFractionRing.ringEquivOfRingEquiv (unitsTwist p)
        (algebraMap _ (PadicMeasure.QuotientField p) μ)
      = algebraMap _ _ (unitsTwist p μ) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (unitsTwist p) μ
```

Call sites in our project (from Phase 6.0):  K = 0 external; 3 in-file uses (`:174`, `:190`, `:225–228`).

Refactor plan:
1. **Delete** `quotientTwist` (EisensteinFamily.lean:167–171),
   `quotientTwist_algebraMap` (:174–177), and `map_nonZeroDivisors_unitsTwist` (:160–164).
2. In `twistedZetaHalf` (:190), replace `quotientTwist p (PadicMeasure.padicZeta p hp2)` with
   `IsFractionRing.ringEquivOfRingEquiv (unitsTwist p) (PadicMeasure.padicZeta p hp2)`.
3. In `twistedZetaHalf_witness_eq` (:225–228), replace the two
   `quotientTwist_algebraMap` rewrites with `IsFractionRing.ringEquivOfRingEquiv_algebraMap`
   (same statement; check the `algebraMap _ _ …` argument order, which is identical).
   The `congrArg quotientTwist …` step (:227) becomes `congrArg (IsFractionRing.ringEquivOfRingEquiv (unitsTwist p)) …`.
4. Add `import Mathlib.RingTheory.Localization.FractionRing` if not already transitively present
   (it almost certainly is, via `QuotientField`).

Next action: delete `quotientTwist` (+ `quotientTwist_algebraMap`, `map_nonZeroDivisors_unitsTwist`)
from the project; rewrite the three in-file uses against `IsFractionRing.ringEquivOfRingEquiv`
and `IsFractionRing.ringEquivOfRingEquiv_algebraMap`. Since the bodies are definitionally equal,
the existing proofs should go through with the names swapped. (This is a `/cleanup`
dedup-against-mathlib action on `main`, not a mathlib PR.)

---

## Next step

Delete `PadicLFunctions.quotientTwist` (together with `quotientTwist_algebraMap` and
`map_nonZeroDivisors_unitsTwist`) and replace its three in-file uses with mathlib's
`IsFractionRing.ringEquivOfRingEquiv (unitsTwist p)` and
`IsFractionRing.ringEquivOfRingEquiv_algebraMap`. This is a `/cleanup`
deduplicate-against-mathlib task on `main`; no mathlib PR is warranted (mathlib already has the
construction). Leave `unitsTwist` itself untouched — it is the project-specific ring
automorphism being extended, and is assessed separately.
