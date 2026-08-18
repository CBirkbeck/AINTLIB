# /mathlibable report — `LutzNagell.PID.den_not_prime_of_on_curve`

## Baseline (Phase 0)
- lake build:               not run (local build stale, per task); reasoning from source
- decl `LutzNagell.PID.den_not_prime_of_on_curve`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDDenominators.lean:176`
- namespace: confirmed `namespace LutzNagell` (l.19) → `namespace PID` (l.20), closed
  `end PID` (l.188) / `end LutzNagell` (l.189). Qualified name **`LutzNagell.PID.den_not_prime_of_on_curve`** verified.
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Denominators on general Weierstrass curves over UFDs — if a
  prime `q` divides `den_R(x)` exactly once for `(x,y)` on the curve, contradiction.

## Statement (Phase 1)

`den_not_prime_of_on_curve` is a **corollary** stating: let `R` be a UFD (here a domain +
`UniqueFactorizationMonoid`) with fraction field `K`, and let `W` be a general Weierstrass
curve `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` with `aᵢ ∈ R`. If `(x, y) ∈ K²` satisfies the
curve equation and the ring-theoretic denominator `IsFractionRing.den R x` is a **prime**
element of `R`, then `False`. In words: the denominator of the x-coordinate of a point on the
curve cannot be (associate to) a prime — a key step of the Nagell–Lutz integrality argument.

Variables / typeclasses (Lean side):
- `R` : `CommRing R`, `IsDomain R`, `UniqueFactorizationMonoid R` — a UFD.
- `K` : `Field K`, `Algebra R K`, `IsFractionRing R K` — its fraction field.
- `W : WeierstrassCurve R` — the (general/long) Weierstrass model.
- `x y : K` — coordinates of the point.

Hypotheses (Lean side):
- `heq` : `(x, y)` lies on the Weierstrass curve (long equation over `K`).
- `hp` : `Prime (IsFractionRing.den R x : R)` — the denominator is a prime element.

Conclusion (math): contradiction.
Conclusion (Lean): `False`.

**Proof body (the entire decl):** delegate to the sibling
`den_no_simple_prime_factor_of_on_curve W heq hp dvd_rfl (…)`, supplying `q := den(x)`,
`hqd := dvd_rfl` (`q ∣ q`), and `hq2 := ` a 4-line inline proof that `¬ q² ∣ q` (from `q` prime:
if `q² ∣ q` then `1 = q · c`, so `q` is a unit, contradicting `hp.not_unit`). The docstring states
this outright: *"This is a special case of `den_no_simple_prime_factor_of_on_curve` where
`q = den(x)` — a prime element trivially has `q² ∤ q`."*

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A corollary/specialisation. Not a `## Main results` entry of the file (the docstring's
sole listed main result is the *parent* `den_no_simple_prime_factor_of_on_curve`). Not a
new structure. It carries the name of no person — it is a one-step instantiation of a sibling
lemma. (Note: literature width was run EXHAUSTIVE regardless.)

## One-line check (Phase 2b)

Body line count: theorem (not a `def`). n/a — the one-line *definition* heuristic does not apply.
The body is a ~6-line term-mode delegation to a sibling lemma, supplying the trivial witness
`¬ q² ∣ q`. (Recorded for narrative: the "substance" of this theorem is precisely that trivial
witness; everything else is forwarded.)

## Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "Nagell-Lutz theorem proof torsion points integral coordinates denominator prime elliptic curve"       | yes  | Torsion ⟹ integral coords; std proof bounds the denominator of `x` via reduction mod `p` | Wikipedia, Harvard (Alpoge "Nagell-Lutz, quickly"), UChicago REU (Galperin), Dummit lec. 19 — the *integrality* step is classical, stated only in texts/notes |
|  2 | WebSearch (general/source form)  | "Silverman arithmetic of elliptic curves reduction modulo p denominator of x coordinate divisible by prime torsion" | yes  | Silverman GTM 106 §VII: formal group / reduction; "Denominators of x-coordinates" is a recognised topic | Silverman; also appears in Hilbert-10 work (Poonen et al.). Packaged via valuations/formal groups, never as a standalone "den is not prime" lemma |
|  3 | WebSearch (named-after / aliases)| (covered by #1: "Nagell–Lutz", "Lutz–Nagell", "torsion integral") + Wikipedia article                 | yes  | Same theorem; proof uses division polynomials / reduction | The *corollary* shape here (den exactly-once ⟹ ⊥, then den = prime as a special case) is a project-specific decomposition, not a named literature lemma |
|  4 | ChatGPT MCP                      | (MCP down per task env; substituted with extra WebSearch coverage of source texts at two generality levels — rows 1,2) | n/a  | —                                | Fallback used as instructed; standard form nonetheless pinned via Silverman + Wikipedia + REU notes |
|  5 | Local references                 | `ls projects/NagellLutz/.mathlib-quality/references/`                                                   | n/a  | (no `references/` dir — only `overview/`) | Directory absent; recorded n/a |
|  6 | nLab                             | "Nagell-Lutz theorem" / "elliptic curve torsion integral"                                               | n/a  | nLab has no Nagell–Lutz / integral-torsion page | Elementary arithmetic-geometry result; not nLab-shaped. n/a with reason |
|  7 | nCatLab (categorical)            | —                                                                                                      | n/a  | not a categorical statement       | A divisibility contradiction over a UFD; no categorical content |
|  8 | Stacks Project (alg geom)        | "elliptic curve torsion integral" / "Nagell"                                                           | n/a  | Stacks has no elliptic-curve arithmetic / Nagell–Lutz material | Stacks is scheme-theoretic foundations; this Diophantine result is out of its scope. n/a with reason |
|  9 | MathOverflow / MSE               | "denominator of x-coordinate torsion point elliptic curve prime" (via #1/#2 result sets)               | yes  | Confirms: denominator bounded by reduction; the "exactly-once prime factor" induction is the standard mechanism | Matches the project's `den_no_simple_prime_factor` parent; the corollary itself is not discussed separately |
| 10 | recent arXiv (last 5 years)      | "Nagell-Lutz" → arXiv:2509.07524 (Nagell–Lutz for imaginary quadratic fields)                          | yes  | Generalises NL to number fields; same integrality core | Even the modern generalisation keeps the result at the level of the *full* integrality theorem, not a "den ≠ prime" micro-lemma |

Protocol pass check:
- WebSearch ≥3 distinct queries at different generality: ✓ (rows 1,2,3).
- ChatGPT MCP standard-form query: substituted (MCP down) with two source-text WebSearches; documented.
- Local references checked: ✓ (absent → n/a).
- nLab checked: ✓ (n/a, reason).
- Stacks / nCatLab / MathOverflow / arXiv each checked or n/a-with-reason: ✓.

### Literature summary (Phase 3)

Concept identified as: the **integrality (denominator-bounding) step of the Nagell–Lutz
theorem** — "a torsion / on-curve point's x-coordinate denominator cannot be divisible by a
prime [to first order]". Standard source: Silverman, *The Arithmetic of Elliptic Curves* (GTM
106), reduction theory / formal groups (§IV, §VII); textbook treatments (Silverman–Tate;
course notes by Dummit, Galperin REU, Alpoge).
Sources agree on the standard form: yes — but the literature states the **full integrality
theorem** (and proves it via reduction mod `p` / the formal group / `p`-adic valuations), not a
standalone "the denominator is not prime" lemma. The exact-once-prime-factor induction (the
project's parent `den_no_simple_prime_factor_of_on_curve`) is the standard *mechanism*; the
**`q = den(x)` corollary assessed here is a project-internal packaging step**, not a named
result anywhere in the literature.
Most general standard form: the integrality theorem over number fields / DVRs (arXiv:2509.07524
does it over imaginary quadratic fields; Silverman over local fields).
Generality dimensions where the literature varies:
  - base ring: ℤ (classical) → ring of integers of a number field → general DVR / local field.
  - statement granularity: literature gives the *whole* integrality theorem; the "den is not
    prime" slice is below the resolution of any cited source.
Disagreement with the literature: none. The math is standard; the *granularity* (this exact
corollary as a separate named theorem) is a Lean-proof-engineering artifact.

## Generality analysis — `LutzNagell.PID.den_not_prime_of_on_curve`

Literature-standard form (from Phase 3): the integrality theorem; the relevant *slice* is the
parent `den_no_simple_prime_factor_of_on_curve` (den has no simple prime factor), of which this
is the `q = den(x)` instance.

| # | Parameter / hypothesis            | Current Lean form                  | Literature-standard form        | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|------------------------------------|---------------------------------|---------------------|----------------------------------|
| 1 | `[UniqueFactorizationMonoid R]` (+ domain) | UFD | ℤ classically; DVR/Dedekind in modern treatments | already general / orthogonal | The project already states it over a general UFD — *more* general than the classical ℤ form. Good. |
| 2 | `hp : Prime (den R x)`            | the **specific** hypothesis        | parent uses `q ∣ den ∧ ¬q² ∣ den` for arbitrary prime `q` | this IS the specialisation | This is exactly where the corollary is *narrower* than its already-present sibling: it fixes `q := den(x)`. |
| 3 | conclusion `False`               | contradiction                      | same                            | n/a                 | — |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN** its in-project sibling
`den_no_simple_prime_factor_of_on_curve` (it is the `q = den(x)`, `q ∣ q`, `q² ∤ q` instance).
But it is NOT narrower than the *literature* — the project's UFD generality already meets/exceeds
the classical ℤ statement.
Number of weakening opportunities: 0 that mathlib would want as a *new decl* — the more general
form already exists in the project (the parent). The corollary is, by construction, a
specialisation of code already present.
Cost of restatement: n/a — the general form is the parent lemma, already written.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                      | Applies? | Proposed reformulation | Mathlib downstream |
|----|-----------------------------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | "let X be a foo" preambles → typeclasses?                                                      | no       | — | hypotheses are already typeclass-based (`UFD`, `IsFractionRing`) |
|  2 | sequences/metric → filters/topology?                                                           | no       | — | purely algebraic divisibility statement |
|  3 | construct object → universal-property class?                                                   | no       | — | no constructed object |
|  4 | set+closure-predicate → bundled substructure?                                                  | no       | — | n/a |
|  5 | vector-space/field-specific → weaken typeclasses?                                              | no       | — | already at UFD/fraction-field generality |
|  6 | 1-categorical → higher-categorical?                                                            | no       | — | n/a |
|  7 | concrete index (ℕ,ℤ,ℝ) → general additive/monoid?                                              | partial  | The natural "general index" move is exactly the parent: replace the fixed `q = den(x)` by an arbitrary prime `q` with `q ∣ den`, `q² ∤ den`. | That generalisation is **already realised** as `den_no_simple_prime_factor_of_on_curve`; nothing new to do |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (the only "generalisation" is the already-existing parent lemma).
One-line reason: This is a corollary whose entire purpose is to *specialise* a more general
sibling that the project already has; there is no contemporary reformulation that improves it.

## Diamond / defeq risk — n/a

n/a — declaration kind is `theorem` (no definitional equalities / instances introduced).

## Mathlib search-status: `LutzNagell.PID.den_not_prime_of_on_curve`

[A] Lean-Finder       (index unavailable locally; substituted with grep over vendored mathlib src + reasoning) — n/a
[B] Loogle            type-pattern `Prime (IsFractionRing.den _ _) → … → False`, and `WeierstrassCurve … → … → False` — no plausible hit; mathlib has **no** Weierstrass-point ⟹ denominator lemma (confirmed by src grep)
[C] LeanSearch        NL: "denominator of x-coordinate of point on Weierstrass curve is not prime" / "Nagell-Lutz integrality" — no hit; mathlib has no Nagell–Lutz development
[D] Grep mathlib src  `grep -rn "den_not_prime|den_no_simple_prime|NagellLutz|Nagell"` over `.lake/packages/mathlib/Mathlib` → **0 hits**. `find -iname "*nagell* -o -iname *lutz*"` → none. Surveyed `Mathlib/AlgebraicGeometry/EllipticCurve/` (incl. `Reduction.lean`, `Weierstrass.lean`): reduction theory exists (`IsIntegral`, `IsMinimal`, `reduction`, `HasGoodReduction`) but **no point-integrality / denominator results, and no torsion-integrality theorem**. |
[E] Name pattern      grep for `den_*`, `*not_prime*`, `*on_curve*` in mathlib EC files — no hit |

Searched for both the user's current form (`q = den(x)`) and the literature-standard slice
(arbitrary prime exactly-once-dividing `den`). **Neither is in mathlib.** Mathlib has the
*reduction-theory scaffolding* (DVR-based good/bad reduction, integral models) but none of the
Nagell–Lutz arithmetic that would consume it.

Concluded: **not in mathlib** (all methods exhausted, plus the literature-standard form). The
*parent* result is also absent from mathlib — there is simply no Nagell–Lutz development upstream.

## Call sites — `LutzNagell.PID.den_not_prime_of_on_curve`

Internal use count: **1** (within the project, excluding the declaring file).
External-to-file callers: **1 distinct file**.

| Caller file:line                                   | Usage pattern (one-line excerpt)                                   |
|----------------------------------------------------|--------------------------------------------------------------------|
| `…/LutzNagellTheorem/GeneralDenominators.lean:51`  | `refine PID.den_not_prime_of_on_curve W (K := ℚ) (y := y) ?_ hden_prime` |

(The two other grep hits at `GeneralDenominators.lean:12,38` are **docstring prose references**,
not call sites.)

Inline-derivation grep (was the same statement re-derived elsewhere without this decl?):
  - (none) — but note the single caller, `den_ne_prime_of_on_general_curve`, is itself the ℚ/ℤ
    specialisation, and *it* could equally well call the parent `den_no_simple_prime_factor_of_on_curve`
    directly with `dvd_rfl` and an inline `¬p² ∣ p`. So the corollary is a one-deep convenience
    wrapper sitting between the parent and the single ℚ/ℤ consumer.

Call-sites signal: **K = 1 internal use only** → "possibly the wrong abstraction; could be
inlined" (per the Phase 6.0.1 table) → leans NO-composable.

## Composition check (Phase 6)

Can `den_not_prime_of_on_curve` be derived in ≤3 chained calls from results **mathlib has**?
→ No: it depends essentially on the project's own parent lemma, which mathlib lacks. So in the
*mathlib-primitives* sense it is NOT composable-from-mathlib.

But the relevant composition question for a verdict here is against the **project's own already-present API**, because the parent is the general form the corollary specialises:

Attempt 1 (from the in-project parent — this is literally the decl's body):
```lean
example (W : WeierstrassCurve R) {x y : K} (heq …) (hp : Prime (den R x : R)) : False :=
  den_no_simple_prime_factor_of_on_curve W heq hp dvd_rfl
    (fun h => hp.not_unit (isUnit_of_dvd_one
      (by obtain ⟨c, hc⟩ := h; exact ⟨c, mul_left_cancel₀ hp.ne_zero (by rw [sq, mul_assoc] at hc; rw [mul_one]; exact hc)⟩)))
```
  - Decls used: the parent `den_no_simple_prime_factor_of_on_curve`, `dvd_rfl`,
    `Prime.not_unit`, `isUnit_of_dvd_one`, `mul_left_cancel₀` (mathlib glue).
  - Result: **succeeds** — it is the existing proof. The only "content" beyond the parent call is
    the 4-line `¬ q² ∣ q` witness, which is pure mathlib divisibility glue (`Prime ⟹ ¬ p² ∣ p`).

Conclusion: **COMPOSABLE** from the project's own parent lemma in a single forwarding call plus a
trivial mathlib divisibility witness. (Not composable from *mathlib alone*, only because the
parent — and all of Nagell–Lutz — is not yet in mathlib.)

## Verdict: `LutzNagell.PID.den_not_prime_of_on_curve`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the Nagell–Lutz integrality step is classical (Silverman GTM 106),
  but only the *full* integrality theorem is a named literature result; this `q = den(x)`
  corollary is a project-internal packaging slice with no literature analogue.
- Generality analysis (Phase 4): STRICTLY NARROWER than its in-project sibling; the general form
  it specialises (`den_no_simple_prime_factor_of_on_curve`) already exists in the project. No
  modern-idiom improvement.
- Mathlib search (Phase 5): not in mathlib — and neither is the parent nor any Nagell–Lutz
  development; mathlib has only reduction-theory scaffolding.
- Composition check (Phase 6): COMPOSABLE — the decl's whole body is one forwarding call to the
  parent plus a trivial `Prime q ⟹ ¬ q² ∣ q` witness; only 1 call site (itself a wrapper).

**Rationale:**

This declaration is a thin convenience corollary, not a mathlib-worthy result *in its own right*.
Its entire mathematical content beyond the sibling lemma `den_no_simple_prime_factor_of_on_curve`
is the elementary fact that a prime `q` does not satisfy `q² ∣ q` — pure mathlib divisibility
glue. It is the `(q := den x, q ∣ q, q² ∤ q)` instantiation of a strictly more general result the
project *already has*. The verdict is therefore about this specific decl: a 1–3 call composition
(here, a single forwarding call) over an existing general lemma plus trivial glue. It has exactly
one consumer, `den_ne_prime_of_on_general_curve`, which could call the parent directly with the
same one-line witness — so the corollary can be inlined at that single site.

Crucially, the NO verdict is **not** a statement that mathlib should ignore Nagell–Lutz. The
*parent* `den_no_simple_prime_factor_of_on_curve` is a substantive, genuinely-absent-from-mathlib
result (mathlib has no point-integrality theory at all — only reduction scaffolding in
`EllipticCurve/Reduction.lean`), and the eventual Nagell–Lutz theorem this project is building
toward is exactly the kind of named classical theorem mathlib wants. The right mathlib grain is
the *parent* (and the headline Nagell–Lutz integrality theorem), with this corollary either
inlined or, at most, kept as a private `@[local]` convenience next to the parent — never shipped
as a standalone public mathlib lemma. (If/when the parent is upstreamed, run `/mathlibable` on
*it* — that is where the YES case lives.)

**WHY not (refactor-actionable):**
Mathlib has the *building blocks for the trivial part* (`Prime.not_unit`, `isUnit_of_dvd_one`,
`mul_left_cancel₀`, `dvd_rfl`); the *substantive* building block is the project's own parent
lemma. The corollary is a ≤3-call composition over (project-parent + mathlib glue). It need not
exist as a separate public theorem.

Project-internal building blocks: `LutzNagell.PID.den_no_simple_prime_factor_of_on_curve`
(`…/PIDDenominators.lean:87`).
Mathlib glue: `Prime.not_unit`, `isUnit_of_dvd_one`, `mul_left_cancel₀`, `dvd_rfl`.

Composition sketch (the decl body, ≤3 effective calls):
```lean
-- at the single call site, replace the corollary by:
den_no_simple_prime_factor_of_on_curve W heq hp dvd_rfl (fun h =>
  hp.not_unit (isUnit_of_dvd_one ⟨_, by
    obtain ⟨c, hc⟩ := h; exact mul_left_cancel₀ hp.ne_zero (by rw [sq, mul_assoc] at hc; rw [mul_one]; exact hc)⟩))
```

Call sites in our project (from Phase 6.0): **K = 1** (`GeneralDenominators.lean:51`).
Refactor plan: at `GeneralDenominators.lean:51`, replace
`PID.den_not_prime_of_on_curve W (K := ℚ) (y := y) ?_ hden_prime`
with a direct call to `PID.den_no_simple_prime_factor_of_on_curve W … hden_prime dvd_rfl <witness>`,
inlining the `¬ q² ∣ q` witness shown above (argument order: the parent takes `hqd` then `hq2`
*after* `hq`, vs. the corollary's single `hp`). Then delete
`LutzNagell.PID.den_not_prime_of_on_curve`.

Caveat for the human: this is a project-scoped NO — the *parent* is a real mathlib candidate.
Deleting the corollary is optional housekeeping (it is harmless and self-documenting as-is); the
load-bearing recommendation is simply that **this corollary, by itself, is not what should go to
mathlib** — its general parent is.

---

## Next step

Delete `LutzNagell.PID.den_not_prime_of_on_curve` from the project and inline the composition at
its single call site `GeneralDenominators.lean:51` (calling the parent
`den_no_simple_prime_factor_of_on_curve` directly with `dvd_rfl` + the trivial `¬q² ∣ q`
witness) — OR keep it as a local convenience, but do not ship it to mathlib as a standalone
lemma. The mathlib-worthy result in this file is the parent
`den_no_simple_prime_factor_of_on_curve`; run `/mathlibable` on that decl separately.
