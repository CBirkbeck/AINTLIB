# `/mathlibable` report — `PadicLFunctions.unitOfNat`

**Final verdict: `BORDERLINE-needs-human`.**

The core unit construction is mathlib's `IsUnit.unit` (composable in one line at the
hypothesis-carrying call site), and the *junk-value total* form `ℕ → ℤ_[p]ˣ` is almost
certainly not the form mathlib wants. But there is a real, unfilled mathlib gap one step
away — a *hypothesis-carrying* `PadicInt.unitOfCoprime` mirroring the existing
`ZMod.unitOfCoprime` — and whether mathlib wants that p-adic analogue (and in what form)
is a taste/policy call the skill cannot make alone. Numbered questions in Phase 7.

---

### Baseline (Phase 0)

- lake build:               not re-run (build is stale/slow in this checkout); **reasoned from source** per the skill's Phase-0 fallback. Decl + all dependencies read directly.
- decl `PadicLFunctions.unitOfNat`:  ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/EisensteinFamily.lean:53`
- kind:                      `def` (`noncomputable`, guarded by `open Classical in`)
- has sorry:                 no
- module docstring summary:  "The p-adic family of Eisenstein series (RJW §8)" — the Kubota–Leopoldt pseudo-measure interpolates the coefficients of the p-stabilised Eisenstein series; non-constant coefficients are divisor-sums of Dirac measures.

### Statement (Phase 1)

`PadicLFunctions.unitOfNat` is a **definition** of the following:

> For a fixed prime `p`, send a natural number `d` to the element of `ℤ_p^×` it represents
> when `p ∤ d` (equivalently `v_p(d) = 0`, equivalently `‖d‖_p = 1`), and to the junk value
> `1 ∈ ℤ_p^×` otherwise. I.e. `unitOfNat p d = d` viewed in `ℤ_p^×` when `d` is a `p`-adic
> unit, else `1`.

The source body is the one-line dependent-if:
```lean
noncomputable def unitOfNat (d : ℕ) : ℤ_[p]ˣ :=
  if h : IsUnit ((d : ℕ) : ℤ_[p]) then h.unit else 1
```

Variables / typeclasses involved (Lean side):
- `p : ℕ` with `[hp : Fact p.Prime]` — the residue characteristic (section `variable`).
- `d : ℕ` — the natural number being viewed as a p-adic unit.

Hypotheses (Lean side):
- none on the def itself (it is **total** — the coprimality condition is replaced by a junk-value branch). The companion lemma `unitOfNat_coe` carries the `¬ p ∣ d` hypothesis to extract the value.

Conclusion (math): the canonical lift `ℤ → ℤ_p^×` restricted to `p`-adic units, totalised by a junk default.

Conclusion (Lean): `ℤ_[p]ˣ`.

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: an indexing/bookkeeping helper — a junk-value totalisation of `IsUnit.unit` used to index a `Finset.sum` of Dirac measures. Not a named structure, not a `## Main results` entry (the main result is `eisensteinFamily_interpolation`), not named after a person/place.

(Note: literature width was EXHAUSTIVE regardless. The SMALL classification did not gate Phase 3.)

### One-line check (Phase 2b)

Body line count: **1 substantive line** (`if h : IsUnit … then h.unit else 1`).
One-liner verdict: **ONE-LINER**.

| Exemption                         | Applies? | Evidence |
|-----------------------------------|----------|----------|
| Avoid defeq abuse                 | no       | No downstream proof relies on the RHS spelling being sealed; `unitOfNat_coe` rewrites it openly via `dif_pos … IsUnit.unit_spec`. |
| Avoid typeclass diamonds          | no       | No competing `Mul`/`One` instance on `ℤ_[p]ˣ` is being disambiguated; the def picks no instance. |
| Mark semantic intent / API name   | **yes (weak)** | The name + docstring is the API surface for the divisor-sum machinery: it lets `divisorMeasure` (line 68) write `PadicMeasure.dirac p (unitOfNat p d)` inside a `Finset.sum` summand where the membership proof `¬ p ∣ d` is **not in lexical scope** (the bound variable `d` ranges freely over the filtered `Finset`). Threading the proof instead (e.g. `Finset.sum_attach`) would be clumsy. So the junk-value totality buys real call-site ergonomics — but only for **one** consumer family inside one file. |

Conclusion: **ONE-LINER WITH-EXEMPTION** (the semantic-intent / call-site-ergonomics exemption applies, but only weakly — a single in-file consumer). Carried into Phase 7: a YES verdict on this one-liner would need to justify shipping it despite the thin exemption; a NO/BORDERLINE leaning is reasonable.

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query | Hit? | Standard form found | Notes |
|----|----------------------------------|-------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "natural number coprime to p as a unit in p-adic integers Z_p^× definition" | yes | `p ∤ d ⟹ d ∈ ℤ_p^×`, equivalently `v_p(d)=0` ⟺ `‖d‖_p=1` | Wikipedia *p-adic valuation*; nLab *p-adic number*; standard. The **fact** is named, not a function. |
|  2 | WebSearch (general form)         | `"unit of coprime" OR unitOfCoprime mathlib ZMod p-adic units construction` | yes | `ZMod.unitOfCoprime (x : ℕ) (h : Nat.Coprime x n) : (ZMod n)ˣ` is the closest *named* construction; it is hypothesis-carrying, in `ZMod`, with **no p-adic analogue** surfaced | mathlib4 docs `Data.ZMod.Basic`; the analogue gap is the load-bearing finding |
|  3 | WebSearch (named-after / aliases)| "Kubota-Leopoldt p-adic L-function Eisenstein measure 'd as an element of' units divisor sum" | yes | Confirms the *usage* ("view `d ∈ ℤ_p^×`") is pervasive in Iwasawa theory / Eisenstein-measure constructions (Serre, Mazur, Delbourgo sum-expressions) | Cambridge EMS, Williams LTCC notes, Dasgupta — the lift is used everywhere but never christened as a function |
|  4 | ChatGPT MCP                      | (intended: "standard definition of viewing a coprime nat as a p-adic unit; standard generality; historical evolution") | **n/a** | — | **ChatGPT MCP not configured in this environment** (no `chatgpt`/`openai` MCP tool present). Substituted with extra WebSearch breadth (rows 1–3, 9, 10) per the EXHAUSTIVE protocol's spirit. |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` | **n/a** | — | Directory absent (only `…/.mathlib-quality/overview/` exists); `refs/` symlink absent. Recorded n/a. |
|  6 | nLab                             | "units of p-adic integers coprime natural number valuation zero" | yes | nLab *p-adic number*: units = elements of valuation 0 / abs value 1; coprime nats qualify | Confirms the fact; no notion of a totalised `ℕ → ℤ_p^×` map |
|  7 | nCatLab (if categorical)         | — | **n/a** | — | Not a categorical concept; it is an elementary ring-theoretic lift. |
|  8 | Stacks Project (if alg geom)     | — | **n/a** | — | Not an algebraic-geometry concept; no scheme/sheaf content. |
|  9 | MathOverflow / Math.SE           | "associate a unit to coprime integer p-adic ring junk value total function" | no | — | No MO/SE discussion treats the *totalisation* as a named object; reinforces that the junk-value packaging is a formalisation convenience, not mathematics. |
| 10 | recent arXiv (last 5 years)      | (covered by rows 2–3: Williams LTCC notes 2017–18, Cambridge EMS sum-expressions 2022, arXiv 2201.08870) | yes | Same as #3 — the lift is used, unnamed | No recent paper introduces a named `unitOfNat`-style total map |

Protocol pass check: WebSearch ran 4 distinct queries across generality levels (specific / general / named-usage / MO-totalisation) + arXiv ✓; ChatGPT MCP unavailable, recorded n/a with reason and compensated with extra WebSearch breadth ✓; local refs n/a with reason ✓; nLab checked ✓; nCatLab / Stacks n/a with reasons ✓; MathOverflow + arXiv checked ✓.

### Literature summary (Phase 3)

Concept identified as: **"a natural number coprime to `p`, viewed as an element of `ℤ_p^×`"** (the restriction of the canonical map `ℤ → ℤ_p` to `p`-adic units). The underlying *fact* — `p ∤ d ⟹ ‖d‖_p = 1 ⟹ d ∈ ℤ_p^×` — is textbook-standard (Wikipedia, nLab, every p-adic-analysis text).
Sources agree on the standard form: **yes** for the fact.
Most general standard form: the canonical map sends any `p`-adic unit (norm 1) to `ℤ_p^×`; coprime naturals are the special case `v_p = 0`. The genuinely general *named* mathlib-style object is a **hypothesis-carrying** unit-of-coprime constructor (cf. `ZMod.unitOfCoprime`), not a junk-value total function.
Generality dimensions where the literature varies:
- **Domain of the lift**: `ℕ` (the user's form) vs `ℤ` vs "any element of norm 1" (`PadicInt.mkUnits`, already in mathlib). The most general *already-present* construction is `mkUnits` from a norm-1 element.
- **Totality vs hypothesis**: literature/mathlib idiom for "make a unit from a coprime input" is **hypothesis-carrying** (`ZMod.unitOfCoprime` takes `Nat.Coprime x n`); the user's *junk-value total* form is a Lean-only convenience with no mathematical referent.
Disagreement with the literature: the literature names the **fact** and (in mathlib) a **hypothesis-carrying** constructor; the user's declaration is a **junk-value totalisation**, which is a formalisation-ergonomics choice, not a literature object.

### Generality analysis — `PadicLFunctions.unitOfNat`

Literature-standard form (from Phase 3): the canonical lift restricted to `p`-adic units; the mathlib-idiomatic *named* form is a hypothesis-carrying `unitOfCoprime`-style constructor (`ZMod.unitOfCoprime` is the template).

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | input `d : ℕ` | natural number | "p-adic unit" (norm-1 element) is the most general source; `ℤ`/`ℕ` are special cases | yes (broader) | mathlib already covers the broadest source via `PadicInt.mkUnits {u : ℚ_[p]} (h : ‖u‖ = 1)`. A nat-keyed version is *narrower*, justified only by the coprimality-indexing use case. |
| 2 | totality (no hypothesis) | junk value `1` when `p ∣ d` | hypothesis-carrying (`ZMod.unitOfCoprime` requires `Nat.Coprime x n`) | yes (cleaner) | The mathlib idiom for this shape is a hypothesis-carrying constructor; the junk branch is discouraged when a natural hypothesis exists. Weakening to hypothesis-carrying is CHEAP but changes the call-site ergonomics the def was built for. |
| 3 | base ring `ℤ_[p]` | p-adic integers | any ring/`DVR`/`local ring` where coprime-to-residue-char ⟹ unit | yes | `CharP.isUnit_natCast_iff (hp : p.Prime) : IsUnit (n : R) ↔ ¬ p ∣ n` (mathlib, `Algebra/CharP/Invertible.lean:71`) holds for any `CharP R p` ring, so a hypothesis-carrying `unitOfNat`/`unitOfNotDvd` could live at full `CharP` generality, not just `ℤ_[p]`. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (junk-value `ℕ`-keyed at fixed `ℤ_[p]`, where mathlib's idiom is hypothesis-carrying and the natural generality is any `CharP R p` ring).
Number of weakening opportunities found: **3** (broaden source via `mkUnits`-style norm-1; drop the junk branch for a hypothesis; generalise the base ring to `CharP R p`).
Proposed restatement (if pursued at all — see Phase 7):
```lean
/-- A natural number not divisible by `p` as a unit of any `CharP R p` ring. -/
noncomputable def unitOfNotDvd {R : Type*} [Monoid R] [AddGroupWithOne R] (p : ℕ)
    [Fact p.Prime] [CharP R p] {d : ℕ} (hd : ¬ p ∣ d) : Rˣ :=
  (CharP.isUnit_natCast_iff (R := R) Fact.out |>.2 hd).unit
```
Cost of restatement: **CHEAP** (mechanical — `CharP.isUnit_natCast_iff` + `IsUnit.unit`), but it is **a different declaration** (hypothesis-carrying, ring-generic), and it would force the `divisorMeasure` summand to thread a per-divisor proof.

If STRICTLY NARROWER → Phase 7 weighs YES-but-generalise-first — but the catch is that the generalisation *removes* the junk-value totality that is the def's only local reason to exist, so the "generalise" target is really a *different* object whose mathlib-worthiness is itself the open question. That pushes toward BORDERLINE rather than a clean YES-but-generalise-first.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances? | no | — | The single hypothesis is `¬ p ∣ d`; no preamble to typeclass-ify beyond the existing `[Fact p.Prime]`. |
|  2 | sequences/metric → filters/topological? | no | — | No limiting/topological content; purely algebraic. |
|  3 | construct an object where a universal-property class would characterise it? | no | — | A unit lift has no universal property to bundle. |
|  4 | set-with-closure-predicate → bundled substructure? | no | — | Not a substructure. |
|  5 | vector-space/metric/field-specific → weaken typeclass to module/(semi)ring? | **yes** | Generalise the base ring `ℤ_[p]` to any `CharP R p` ring via `CharP.isUnit_natCast_iff` (Phase 4a row 3). | Would unify with `CharP`/`ZMod` unit API; the same constructor specialises to `ZMod`, `ℤ_[p]`, `𝓞_K/𝔭`, etc. |
|  6 | 1-categorical → higher-categorical? | no | — | n/a |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive monoid/ordered structure? | partial | The `ℕ` index could be `ℤ`, but the divisor-sum use case is intrinsically over `ℕ` divisors. | Marginal; not a real organisational win for this consumer. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes (ring-genericity via `CharP`)** — but it is the *same move* as the Phase-4b base-ring weakening, and it points at the hypothesis-carrying `unitOfNotDvd` above, **not** at a totalised `unitOfNat`.
- Cost: CHEAP.
- Mathlib downstream this enables: a single `CharP`-generic "coprime-to-`p` ⟹ unit" constructor that specialises to `ZMod` and `ℤ_[p]` alike — *if* mathlib wants such a constructor at all (it currently has only the **iff lemma** `CharP.isUnit_natCast_iff`, not a packaged unit constructor). 
- Real mathematical improvement: marginal. The content is one application of `CharP.isUnit_natCast_iff` to `IsUnit.unit`; the "improvement" is packaging, and mathlib's revealed preference (it ships the iff lemma, not the constructor, and ships `ZMod.unitOfCoprime` only because `ZMod` units are heavily used) suggests the packaging is wanted only where there is demand. That demand question is a human call.

### Diamond / defeq risk — `PadicLFunctions.unitOfNat`

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | **none** | Not an instance; produces a term of `ℤ_[p]ˣ` and selects no typeclass. |
| 2 | Reducibility leak | **none** | Not `@[reducible]`; sealed `noncomputable def`. Body would be exposed to defeq only on explicit `unfold`/`rw [unitOfNat]`, exactly as `unitOfNat_coe` does. |
| 3 | Non-canonical unfolding | **low** | `simp` will not unfold it (no `@[simp]`); the dependent-`if` means `rfl` won't fire without resolving the `IsUnit` decidability. Surprises unlikely; the one consumer rewrites explicitly. |
| 4 | Instance priority collision | **n/a** | Not an instance. |
| 5 | Universe-polymorphism issues | **none** | Monomorphic in `Type 0` (`ℤ_[p]ˣ`); no universe variable. |
| 6 | Coercion ambiguity | **none** | No `CoeFun`/`CoeSort` declared; uses the standard `Units.val` coercion only. |

### Risk verdict (Phase 4.5)

Overall risk: **NONE**.
Top risks: none.
Mitigations: n/a.

### Mathlib search-status: `PadicLFunctions.unitOfNat`

[A] Lean-Finder       (server not available in this offline checkout; substituted with doc-site WebFetch of `Mathlib/NumberTheory/Padics/PadicIntegers.html` + targeted grep over `.lake/packages/mathlib`)   n/a → covered by [C]/[D]
[B] Loogle            type pattern `ℕ → _ˣ` keyed on p-adic / `IsUnit _ → _ˣ` (emulated by grep `def …[Uu]nit…: …ˣ` filtered to nat/coprime/cast)   **no hit** for any nat-keyed p-adic unit constructor
[C] LeanSearch        natural-language: "unit of p-adic integers from coprime natural number" (via WebSearch row 2 + doc fetch)   **no hit** beyond `ZMod.unitOfCoprime` (different ring) and `PadicInt.mkUnits`/`unitCoeff` (different inputs)
[D] Grep mathlib src  `grep -rnE "def .*[Uu]nit.*: .*ˣ"` over `.lake/packages/mathlib/Mathlib/` filtered to nat/coprime/cast   hits: `ZMod.unitOfCoprime`, `ZMod.unitsEquivCoprime`, `ZMod.unitsMap` — **all `ZMod`, none p-adic**; PadicInt has only `mkUnits`, `unitCoeff`
[E] Name pattern      grep `unitOfNat` / `unitOfCoprime` across `.lake/packages/mathlib` and `projects/`   `unitOfNat` exists **only** in this project (`EisensteinFamily.lean:53`); the `FltRegularBernoulli` `unitOfNatCast_notMem` is an unrelated decl (residue field `𝓞 K ⧸ P`, different namespace, hypothesis-carrying)

Searched for both:
- the user's current form (junk-value `ℕ → ℤ_[p]ˣ`): **not in mathlib**.
- the literature/idiomatic form (hypothesis-carrying p-adic `unitOfCoprime`): **not in mathlib** (mathlib stops at the iff lemma `CharP.isUnit_natCast_iff` + `IsUnit.unit`; `ZMod.unitOfCoprime` is the only packaged constructor and it is for `ZMod`).

Concluded: **not in mathlib** as a packaged construction (all methods exhausted, both forms). The **building blocks are present**: `IsUnit.unit` + `IsUnit.unit_spec` (`Mathlib/Algebra/Group/Units/Defs.lean:497,505`), `CharP.isUnit_natCast_iff` (`Mathlib/Algebra/CharP/Invertible.lean:71`), and the project-local `PadicInt.isUnit_natCast_of_not_dvd` (`projects/PadicLFunctions/PadicLFunctions/KubotaLeopoldt/MuA.lean:35`). The junk-value idiom `if h : IsUnit x then h.unit else <junk>` is itself an established mathlib pattern (`Ring.inverse`, `Mathlib/Algebra/GroupWithZero/Units/Basic.lean:84`; `MulChar`, `Mathlib/NumberTheory/MulChar/Basic.lean:157`).

### Call sites — `PadicLFunctions.unitOfNat`

Internal use count: **2** (within the project, NOT counting nothing — all uses are in the **declaring file**).
External-to-file callers: **0 distinct files**.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| EisensteinFamily.lean:70 (`divisorMeasure`) | `PadicMeasure.dirac p (unitOfNat p d)` inside `∑ d ∈ n.divisors.filter (¬ p ∣ d), …` — membership proof NOT in scope at the call |
| EisensteinFamily.lean:80–81 (`divisorMeasure_moment`) | `change ((unitOfNat p d : ℤ_[p]ˣ) : ℤ_[p]) ^ k = …; rw [unitOfNat_coe p (Finset.mem_filter.1 hd).2, …]` |
| EisensteinFamily.lean:56–58 (`unitOfNat_coe`) | glue lemma: `((unitOfNat p d : ℤ_[p]ˣ) : ℤ_[p]) = (d : ℤ_[p])` under `¬ p ∣ d`, proved by `rw [unitOfNat, dif_pos …, IsUnit.unit_spec]` |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `unitOfNat`?):
- (none) — no other site builds a p-adic unit from a coprime nat inline; the only adjacent code is `EisensteinComplex.lean:63`, which sums `d ^ k` over divisors **without** lifting to units (it stays in `ℕ`/`ℂ`), so it has no need for the lift.

Call-sites signal: **K = 0 external, 2 internal (same file), no inline re-derivation**. Per the Phase-6.0.1 table this is the "K small, all in declaring file, no inline re-derivation" pattern → leans NO-composable / wrong-abstraction, *unless* the def is destined to be reused — which here means the open mathlib question, not current local demand.

### Composition check (Phase 6)

Can `unitOfNat` be derived from mathlib in ≤3 chained calls?

Attempt 1 (the value, where a coprimality proof is available — i.e. every *meaningful* use):
```lean
-- at a site with hd : ¬ p ∣ d in scope:
(PadicInt.isUnit_natCast_of_not_dvd hd).unit   -- = unitOfNat p d on the non-junk branch
```
- Mathlib/project decls used: `PadicInt.isUnit_natCast_of_not_dvd` (project; itself a 1-line `CharP.isUnit_natCast_iff` analogue) + `IsUnit.unit` (mathlib).
- Result: **succeeds** — this is exactly `unitOfNat`'s `then` branch, and `unitOfNat_coe` is literally `dif_pos … IsUnit.unit_spec`.
- Notes: the only thing not reproduced is the **junk branch**, which is never observed on the non-junk path.

Attempt 2 (the actual consumer `divisorMeasure`, summing over a filtered `Finset`):
- The summand is `PadicMeasure.dirac p (unitOfNat p d)` where `d` is the `Finset.sum` bound variable and the filter proof `¬ p ∣ d` is **not in lexical scope**. To inline `(PadicInt.isUnit_natCast_of_not_dvd hd).unit` one must recover `hd` from `Finset.mem_filter`, i.e. rewrite the sum over `Finset.attach` or use `Finset.sum_congr`/`Finset.sum_attach` plumbing.
- Result: **partial** — composable in principle, but inlining costs a non-trivial `Finset.attach`/`sum_congr` refactor at the one consumer, not a clean ≤3-call substitution.

Conclusion: **COMPOSABLE for the value; NOT-cleanly-inlinable for the totalised consumer.** The unit *construction* is a 1-call mathlib composition (`IsUnit.unit`); the *junk-value totalisation* is what is not composable, and it exists solely to lubricate one `Finset.sum`.

## Verdict: `PadicLFunctions.unitOfNat`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the *fact* "coprime nat is a p-adic unit" is textbook-standard; the *junk-value total function* is a Lean convenience with no literature referent. The nearest *named* construction is `ZMod.unitOfCoprime` (hypothesis-carrying, `ZMod`), with **no p-adic analogue in mathlib**.
- Generality analysis (Phase 4): **STRICTLY NARROWER** — three weakenings (broader source à la `mkUnits`; hypothesis instead of junk; `CharP R p` base ring). But every weakening drops the junk-value totality, i.e. yields a *different* object (`unitOfNotDvd`), so this is not a clean "generalise the same decl" situation.
- Mathlib search (Phase 5): **not in mathlib** (both forms); building blocks `IsUnit.unit` + `CharP.isUnit_natCast_iff` + the junk-`if` idiom are all present.
- Composition check (Phase 6): the unit value is a **1-call** composition `(PadicInt.isUnit_natCast_of_not_dvd hd).unit`; only the junk-value totalisation resists clean inlining, and only at one in-file consumer.

**Rationale (1–2 paragraphs):**

`unitOfNat` is a one-line `noncomputable def` whose mathematical content is entirely `IsUnit.unit` applied to "a nat coprime to `p` is a `p`-adic unit" — a fact already packaged as the iff `CharP.isUnit_natCast_iff` in mathlib and as the project-local `PadicInt.isUnit_natCast_of_not_dvd`. Wherever a coprimality proof is in scope, the def is replaced by the one-call composition `(PadicInt.isUnit_natCast_of_not_dvd hd).unit`, which is exactly what its own glue lemma `unitOfNat_coe` proves. So *as written* — a junk-value total `ℕ → ℤ_[p]ˣ` at fixed `ℤ_[p]` — it is **not** the right mathlib object: mathlib's idiom for "make a unit from a coprime input" is hypothesis-carrying (`ZMod.unitOfCoprime`), and junk-value totalisations are added only when they buy something the hypothesis-carrying form cannot. Here the totality buys exactly one thing: it lets `divisorMeasure` write the summand `dirac p (unitOfNat p d)` over a filtered `Finset` without threading a per-divisor proof — a real but purely local, single-consumer ergonomic gain.

What makes this BORDERLINE rather than a clean NO is the genuine, one-step-away mathlib gap surfaced by Phase 3/5: mathlib has `ZMod.unitOfCoprime` but **no p-adic (or `CharP`-generic) packaged unit-of-coprime constructor**, even though it ships the underlying iff lemma. A hypothesis-carrying, `CharP`-generic `unitOfNotDvd p hd : Rˣ` would fill that asymmetry and specialise to both `ZMod` and `ℤ_[p]`. Whether mathlib *wants* that constructor — given that it deliberately stops at the iff lemma and only packages the `ZMod` case where demand is high — is a taste/policy judgment the skill cannot ground in the evidence. And the *junk-value* `unitOfNat` itself is almost certainly the wrong form to upstream regardless. So the decision splits into "should the project keep `unitOfNat` as a local convenience (likely yes), and separately, should mathlib gain a hypothesis-carrying `PadicInt.unitOfCoprime`/`CharP`-generic `unitOfNotDvd` (human call)?" — which is exactly a BORDERLINE handoff.

**Refactor-actionable bar — BORDERLINE-needs-human:**

Numbered questions (≤5):
1. Do you intend `unitOfNat` to be **upstreamed to mathlib at all**, or is it a deliberately project-local indexing convenience for the divisor-sum measures (in which case the verdict collapses to "keep local; not for mathlib", and no PR is planned)?
2. If a p-adic unit-of-coprime constructor *were* upstreamed, the mathlib-idiomatic form is **hypothesis-carrying and `CharP`-generic** — `unitOfNotDvd {R} [CharP R p] {d} (hd : ¬ p ∣ d) : Rˣ := (CharP.isUnit_natCast_iff Fact.out |>.2 hd).unit` — *not* the junk-value `ℕ → ℤ_[p]ˣ`. Do you agree the junk-value form should **not** go to mathlib (and at most stay project-local)?
3. Mathlib currently ships the **iff lemma** `CharP.isUnit_natCast_iff` but *no* packaged unit constructor outside `ZMod.unitOfCoprime`. Is filling that asymmetry (a `CharP`-generic `unitOfNotDvd`) something you want to pursue as its own small PR — or is the iff lemma + `IsUnit.unit` considered sufficient by mathlib convention (in which case: NO-composable, inline `(…isUnit…).unit` at call sites)?
4. The single in-file consumer `divisorMeasure` relies on the junk-value totality to avoid `Finset.attach` plumbing. Are you willing to accept that minor plumbing cost in exchange for dropping `unitOfNat` (favouring inlining `(PadicInt.isUnit_natCast_of_not_dvd …).unit`), or is the ergonomic win worth keeping the local def?

Next action: user answers. Likely resolutions:
- **(1)=project-local / (2)=agree / (4)=keep def** → drop from mathlib consideration; keep `unitOfNat` as a documented project-local convenience. Effective verdict: **not for mathlib** (NO-composable-from-mathlib at the value level: inline `(PadicInt.isUnit_natCast_of_not_dvd hd).unit` is the mathlib-side story; the junk wrapper stays local).
- **(3)=pursue the `CharP`-generic constructor** → re-run `/mathlibable` (or `/generalise`) on the **hypothesis-carrying `unitOfNotDvd`** form, which would likely land as **YES-but-generalise-first** (target = `CharP`-generic `unitOfNotDvd`, mirroring `ZMod.unitOfCoprime`), shipped *without* the junk branch and *with* the `CharP` generality.
- **(3)=iff-lemma-is-enough** → **NO-composable-from-mathlib**: building blocks `CharP.isUnit_natCast_iff` + `IsUnit.unit`; composition `(CharP.isUnit_natCast_iff Fact.out |>.2 hd).unit` (≤2 calls); inline at the (1 meaningful) call site.

---

## Next step

User answers the four numbered questions above; re-run `/mathlibable` (on the hypothesis-carrying `CharP`-generic `unitOfNotDvd` form if Q3 says "pursue the constructor") to resolve the verdict. The skill does not pick between "keep local", "ship a `CharP`-generic `unitOfNotDvd`", and "inline from `CharP.isUnit_natCast_iff`" on the user's behalf — that hinges on whether mathlib wants a packaged p-adic/`CharP` unit-of-coprime constructor, which is the open judgment.
