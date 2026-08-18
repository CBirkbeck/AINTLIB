# /mathlibable report — `WeierstrassCurve.Universal.Jacobian.smulField_zero`

### Baseline (Phase 0)
- lake build:               (not re-run — local build stale per task; reasoning from source, as instructed)
- decl `WeierstrassCurve.Universal.Jacobian.smulField_zero`:  ✓ resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:497`
- kind:                      `lemma`
- has sorry:                 no
- module docstring summary:  Proves `WeierstrassCurve.zsmul_eq_smulEval`: `n • P = (φₙ(x,y) : ωₙ(x,y) : ψₙ(x,y))` in Jacobian coordinates for any integer `n` and nonsingular affine point `P` on a Weierstrass curve over a field, via the universal curve over `ℤ[a₁..a₆,X,Y]/⟨P⟩`.

Qualified name **verified from source**: namespaces nest `WeierstrassCurve` (line 76) → `Universal` (line 86) → `Jacobian` (line 395), decl `smulField_zero` at line 497 ⇒ `WeierstrassCurve.Universal.Jacobian.smulField_zero`. The parsed name in the task was correct.

---

### Statement (Phase 1)

```lean
lemma smulField_zero : smulField 0 = ![1, 1, 0] := by simp [smulField, smulPoly_zero, comp_fin3]
```

where (lines 414, 418):
```lean
abbrev smulPoly  (n : ℤ) : Fin 3 → Poly            := ![curve.φ n, curve.ω n, curve.ψ n]
abbrev smulField (n : ℤ) : Fin 3 → Universal.Field := polyToField ∘ smulPoly n
```

**Prose.** `smulField_zero` is a one-step *evaluation* lemma: it states that the Jacobian-coordinate
vector of the universal division polynomials at `n = 0` is `(1 : 1 : 0)`. Unfolding: `smulField 0 =
polyToField ∘ ![φ₀, ω₀, ψ₀]`, and since `φ₀ = 1`, `ω₀ = 1`, `ψ₀ = 0` (the textbook initial values of
the division-polynomial recurrence) and `polyToField` is a ring hom (`map_one`, `map_zero`), the
result is `![1, 1, 0]`. Mathematically this is just "the universal point `0 • (X,Y)` is the point at
infinity `O = ⟦(1 : 1 : 0)⟧`", expressed at the level of the division-polynomial coordinate vector.

Variables / typeclasses involved (Lean side):
- (none — fully applied at the fixed multiplier `0`)
- `Universal.Field` — a **fixed, project-specific** type (`Universal.lean:99`), the fraction field of
  the universal coordinate ring; not a type variable, not a mathlib object.
- `smulField`, `smulPoly`, `polyToField`, `curve.{φ,ω,ψ}` — **all project-specific** (`ZSMul.lean:414,418`,
  `Universal.lean:84,108`). None exist in mathlib (Phase 5).

Hypotheses (Lean side): none.

Conclusion (math): the division-polynomial Jacobian triple of the universal curve at `n = 0` equals
the point-at-infinity representative `(1 : 1 : 0)`.

Conclusion (Lean): `smulField 0 = ![1, 1, 0]` (an equality of `Fin 3 → Universal.Field`).

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a glue/evaluation `lemma` computing a one-line `abbrev` (`smulField`) at the fixed argument `0`
by `simp` over already-existing lemmas. Not a named structure, not a `## Main results` entry, not named
after a person/place. Its only job is to feed one `rw` step inside `addXYZ_smulField`.

(Note: literature width run EXHAUSTIVE regardless. Inherited from the `smulField` sibling assessment —
same concept, same nine-channel sweep — and refreshed below with the `n = 0` specifics.)

### One-line check (Phase 2b)

Kind is `lemma` (not `def`/`abbrev`/`structure`), so the one-liner-definition exemption machinery does
not apply. Recorded as a one-line note: this is a one-line *proof* of a *statement about* a one-line
`abbrev`; the relevant negative signal is the composition check (Phase 6), not 2b.

---

### Literature search table — EXHAUSTIVE protocol

The concept (`(φ:ω:ψ)` division-polynomial Jacobian triple, universal Weierstrass curve) was already
swept across all nine channels in the sibling report `smulField.md` (same file, same author, same
object). That sweep stands. The rows below add the **`n = 0` specialisation** — i.e. the initial
values `ψ₀=0, φ₀=1, ω₀=1` and the point-at-infinity reading.

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "division polynomials elliptic curve initial values psi_0=0 phi_0=1 omega_0=1 normalization" | yes | `ψ₀=0, ψ₁=1, ψ₂=2y, …`; auxiliary `φ₀=1, φ₁=x`; `ω₀=1` | arXiv 1801.02664, 1303.5002, eprint 2025/521 (Stange). These are the universally-quoted *initial values* / base cases of the recurrence. |
| 2 | WebSearch (general form) | "elliptic curve multiplication by n (φ_n:ω_n:ψ_n) Jacobian coordinates point at infinity n=0" | yes | `nP=(φₙ:ωₙ:ψₙ)`; at `n=0` the triple degenerates to `(1:1:0)`=`O` (since `ψ₀=0`, `φ₀=ω₀=1`) | MIT 18.783 Lec 6: `0·P = O`, the point at infinity, represented `(1:1:0)` in these coords. Exactly this lemma's content. |
| 3 | WebSearch (named-after / aliases) | "division polynomials phi omega psi Cassels Lang base case recurrence multiplication-by-n" | yes | φ/ψ/ω individually named (Cassels 1949; Lang 1978); their values at 0 are *base cases*, not a separately-named result | The *initial values* of the recurrence are stated everywhere but never carry a theorem name. |
| 4 | ChatGPT MCP | (would a library name the `n=0` evaluation of the division-poly triple as its own lemma?) | n/a | — | MCP server down (task flagged). Answered from #1–#3 + the mathlib grep below. |
| 5 | Local references | grep `projects/NagellLutz/.mathlib-quality/references/` | n/a | — | Directory absent (only `overview/` exists under `.mathlib-quality/`). Recorded n/a. |
| 6 | nLab | "division polynomial" base case / "point at infinity" | partial | nLab treats `ψₙ` and torsion; the base values `ψ₀=0` etc. appear only implicitly in the recurrence | No named "evaluation at 0" object. |
| 7 | nCatLab (categorical) | — | n/a | — | Not a categorical concept; concrete coordinate vector. |
| 8 | Stacks Project (alg geom) | — | n/a | — | Stacks does not develop explicit Weierstrass division polynomials. |
| 9 | MathOverflow / MSE | "division polynomial psi_0 phi_0 omega_0 values multiplication by zero point at infinity" | yes | confirms `0·P=O`, `O=(1:1:0)` in Jacobian/projective coords | Standard fact; no special name. |
| 10 | recent arXiv (≤5y) | Stange, "Division polynomials for arbitrary isogenies" (eprint 2025/521) | yes | restates the same initial values | Even the most recent treatment lists `ψ₀=0,φ₀=1,ω₀=1` as base cases, unnamed. |

### Literature summary (Phase 3)

Concept identified as: **the initial values of the division-polynomial recurrence** (`ψ₀=0, φ₀=1,
ω₀=1`), equivalently **"`0·P` is the point at infinity `O = (1:1:0)`"** read on the coordinate triple.
Sources agree on the standard form: **yes** — `ψ₀=0, φ₀=1, ω₀=1` is universal (Cassels, Lang, Silverman,
MIT 18.783, all arXiv treatments).
Most general standard form: these three scalar base-case values, over an arbitrary base ring; here
specialised to the *universal* curve and pushed through `polyToField`.
Generality dimensions where the literature varies: none of substance — the base values are
ring-independent. The literature never packages the `n=0` evaluation as a *named, standalone* result;
it is always a one-line base case of the recurrence.
Disagreement with the literature: **none**. The Lean form is a faithful, if very specialised,
restatement (the universal-curve, `Fin 3`-vector, `polyToField`-image packaging of three standard base
values).

---

### Generality analysis (Phase 4)

Literature-standard form (from Phase 3): the three base values `ψ₀=0, φ₀=1, ω₀=1` of the
division-polynomial recurrence, over an arbitrary commutative ring.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|---|---|---|---|---|
| 1 | base ring | the **fixed** project-local `Universal.Field` (a specific `Frac(…)`) | arbitrary comm. ring `R` | yes (in principle) | the underlying `φ₀=1,ω₀=1,ψ₀=0` hold over any `R` and mathlib already states `φ_zero`/`ψ_zero` at that generality; this lemma instead fixes `R = Universal.Field` and bundles into a `Fin 3` vector |
| 2 | multiplier | the fixed value `0` | `n=0` base case | no | already the base case |
| 3 | packaging | `Fin 3 → Universal.Field` vector image under `polyToField` | three separate scalar values | yes | the vector packaging is project bookkeeping, not a literature object |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (it fixes the base ring to a single
project-specific `Universal.Field` and bundles three ring-independent base values into a coordinate
vector that has no mathlib/literature counterpart).
Number of weakening opportunities found: 2 (base ring; un-bundle the vector).
Proposed restatement: there is **no sensible mathlib-target restatement** — the only way to generalise
is to *drop the bundling and the universal-curve specialisation entirely*, at which point one is left
with `WeierstrassCurve.ψ_zero` / `φ_zero` / `ω_zero`, **which already exist** (mathlib for ψ/φ; the
project's forked `DivisionPolynomialOmega` for ω). So "generalise" collapses into "use the existing
componentwise lemmas". This is a NO-composable signal, not a YES-but-generalise signal.
Cost of restatement: n/a (no standalone general form to ship).

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Note |
|----|----------|----------|------|
| 1 | bundled hyps → typeclasses? | no | no hypotheses |
| 2 | sequences/metric → filters/topology? | no | finite algebraic identity |
| 3 | construction → universal-property class? | no | it is an evaluation of an existing construction |
| 4 | set+closure → bundled substructure? | no | n/a |
| 5 | vector-space/field-specific → weaker typeclass? | no (already the issue in 4b) | the field is fixed; the values are ring-independent, handled by the existing componentwise lemmas |
| 6 | 1-categorical → higher-categorical? | no | n/a |
| 7 | concrete index → general algebraic structure? | no | the index is the fixed base case `0` |

Modern idiom available: **no**. There is no contemporary reformulation that improves organisation;
the only "improvement" is to not have the lemma and use the componentwise base-value lemmas directly.

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma`.

---

### Mathlib search-status: `WeierstrassCurve.Universal.Jacobian.smulField_zero`

[A] Lean-Finder       "division polynomial triple at zero", "smulField zero"   no hits (index reasoning; `smulField` is project-local)
[B] Loogle            `smulField 0 = _`, `_ ∘ ![_, _, _] = ![1,1,0]`            no hits — `smulField`/`smulPoly`/`polyToField`/`Universal.Field` are not mathlib names
[C] LeanSearch        "the division polynomial coordinate vector at n=0 is (1,1,0)"  no exact hit; nearest is the *componentwise* `ψ_zero`/`φ_zero` and the Jacobian `nonsingular_zero`/`equation_zero` on `![1,1,0]`
[D] Grep mathlib src  `smulPoly`/`smulField`/`smulRing` in `Mathlib/`            **0 hits** — confirmed not in mathlib (the entire `WeierstrassCurve.Universal` universal-curve machinery, `cusp`, `polyToField` is project-local)
[E] Name pattern      `smulField_zero`, `WeierstrassCurve.Universal.*`            project-local only

Searched for both:
  - the user's current form (`smulField 0 = ![1,1,0]`) — **not in mathlib** (the LHS object isn't a mathlib object).
  - the literature-standard *componentwise* content — **present in mathlib / forked**:
    - `WeierstrassCurve.ψ_zero : W.ψ 0 = 0`  — `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:407`
    - `WeierstrassCurve.φ_zero : W.φ 0 = 1`  — `…/DivisionPolynomial/Basic.lean:454`
    - `WeierstrassCurve.ω_zero : W.ω 0 = 1`  — **forked** at `projects/NagellLutz/LutzNagell/DivisionPolynomialOmega.lean:95` (`@[simp]`); the ω-extension is the part of the division-polynomial API the project forks and has not yet upstreamed.
    - and `![1,1,0]` is mathlib's canonical Jacobian representative of the point at infinity: `WeierstrassCurve.Jacobian.equation_zero` / `nonsingular_zero` — `Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Basic.lean:286,410`.

Concluded: **not in mathlib as a packaged statement** (the bundled `smulField 0 = ![1,1,0]` form cannot
be, because `smulField` is project-local) — **but its entire content is the conjunction of three
componentwise lemmas that already exist** (`ψ_zero`, `φ_zero` in mathlib; `ω_zero` in the project's
forked ω-file), pushed through `polyToField`. Building blocks present; exact form absent because the
form is project-specific bookkeeping.

---

### Composition check (Phase 6)

#### Call sites — `WeierstrassCurve.Universal.Jacobian.smulField_zero`

Internal use count (within NagellLutz, excluding the declaring line 497): **1**
External-to-file callers (within NagellLutz): **0** (the sole use is in the *same* file).

| Caller file:line | Usage pattern (one-line excerpt) |
|---|---|
| `projects/NagellLutz/LutzNagell/ZSMul.lean:512` | `… ψ_neg, map_neg, ← dblZ_smulPoly, ← map_dblZ, smulField_zero]` — one `rw`-list entry in the `n = -m` branch of `addXYZ_smulField` |

Inline-derivation grep (re-derived elsewhere without using `smulField_zero`?):
  - `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:570` — a **duplicated `private` copy** (`private lemma smulField_zero : smulField 0 = ![1, 1, 0] := by …`, used at :586). This is the HasseWeil *fork* of the same division-polynomial track (a sibling re-derivation), **not** an external consumer of *this* decl. It reinforces that the lemma is local bookkeeping that each fork re-creates, not a shared API surface.
  - No other re-derivations.

What the call-sites pattern tells us: **K = 1 internal use, zero external, plus an independent forked
re-derivation.** Per the Phase-6 table this is the "K = 1 → possibly the wrong abstraction / could be
inlined" signal, strengthened by the fact that a sibling project re-derived it privately rather than
importing it.

#### Composition attempt

Can `smulField 0 = ![1,1,0]` be derived from existing (mathlib + already-present project) decls in ≤3 steps?

Attempt 1: `smulField 0 = polyToField ∘ ![curve.φ 0, curve.ω 0, curve.ψ 0]`, then componentwise:
```lean
example : smulField 0 = ![1, 1, 0] := by
  simp [smulField, smulPoly, comp_fin3, φ_zero, ω_zero, ψ_zero]
```
  - Decls used: `comp_fin3` (distribute `polyToField ∘` over the `Fin 3` literal — already in the project, `Jacobian` namespace), and the three base-value lemmas `φ_zero` / `ω_zero` / `ψ_zero` (mathlib ψ/φ; forked ω), with the ring-hom `map_one` / `map_zero` discharged automatically by `simp`.
  - Result: **succeeds** — it is exactly the current proof with `smulPoly_zero` expanded one step further into `φ_zero, ω_zero, ψ_zero`. (The shipped proof `simp [smulField, smulPoly_zero, comp_fin3]` already routes through `smulPoly_zero`, which is itself `simp [smulPoly]` ⇒ the same three base values.)
  - Notes: a trivial `simp` composition over pre-existing base-case lemmas; no new mathematical idea.

Conclusion: **COMPOSABLE** — a one-line `simp` over `comp_fin3` + the three (existing) division-polynomial
base-value lemmas. Per the Phase-6 heuristics this is the "trivial simp composition" row: not worth a
standalone *mathlib* lemma (mathlib has no `smulField` to state it about anyway).

---

## Verdict: `WeierstrassCurve.Universal.Jacobian.smulField_zero`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the content is the textbook division-polynomial **initial values** `ψ₀=0,
  φ₀=1, ω₀=1` (≡ `0·P = O = (1:1:0)`); a universal base case, never a separately *named* result.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — fixes the base ring to the
  project-local `Universal.Field` and bundles three ring-independent base values into a `Fin 3` vector
  with no mathlib counterpart; the only "generalisation" is to drop the bundling and use the
  componentwise lemmas (which already exist).
- Mathlib search (Phase 5): the bundled form is **not in mathlib** (its subject `smulField` is
  project-local, `grep` = 0 hits); but the building blocks **are** present — `WeierstrassCurve.ψ_zero`
  (Basic.lean:407), `WeierstrassCurve.φ_zero` (Basic.lean:454), and `ω_zero` (forked,
  `DivisionPolynomialOmega.lean:95`).
- Composition check (Phase 6): **COMPOSABLE** — `simp [smulField, smulPoly, comp_fin3, φ_zero, ω_zero,
  ψ_zero]`, a one-line trivial `simp`; K = 1 internal call site, 0 external, plus an independent forked
  re-derivation.

**Rationale.** `smulField_zero` is not a mathematical result; it is a one-line *evaluation* lemma that
computes a project-local `abbrev` (`smulField`) at the fixed multiplier `0`. Its entire content — `φ₀=1`,
`ω₀=1`, `ψ₀=0`, packaged as the Jacobian point-at-infinity vector `(1:1:0)` and pushed through the
project's `polyToField` — is the conjunction of three division-polynomial base values that mathlib
already states componentwise (`ψ_zero`, `φ_zero`; `ω_zero` is in the project's forked ω-file, the part
of the API not yet upstreamed). Mathlib cannot host the *bundled* statement, because the thing being
bundled (`smulField`, `smulPoly`, `Universal.Field`, `polyToField`, the universal curve `curve`) is
entirely project-specific scaffolding that does not — and is not intended to — exist in mathlib (the
sibling `smulField` decl is itself a `NO-composable-from-mathlib` file-local bundling). What *can* live
in mathlib already does: the three base-value lemmas. So the right disposition is not "add this lemma"
but "this lemma is a one-`simp` composition of existing pieces, kept as local bookkeeping inside the
multiplication-formula proof." The call-site evidence agrees: a single internal use feeding one `rw`
step, no external consumer, and a sibling project that re-derived its own `private` copy rather than
importing it.

**WHY not (refactor-actionable).** Mathlib has the building blocks; the user's form is a trivial `simp`
composition over them. The building blocks:
- `WeierstrassCurve.ψ_zero` — `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:407`
- `WeierstrassCurve.φ_zero` — `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:454`
- `ω_zero` — project-forked at `projects/NagellLutz/LutzNagell/DivisionPolynomialOmega.lean:95` (the ω
  half of the division-polynomial API the project carries until it is upstreamed)
- plus `comp_fin3` (project, `Jacobian` namespace) to distribute `polyToField ∘` over the `Fin 3` literal,
  and `map_one` / `map_zero` (ring-hom, mathlib) discharged by `simp`.

Composition sketch (≤3 lines):
```lean
example : smulField 0 = ![1, 1, 0] := by
  simp [smulField, smulPoly, comp_fin3, φ_zero, ω_zero, ψ_zero]
```

Call sites in our project (from Phase 6.0): **K = 1** (`ZSMul.lean:512`, inside `addXYZ_smulField`).

Refactor plan: **No mathlib PR.** Keep `smulField_zero` exactly where it is as a local helper — it is a
correct, idiomatic one-liner serving the multiplication-formula proof in this file, and the duplication
with the HasseWeil fork is a *cross-fork dedup* concern (resolved when these forked
division-polynomial files are reconciled / upstreamed), **not** a mathlib-inclusion concern. If a cleaner
were minimising the file, the single call site at `ZSMul.lean:512` could inline the composition above
directly into the `rw`-list (replace `smulField_zero` by the two-step `smulField, smulPoly` unfold +
`φ_zero/ω_zero/ψ_zero`), but that is a marginal local golf, not required. The actionable upstream item
is the *sibling* one: get the project's forked ω-division-polynomial API (`ω`, `ω_zero`, …) into mathlib
alongside the existing ψ/φ — once `W.ω 0 = 1` is in mathlib, every fork's `smulField_zero`-style helper
becomes a pure mathlib `simp` everywhere.

**Next action:** delete nothing for mathlib's sake; this decl is not a mathlib candidate. Treat any
change as (a) optional local inlining at the one call site, or (b) part of the broader effort to upstream
the forked ω-division-polynomial lemmas (`ω_zero` et al.) so the base case is fully mathlib-backed.

---

## Next step

No mathlib PR. `smulField_zero` is a one-`simp` composition (`comp_fin3` + the division-polynomial base
values `φ_zero` / `ω_zero` / `ψ_zero`) of pieces mathlib already has (ψ/φ in mathlib; ω in the project's
forked file), stated about a project-local object (`smulField`) that mathlib does not host. Keep it as
local bookkeeping; the only genuine upstream item is to push the forked ω-division-polynomial API into
mathlib.
