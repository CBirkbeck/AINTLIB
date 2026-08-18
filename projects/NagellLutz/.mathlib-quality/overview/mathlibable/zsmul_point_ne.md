# /mathlibable report — `WeierstrassCurve.Universal.Jacobian.zsmul_point_ne`

> Step-9 mathlibable assessment (NagellLutz project). Single declaration.
> Verdict up front: **NO-composable-from-mathlib**.

---

### Baseline (Phase 0)
- lake build:               not run (local build is stale per task note); reasoned from source. The decl elaborates in the committed tree — it is `import`ed/used at ZSMul.lean:522.
- decl `WeierstrassCurve.Universal.Jacobian.zsmul_point_ne`:  resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:407`
- kind:                      lemma (theorem)
- has sorry:                 no
- module docstring summary:  Expresses `n • P` of a nonsingular affine point on a Weierstrass curve via division polynomials (`zsmul_eq_smulEval`), built on the universal curve `ℤ[a₁,…,a₆,X,Y]/⟨W⟩`.

**Qualified-name verification.** Namespaces from the source: `namespace WeierstrassCurve` (L76) → `namespace Universal` (L86) → `namespace Jacobian` (L395), with `zsmul_point_ne` at L407 inside all three. Confirmed full name: `WeierstrassCurve.Universal.Jacobian.zsmul_point_ne`. (The parsed guess in the task was correct.)

---

### Statement (Phase 1)

```lean
variable {m n : ℤ}   -- L97
lemma zsmul_point_ne (h : m ≠ n) : m • Jacobian.point ≠ n • Jacobian.point := by
  rw [← sub_ne_zero, sub_eq_add_neg, ← sub_zsmul]
  exact zsmul_point_ne_zero (sub_ne_zero.mpr h)
```

`zsmul_point_ne` states: **distinct integer multiples of the distinguished universal point are distinct.** Here `Jacobian.point : Jacobian.Point (curve.baseChange Universal.Field)` is the canonical point `(X, Y, 1)` on the *universal* Weierstrass curve, over the field `Universal.Field = Frac(ℤ[A₁,A₂,A₃,A₄,A₆,X,Y]/⟨W⟩)` (Universal.lean:151–156). Because that base field is a transcendental extension, the universal point has **infinite order** (is non-torsion), so the map `n ↦ n • point` is injective. The lemma is the `m ≠ n ⇒ m•P ≠ n•P` form of that injectivity.

Variables / typeclasses (Lean side):
- `m n : ℤ` — two integers.
- `Jacobian.point` — a fixed element of the additive group `Jacobian.Point (curve.baseChange Universal.Field)` (the Mordell–Weil-style group of a Weierstrass curve over a field).

Hypotheses:
- `h : m ≠ n` — the two integers differ.

Conclusion (math): `m·P ≠ n·P` for the universal point `P`; equivalently `P` is non-torsion / `n ↦ n•P` is injective.
Conclusion (Lean): `m • Jacobian.point ≠ n • Jacobian.point`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A helper lemma — the contrapositive/injective form of the non-torsion fact `zsmul_point_ne_zero`. Not a named theorem, not in `## Main results` (the file's main result is `zsmul_eq_smulEval`), not a new structure. (Literature width still run EXHAUSTIVE below.)

### One-line check (Phase 2b)

Body line count: 2 substantive lines (a `rw` then an `exact`). Kind is `lemma`, so the def one-liner exemption machinery is **n/a** — this is a proof, not a `def`. Recorded for narrative: the proof is a trivial 2-step reduction to `zsmul_point_ne_zero`.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | injective integer multiples group element infinite order non-torsion "m • P ≠ n • P"                   | yes  | distinct multiples ⇔ infinite order | Order(group theory)/Wikipedia: order is the least m>0 with aᵐ=e; if none, order is infinite |
|  2 | WebSearch (general form)         | element infinite order group "n ↦ n • x" injective iff not torsion distinct multiples                  | yes  | `n ↦ n•x` injective ⇔ `x` non-torsion | confirmed as a generic group-theory equivalence; not EC-specific |
|  3 | WebSearch (named-after/aliases)  | order of a group element; torsion vs infinite order (Wikipedia "Order (group theory)")                 | yes  | "If no such m exists, the order of a is infinite." | standard textbook fact; the injective ⇔ infinite-order direction is the elementary cyclic-group argument |
|  4 | ChatGPT MCP                      | "Is `n ↦ n•P` injective ⇔ `¬IsOfFinAddOrder P` generic group theory; is it a 1-step consequence of `injective_zsmul_iff_not_isOfFinAddOrder`?" | n/a  | —                                | **MCP down** (Codex exec failed; task flagged this). Fallback: WebSearch + direct mathlib source read below, which already settle the question. |
|  5 | Local references                 | grep `.mathlib-quality/references/` for torsion / infinite order                                       | n/a  | (no references dir)              | `projects/NagellLutz/.mathlib-quality/references/` absent — recorded n/a. |
|  6 | nLab                             | "torsion subgroup" / order of an element                                                               | yes  | torsion = finite order; non-torsion = infinite order | nLab "torsion subgroup": g torsion iff some n≥1 with n·g=0; complement is infinite order. The injectivity restatement is folklore. |
|  7 | nCatLab (categorical)            | —                                                                                                      | n/a  | —                                | Not a categorical concept; it is an elementary statement about a single group element. |
|  8 | Stacks Project (alg geom)        | —                                                                                                      | n/a  | —                                | The *statement* is pure group theory; Stacks would only be relevant for "the generic point of an EC over a function field is non-torsion" (the **dependency** `zsmul_point_ne_zero`), not for this injective-form wrapper. |
|  9 | MathOverflow / MSE               | distinct multiples of infinite-order element are distinct                                              | yes  | standard                         | MSE/MO: an element has infinite order iff its powers are pairwise distinct — elementary, ubiquitous. |
| 10 | recent arXiv (last 5 yrs)        | torsion / infinite order distinct multiples                                                            | n/a  | —                                | Nothing recent/novel: this is 19th-century group theory, not a research statement. |

### Literature summary (Phase 3)

Concept identified as: **"an element of infinite order has pairwise-distinct integer multiples"** — equivalently, *the map `n ↦ n•x` is injective iff `x` is non-torsion (not of finite additive order).*
Sources agree on the standard form: **yes**. Distinct-multiples ⇔ infinite-order is a standard elementary group-theory equivalence; the EC context is incidental.
Most general standard form: in **any** (additive) group/monoid, `(fun n : ℤ ↦ n • x).Injective ↔ ¬IsOfFinAddOrder x`. The `m ≠ n ⇒ m•x ≠ n•x` form is the `.injective.ne` specialisation.
Generality dimensions where the literature varies:
  - ambient structure: the iff lives at the level of a group (additive `Group`/`SubtractionMonoid`); no field, no curve needed.
  - the EC-specific input is *only* "this particular `point` is non-torsion" — that is `zsmul_point_ne_zero`, a **different declaration**, not the one under assessment.
Disagreement with the literature: none. The literature standard *is* the generic injectivity/non-torsion equivalence; this lemma is a one-line corollary of it for a specific point.

---

### Generality analysis — `WeierstrassCurve.Universal.Jacobian.zsmul_point_ne`

Literature-standard form (from Phase 3): for any additive group `G` and `x : G`, `(fun n : ℤ ↦ n • x).Injective ↔ ¬IsOfFinAddOrder x`; the `m≠n` form is `(…).injective.ne`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|---|---|---|---|---|
| 1 | the point `Jacobian.point` | one specific universal-curve point | an arbitrary non-torsion element of an arbitrary additive group | yes | nothing in the *statement* uses that it is this point; the proof only uses `zsmul_point_ne_zero` (the point's non-torsion-ness). The general fact already exists in mathlib (Phase 5). |
| 2 | ambient group | `Jacobian.Point (curve.baseChange Universal.Field)` | any `AddGroup` | yes | the injective ⇔ non-torsion equivalence is at `AddGroup` generality. |
| 3 | index type `ℤ` | `m n : ℤ` | `ℤ` (this *is* the natural index) | NO | `ℤ`-indexing is exactly the standard form; not a narrowing. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** — it is a single-point specialisation of a general-group equivalence that mathlib already has. But narrowness here does **not** argue for "generalise then add", because the general form is *already in mathlib* (Phase 5). It argues for **delete + compose**.
Number of weakening opportunities found: 2 (the point, the ambient group) — both already covered by the existing mathlib general lemma.
Cost of restating: n/a — we would not restate; we would inline.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Downstream |
|----|----------|----------|------------------------|------------|
|  1 | bundled-hypothesis → typeclass/instance? | no | — | the only hypothesis is `m ≠ n`; nothing to classify. |
|  2 | sequences/metric → filters/topology? | no | — | no limiting notion present. |
|  3 | construct → universal-property class? | no | — | nothing constructed. |
|  4 | set+closure-pred → bundled substructure? | no | — | no substructure. |
|  5 | vector-space/field-specific → weaken typeclass? | **yes (already done by mathlib)** | use `injective_zsmul_iff_not_isOfFinAddOrder` at `AddGroup` generality | full non-torsion API (`IsOfFinAddOrder`, `addOrderOf`, `injOn`, `zsmul_eq_zero` machinery) |
|  6 | 1-categorical → higher-categorical? | no | — | n/a. |
|  7 | concrete index ℤ → arbitrary monoid? | no | — | `ℤ` is the correct index for the injective-zsmul statement. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes, but it is "use the existing mathlib general lemma", not "add a new generalised lemma"** — so it feeds NO-composable, not YES-but-generalise. The mathlib-idiomatic statement of this fact is `injective_zsmul_iff_not_isOfFinAddOrder.mpr (h_nontorsion)` plus `.ne`; there is no new declaration to ship.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (a proof). No definitional equalities or typeclass-search paths introduced.

---

### Mathlib search-status: `WeierstrassCurve.Universal.Jacobian.zsmul_point_ne`

[A] Lean-Finder       (mathlib index)                              n/a: offline here; covered by source grep + known API.
[B] Loogle            `Function.Injective fun (_ : ℤ) => _ • _`,
                      `?m • ?x ≠ ?n • ?x`                          hits: `injective_zsmul_iff_not_isOfFinAddOrder`; `zsmul_right_injective`.
[C] LeanSearch        "integer multiples of element injective iff
                      not finite order"                            hits: `injective_zsmul_iff_not_isOfFinAddOrder` (the additive `to_additive` of `injective_zpow_iff_not_isOfFinOrder`).
[D] Grep mathlib src  `injective.*zsmul`, `zsmul.*injective`,
                      `injective_zpow_iff_not_isOfFinOrder`,
                      `zsmul_right_injective`, `Injective.ne`      hits (verified, with file:line):
                        • `Mathlib/GroupTheory/OrderOfElement.lean:1049` —
                          `@[to_additive (attr := simp)] theorem injective_zpow_iff_not_isOfFinOrder :`
                          `(Injective fun n : ℤ => x ^ n) ↔ ¬IsOfFinOrder x`
                          → additive: `injective_zsmul_iff_not_isOfFinAddOrder`
                          (used at `Mathlib/GroupTheory/SpecificGroups/Cyclic.lean:310`).
                        • `Mathlib/Algebra/Group/Torsion.lean:63` —
                          `@[to_additive zsmul_right_injective] zpow_left_injective` (torsion-free → injective in the *base*, different shape).
                        • `Function.Injective.ne` — core (64 files use `.injective.ne`; e.g. `Mathlib/Algebra/NoZeroSMulDivisors/Defs.lean:76` `(zsmul_right_injective hx.1).ne hx.2`).
                        • building blocks for the existing proof: `sub_zsmul` (`Mathlib/Algebra/Group/Basic.lean:830`, `to_additive` of `zpow_sub`), `sub_ne_zero`, `sub_eq_add_neg` — all core.
[E] Name pattern      project-local grep for `zsmul_point_ne`      hits: this decl (ZSMul.lean:407); a `private` **duplicate** in HasseWeil (`projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:538`, identical statement & proof); the real-content dependency `zsmul_point_ne_zero` (ZSMul.lean:389/402 and HasseWeil:457/469).

Searched for both:
  - the user's current form (`m•P ≠ n•P`) — matched by `injective_zsmul_iff_not_isOfFinAddOrder` + `.ne`.
  - the literature-standard form (`Injective (n ↦ n•x) ↔ ¬IsOfFinAddOrder x`) — **found verbatim in mathlib**.

Concluded: **found the general principle in mathlib as `injective_zsmul_iff_not_isOfFinAddOrder`** (`Mathlib/GroupTheory/OrderOfElement.lean:1049`, additive form). Mathlib does **not** (and should not) have the point-specific instance; that is a composition. The EC-specific fact that the universal point is non-torsion is the **dependency** `zsmul_point_ne_zero`, which is its own declaration and is not what is under assessment.

---

### Call sites — `WeierstrassCurve.Universal.Jacobian.zsmul_point_ne`

Internal use count: **1** (within NagellLutz, excluding the declaring lines).
External-to-file callers: 0 distinct files in NagellLutz. (Plus a separate **duplicate** copy living in HasseWeil with its own single call site.)

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| `projects/NagellLutz/LutzNagell/ZSMul.lean:522` | `add_point_of_ne_eq_addXYZ … (zsmul_point_ne h)` — inside `addXYZ_smulField`, supplies "the two added points differ" so the `addXYZ` formula applies. |
| `projects/HasseWeil/…/DivisionPolynomial.lean:596` | `… (zsmul_point_ne h)` — identical use of HasseWeil's own `private` copy (DivisionPolynomial.lean:538). |

Inline-derivation grep (was the equivalent re-derived elsewhere without using this lemma?):
  - HasseWeil re-derives the **entire lemma** inline as a `private` copy (DivisionPolynomial.lean:538) with a 3-line proof `intro heq; apply zsmul_point_ne_zero (sub_ne_zero.mpr h); rw [sub_smul, heq, sub_self]` — i.e. consumers bypass this declaration and re-prove it. Strong NO-composable signal.

Call-sites read: K = 1 internal use, and the same statement is re-derived (not imported) in a sibling project. Per the Phase-6 signal table, "K = 1, plus an inline re-derivation elsewhere" leans firmly toward **NO-composable / inline**.

---

### Composition check (Phase 6)

Can `zsmul_point_ne` be derived from mathlib (and the project's existing non-torsion lemma) in ≤3 chained calls? **Yes — two independent ≤3-call routes.**

**Attempt 1 — the project's own proof, already ≤3 calls (NOT-new-math):**
```lean
example (h : m ≠ n) : m • Jacobian.point ≠ n • Jacobian.point := by
  rw [← sub_ne_zero, sub_eq_add_neg, ← sub_zsmul]
  exact zsmul_point_ne_zero (sub_ne_zero.mpr h)
```
  - Mathlib decls used: `sub_ne_zero`, `sub_eq_add_neg`, `sub_zsmul` (all core).
  - Project decl used: `zsmul_point_ne_zero` (the real content — already a separate lemma).
  - Result: **succeeds** — this *is* the current body, verbatim. It is a mechanical reduction, not a proof with new ideas.

**Attempt 2 — pure mathlib via the general equivalence (one line):**
```lean
-- given  hpt : ¬IsOfFinAddOrder Jacobian.point
example (h : m ≠ n) : m • Jacobian.point ≠ n • Jacobian.point :=
  (injective_zsmul_iff_not_isOfFinAddOrder.mpr hpt).ne h
```
  - Mathlib decls used: `injective_zsmul_iff_not_isOfFinAddOrder` (OrderOfElement.lean:1049, additive), `Function.Injective.ne`.
  - Needs `hpt : ¬IsOfFinAddOrder Jacobian.point`, which is `zsmul_point_ne_zero` repackaged (`fun hfin => zsmul_point_ne_zero hfin.dvd_orderOf… ` — or directly: non-torsion follows from `zsmul_point_ne_zero` since some nonzero multiple would have to be 0). One extra glue line at most.
  - Result: **succeeds** — a clean 1–2 line composition off the existing non-torsion fact.

Conclusion: **COMPOSABLE.** The exact form is a ≤3-call composition; no new lemma is warranted. (Attempt 1 is the existing body; Attempt 2 is the mathlib-idiomatic one-liner.)

---

## Verdict: `WeierstrassCurve.Universal.Jacobian.zsmul_point_ne`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature search (Phase 3): the statement is the standard "infinite-order ⇒ distinct multiples" fact — pure generic group theory, not EC-specific.
- Generality analysis (Phase 4): STRICTLY NARROWER than standard (single-point specialisation), but the general form is already in mathlib, so this is delete-and-compose, not generalise-and-add.
- Mathlib search (Phase 5): general principle present as `injective_zsmul_iff_not_isOfFinAddOrder` (`Mathlib/GroupTheory/OrderOfElement.lean:1049`); building blocks `sub_zsmul`, `sub_ne_zero`, `Function.Injective.ne` all core.
- Composition check (Phase 6): **COMPOSABLE** — two ≤3-call routes, one of which is literally the current 2-line body.

**Rationale.**
`zsmul_point_ne` carries no elliptic-curve content of its own. Its statement is the completely generic group-theory fact "distinct integer multiples of a non-torsion element are distinct", i.e. the `.injective.ne` of `injective_zsmul_iff_not_isOfFinAddOrder`, which mathlib already provides at full `AddGroup` generality. The single EC-specific input — that the universal point is non-torsion — lives entirely in the **dependency** `zsmul_point_ne_zero` (a separate declaration, ZSMul.lean:389/402), not here. So this lemma is a 2-line bridge between a project-internal non-torsion fact and a generic mathlib equivalence; its own body `rw [← sub_ne_zero, sub_eq_add_neg, ← sub_zsmul]; exact zsmul_point_ne_zero (sub_ne_zero.mpr h)` is exactly that bridge and uses only core mathlib lemmas. The call-site evidence reinforces the verdict: exactly one internal use (ZSMul.lean:522), and a sibling project (HasseWeil) re-derives the identical lemma inline as a `private` copy rather than importing it — the canonical "consumers bypass a thin wrapper" pattern.

**WHY not (refactor-actionable).**
Mathlib already has the building block — the injectivity ⇔ non-torsion equivalence — and the project already has the only non-generic ingredient (`zsmul_point_ne_zero`). Nothing new would be contributed to mathlib by `zsmul_point_ne`; it is a thin specialisation that mathlib would reject (mathlib does not add per-element corollaries of `injective_zsmul_iff_not_isOfFinAddOrder`). The lemma's value is purely local ergonomics, and even locally it has one consumer.

Mathlib building blocks (with full paths):
- `injective_zsmul_iff_not_isOfFinAddOrder` — additive `to_additive` of `injective_zpow_iff_not_isOfFinOrder`, `Mathlib/GroupTheory/OrderOfElement.lean:1049` (`@[to_additive (attr := simp)]`).
- `Function.Injective.ne` — core (`Mathlib/Logic/Function/Defs.lean`; 64 mathlib call sites).
- `sub_zsmul` — `Mathlib/Algebra/Group/Basic.lean:830` (`to_additive` of `zpow_sub`); `sub_ne_zero`, `sub_eq_add_neg` — core `Algebra/Group/Basic`.

Composition sketch (≤3 lines, the existing body):
```lean
example (h : m ≠ n) : m • Jacobian.point ≠ n • Jacobian.point := by
  rw [← sub_ne_zero, sub_eq_add_neg, ← sub_zsmul]
  exact zsmul_point_ne_zero (sub_ne_zero.mpr h)
```
(Equivalently, the mathlib-idiomatic one-liner once non-torsion is packaged:
`(injective_zsmul_iff_not_isOfFinAddOrder.mpr hpt).ne h`.)

Call sites in our project (from Phase 6.0): **K = 1** (ZSMul.lean:522), plus 1 in the duplicate HasseWeil copy.

Refactor plan:
1. **NagellLutz (primary):** `zsmul_point_ne` may stay as a 2-line private helper *if* the team prefers readability at ZSMul.lean:522 — but it is NOT a mathlib candidate. If trimming: inline the composition at ZSMul.lean:522, replacing `(zsmul_point_ne h)` with the 2-line derivation off `zsmul_point_ne_zero` (or factor a single `¬IsOfFinAddOrder Jacobian.point` lemma and use mathlib's `injective_zsmul_iff_not_isOfFinAddOrder`).
2. **Cross-project dedup (the real cleanup):** NagellLutz and HasseWeil have **identical** `zsmul_point_ne` + `zsmul_point_ne_zero` definitions (HasseWeil's are a `private` copy). This is the cardinal duplication the AINTLIB rules call out. File a `lane:cleanup`/dedup ticket to hoist the shared universal-point non-torsion API (`zsmul_point_ne_zero` and, if kept, `zsmul_point_ne`) into a common location both projects `import`, deleting the HasseWeil copy. Argument-order note: both copies have the identical signature `(h : m ≠ n)`, so call sites need no change beyond the import.

**Next action:** delete (or keep as a clearly project-local helper) `zsmul_point_ne`; do **not** propose it to mathlib. The actionable cleanup is the NagellLutz↔HasseWeil dedup of the universal-point non-torsion API. The genuinely mathlib-relevant question, if any, is whether the *dependency* `zsmul_point_ne_zero` (the universal point is non-torsion) deserves upstreaming — assess that decl separately; this wrapper does not.

---

## Next step

Delete or localise `zsmul_point_ne` (it is a ≤3-call composition off mathlib's `injective_zsmul_iff_not_isOfFinAddOrder` and the project's own `zsmul_point_ne_zero`); file a cross-project dedup ticket for the duplicated NagellLutz/HasseWeil universal-point non-torsion API. Not a mathlib candidate.
