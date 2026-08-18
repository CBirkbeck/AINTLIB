# /mathlibable report — `WeierstrassCurve.Universal.net_ψᵤ`

> Step-9 mathlibable assessment, NagellLutz project. Run manually (skill reference
> docs not present on this machine; reasoning from source + mathlib tree + web).

## Baseline (Phase 0)

- lake build:               not run (local build stale per task brief); reasoned from source
- decl `WeierstrassCurve.Universal.net_ψᵤ`: resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:140`
- kind:                     lemma
- has sorry:                no
- module docstring summary: integer multiples `n • P` of a rational point on an elliptic curve,
  expressed via division polynomials `(φₙ, ωₙ, ψₙ)` in Jacobian coordinates.

**Qualified name verified from source:** the decl sits inside `namespace WeierstrassCurve`
(ZSMul.lean:76) → `namespace Universal` (ZSMul.lean:86), so the full name is
`WeierstrassCurve.Universal.net_ψᵤ`. Matches the parsed name in the task brief.

## Statement (Phase 1)

```lean
lemma net_ψᵤ (p q r s) : EllSequence.net ψᵤ p q r s = 0 := by
  rw [ψᵤ_eq_normEDS]; apply net_normEDS
```

`net_ψᵤ` is a **theorem** stating: the universal `ψ`-family of division polynomials,
viewed as a sequence `ψᵤ : ℤ → Universal.Field` (i.e. `n ↦ polyToField (curve.ψ n)`
in the fraction field of the universal coordinate ring), satisfies Stange's four-index
**elliptic-net relation** identically — for all integers `p, q, r, s`,
`net ψᵤ p q r s = 0`, where

  `net W p q r s = W(p+q+s)·W(p−q)·W(r+s)·W(r) − W(p+r+s)·W(p−r)·W(q+s)·W(q) + W(q+r+s)·W(q−r)·W(p+s)·W(p)`.

Variables / typeclasses (Lean side):
- `p q r s : ℤ` — the four net indices (implicitly typed).
- ambient: a `WeierstrassCurve R` over `[CommRing R]`; `ψᵤ` is the *universal* sequence
  (`curve` = the universal curve over `ℤ[A₁..A₆]`, `Universal.Field` its function field).

Hypotheses (Lean side): none beyond the ambient universal-curve setup.

Conclusion (math): the universal division-polynomial sequence is an elliptic net (the
`net` polynomial vanishes), which is exactly the four-index Stange relation that the
three-index EDS recurrence packages.

Conclusion (Lean): `EllSequence.net ψᵤ p q r s = 0`.

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: helper lemma — a one-line specialization of the general `net_normEDS` at the
particular sequence `ψᵤ`; not a named theorem, not a `## Main results` entry. It is a
glue step inside the proof of the multiplication formula `zsmul_eq_smulEval`.

## One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → one-liner check **n/a**.
(The proof body is itself one line — `rw [...]; apply net_normEDS` — a 2-call
composition, which is the relevant signal here and feeds Phase 6.)

## Literature search (Phase 3)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific) | "Stange elliptic nets net relation division polynomials universal Weierstrass curve" | yes | the `net`/elliptic-net relation is Stange's; division polys satisfy it | eprint.iacr.org/2006/392 (Stange, Tate pairing via elliptic nets); arXiv 2512.09601 |
| 2 | WebSearch (general) | "elliptic divisibility sequence normalized EDS division polynomial recurrence net relation" | yes | EDS recurrence `h_{m+n}h_{m−n}=h_{m+1}h_{m−1}h_n²−h_{n+1}h_{n−1}h_m²`; division polys evaluate to EDS | Wikipedia EDS; arXiv 1909.12654; Ward 1948 origin |
| 3 | WebSearch (named-after/aliases) | (covered by #1) "Stange elliptic nets" / "net relation" | yes | named after Stange (elliptic nets); 3-index EDS named after Ward/Morgan | concept named; the *universal-curve instance* is not separately named |
| 4 | ChatGPT MCP | — | n/a | — | MCP down per task brief; substituted with extra WebSearch + nLab |
| 5 | Local references | `.mathlib-quality/references/` | n/a | — | directory absent (only `overview/` present under `.mathlib-quality/`) |
| 6 | nLab | "elliptic divisibility sequence" / "elliptic net" | n/a | — | nLab has no dedicated EDS/elliptic-net page; concept lives in number-theory literature, not category theory |
| 7 | nCatLab | — | n/a | — | not a categorical concept |
| 8 | Stacks Project | "division polynomial" / "elliptic net" | n/a | — | Stacks has elliptic curves but no division-polynomial/elliptic-net chapter |
| 9 | MathOverflow/MSE | (subsumed by #1/#2) | n/a | — | EDS/elliptic-net Q&A exists but adds nothing past Stange/Ward standard form |
| 10 | recent arXiv (≤5y) | (from #1/#2) | yes | Stange 2025 "Division polynomials for arbitrary isogenies" (eprint 2025/521); arXiv 2604.05280 "On Elliptic Sequences over Commutative Rings" | confirms the general `normEDS ⇒ net = 0` fact is the standard object; the universal-ψ instance is formalization-internal |

### Literature summary (Phase 3)

Concept identified as: **Stange's elliptic-net (`net`) relation** for the division-polynomial /
elliptic-divisibility sequence; the underlying object is the normalized EDS (`normEDS`).
Sources agree on the standard form: **yes** — division polynomials of an elliptic curve form an
elliptic net / satisfy the EDS recurrence (Ward 1948; Stange 2007).
Most general standard form: *every* normalized EDS (equivalently the universal division-polynomial
sequence over `ℤ[A₁..A₆]`) satisfies the net relation — this is `net_normEDS`, already a
project-local lemma. `net_ψᵤ` is the trivial **instance** of that general fact at the one specific
sequence `ψᵤ`.
Generality dimensions where the literature varies: base ring (finite field → arbitrary commutative
ring, arXiv 2604.05280); the *most general* is "arbitrary commutative ring", which the project's
`net_normEDS` already covers. `net_ψᵤ` does NOT introduce new generality — it fixes the ring to the
universal field and the sequence to `ψᵤ`.
Disagreement with the literature: none. The literature names the general object, not this instance.

## Generality analysis (Phase 4)

Literature-standard form (Phase 3): "every normalized EDS satisfies the net relation" — held by
the project's own `EllSequence.net_normEDS` (`...EllipticDivisibilitySequence.lean:1465`) and by
`IsEllSequence.normEDS` upstream of it. `net_ψᵤ` specializes this to `W := ψᵤ`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | the sequence `W` | fixed to `ψᵤ` (universal-field ψ) | arbitrary `normEDS b c d` | **YES** | `net_normEDS` already states it for any normEDS over any comm ring; `net_ψᵤ` just plugs in one sequence |
| 2 | base ring | `Universal.Field` (a field) | arbitrary `[CommRing R]` | **YES** | the general lemma needs no field; the field here is incidental to the surrounding proof |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** — but the more general form is **not a
restatement of this lemma**, it is a *different, already-existing* lemma (`net_normEDS`). So the
right move is not "generalise `net_ψᵤ`"; it is "delete `net_ψᵤ` and call `net_normEDS` after
`ψᵤ_eq_normEDS`". This points to a NO bucket, not YES-but-generalise-first. (YES-but-generalise
would apply if the general form did not yet exist; here it does, project-locally.)
Number of weakening opportunities: 2 (both already realized by `net_normEDS`).
Cost of restatement: n/a — no restatement; the general lemma exists.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Note |
|---|----------|----------|------|
| 1 | bundled hyps → typeclasses? | no | already typeclass-driven (`IsEllSequence`, `normEDS`) |
| 2 | sequences/metric → filters/topology? | no | discrete integer-indexed algebraic identity; no topology |
| 3 | construction → universal-property class? | no | `net = 0` is a polynomial identity, not a UP |
| 4 | set+closure-pred → bundled substructure? | no | n/a |
| 5 | vector-space/field-specific → weaker typeclass? | partially | the field is incidental; general lemma is over `CommRing` — but that's covered by `net_normEDS`, not a new idiom for *this* decl |
| 6 | 1-categorical → higher-categorical? | no | n/a |
| 7 | concrete index ℤ → general monoid? | no | the net relation is intrinsically ℤ-indexed (Stange) |

Modern idiom available: **no** (for `net_ψᵤ` specifically). One-line reason: it is a plug-in
instance of an existing general lemma; there is no contemporary reformulation that improves *this*
decl — the improvement is simply to not have it.

## Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equality or typeclass-search path introduced).

## Mathlib search (Phase 5)

```
### Mathlib search-status: WeierstrassCurve.Universal.net_ψᵤ

[A] Lean-Finder       n/a (offline)              n/a
[B] Loogle            "EllSequence.net … = 0" pattern   not run live (offline); resolved by direct mathlib-tree grep below
[C] LeanSearch        n/a (offline)              n/a
[D] Grep mathlib src  "EllSequence", "def net (p q r s", "net_normEDS", "namespace EllSequence" over .lake/packages/mathlib/Mathlib/   NO HITS
[E] Name pattern      "net_ψᵤ", "ψᵤ", "Universal.net"  NO HITS in mathlib tree
```

Searched for both forms:
- user's form (`net ψᵤ … = 0`): **not in mathlib** — neither `ψᵤ` (the universal-field ψ
  sequence) nor `net_ψᵤ` exist upstream.
- literature-standard / general form (`net (normEDS …) = 0`): **also not in mathlib** —
  `EllSequence.net`, `net_normEDS`, and the whole `EllSequence` namespace are **project-local
  additions**. Mathlib's `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` is 547 lines and
  contains `IsEllSequence`, `normEDS`, `normEDSRec` — but has **no** `net`, no `addMulSub`, no
  `rel₄`, no `invarNum`. The project's fork of that file is **1672 lines** (a ~3× superset adding
  Stange's elliptic-net layer).

Concluded: **not in mathlib** (mathlib tree grep exhausted, both the user's form and the general
form). Crucially, the *building block* `net_normEDS` it composes from is itself NOT upstream — it is
project-local. So this is not `NO-mathlib-has-it`.

## Composition check (Phase 6)

### Call sites — `WeierstrassCurve.Universal.net_ψᵤ`

Internal use count (NagellLutz, excluding declaring file): **1**
- `projects/NagellLutz/LutzNagell/ZSMul.lean:334`:
  `· have := (EllSequence.net_add_sub_iff _ n m).mp (net_ψᵤ _ _ _ _)`

External-to-project duplicate: a **verbatim-identical twin** exists in the HasseWeil project:
- `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:218` — same statement, same proof
  `rw [ψᵤ_eq_normEDS]; apply net_normEDS`; used at `DivisionPolynomial.lean:405` the same way.
  This is the duplicated General*/auxiliary track the project context warned about.

Inline-derivation grep: the only consumers are the two `net_add_sub_iff … |>.mp` sites; the fact is
not re-derived inline elsewhere.

### Composition (Phase 6)

Can `net_ψᵤ` be derived in ≤3 chained calls from already-available (project) primitives?

Attempt 1: `by rw [ψᵤ_eq_normEDS]; apply net_normEDS`  ← **this IS the proof**, verbatim.
  - Decls used: `ψᵤ_eq_normEDS` (ZSMul.lean:134) + `EllSequence.net_normEDS`
    (EllipticDivisibilitySequence.lean:1465).
  - Result: **succeeds** — 2 calls (one `rw`, one `apply`).

Conclusion: **COMPOSABLE** — but from *project-local* primitives, not from mathlib primitives.
This is the decisive distinction: the standard `NO-composable-from-mathlib` bucket requires the
building blocks to be in **mathlib**. Here `net_normEDS` and `EllSequence.net` are project code, so
inlining `net_ψᵤ` at its 1 call site would mean inlining a call to *another project-local lemma* —
it does not remove a mathlib-gap, it just trades a named 2-line helper for an inline 2-call.

## Verdict: `WeierstrassCurve.Universal.net_ψᵤ`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the named object is Stange's elliptic-net relation; the standard
  result is "every normEDS satisfies net = 0" (the general lemma), not this universal-ψ instance.
- Generality analysis (Phase 4): STRICTLY NARROWER than the general `net_normEDS`, which already
  exists project-locally — so the fix is to call the general lemma, not to generalise this one.
- Mathlib search (Phase 5): NOT in mathlib in any form; moreover its building blocks
  (`EllSequence.net`, `net_normEDS`) are themselves NOT in mathlib (project fork of the EDS file).
- Composition check (Phase 6): COMPOSABLE in 2 calls (`ψᵤ_eq_normEDS` then `net_normEDS`); K = 1
  internal call site; a verbatim duplicate lives in HasseWeil.

**Rationale:**

`net_ψᵤ` is not a candidate for mathlib **as itself**: it is a one-line instantiation
(`rw [ψᵤ_eq_normEDS]; apply net_normEDS`) of the general fact "any normalized EDS satisfies
Stange's net relation" at the single sequence `ψᵤ`, the universal division-polynomial sequence
inside this formalization's universal-curve machinery. It mentions a wholly project-internal object
(`ψᵤ : ℤ → Universal.Field`) that has no upstream analogue and no independent mathematical interest
outside the proof of `zsmul_eq_smulEval`. Mathlib's bar wants the **general** statement
(`net_normEDS` — every `normEDS` is an elliptic net), not a per-construction instance of it.

The reason this is `NO-composable-from-mathlib` rather than `NO-mathlib-has-it` is that the general
lemma it specializes — `EllSequence.net_normEDS` — is **not yet in mathlib**; it lives in this
project's 1672-line fork of `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (upstream is
547 lines and has no `net`/`EllSequence` layer at all). So today there is nothing in mathlib to
cite; the fact is purely a 2-call composition of project-local primitives. (The genuinely
upstreamable object in this neighbourhood is the elliptic-net layer itself — `EllSequence.net`,
`net_normEDS`, `rel₄`, `net_add_sub_iff` — which should be assessed/contributed as a unit; `net_ψᵤ`
would then *not* be part of that PR, because it is a downstream specialization at a project-specific
sequence.)

**WHY not (refactor-actionable):**
Mathlib has the *building blocks* only in the limited sense that the general theory will live there
once the project's elliptic-net layer is upstreamed; right now even those blocks are project-local.
`net_ψᵤ` itself contributes no new mathematical content — it is the trivial `W := ψᵤ` instance.

Project-local building blocks (the composition):
- `WeierstrassCurve.Universal.ψᵤ_eq_normEDS` — `projects/NagellLutz/LutzNagell/ZSMul.lean:134`
- `EllSequence.net_normEDS` — `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1465`

Composition sketch (≤3 lines), already the proof body:
```lean
example (p q r s : ℤ) : EllSequence.net ψᵤ p q r s = 0 := by
  rw [ψᵤ_eq_normEDS]; apply net_normEDS
```

Call sites in this project (Phase 6.0): K = 1 — `ZSMul.lean:334`
(`(EllSequence.net_add_sub_iff _ n m).mp (net_ψᵤ _ _ _ _)`).

Refactor plan (for an eventual cleanup, NOT a mathlib PR):
1. At `ZSMul.lean:334`, inline: replace `net_ψᵤ _ _ _ _` with the 2-call composition
   `(by rw [ψᵤ_eq_normEDS]; apply net_normEDS : EllSequence.net ψᵤ _ _ _ _ = 0)`, then delete the
   `net_ψᵤ` lemma — OR keep `net_ψᵤ` as a thin local convenience wrapper (it is harmless and the
   1-line proof is self-evident). With only one call site, deletion-and-inline is the cleaner
   option; keeping it is defensible as a readability alias.
2. Note the HasseWeil duplicate (`DivisionPolynomial.lean:218`): whatever is decided here should be
   applied identically there — this is a cross-project dedup candidate (the two are character-for-
   character identical), better tracked as an AINTLIB cleanup issue than as a mathlib question.

**This decl does NOT go to mathlib.** It is internal glue. If anything in this file is upstreamed,
it is the general elliptic-net layer (assess `net_normEDS` / `EllSequence.net` separately), not
`net_ψᵤ`.

---

## Next step

Do not open a mathlib PR for `net_ψᵤ`. Treat it as an inline-able 2-call composition of project
primitives. For cross-project hygiene, file an AINTLIB cleanup/dedup issue covering the identical
NagellLutz/HasseWeil `net_ψᵤ` twins. Separately, the *upstreamable* target nearby is the
elliptic-net layer (`EllSequence.net`, `net_normEDS`, `rel₄`, `net_add_sub_iff`) — assess those with
their own `/mathlibable` runs.
