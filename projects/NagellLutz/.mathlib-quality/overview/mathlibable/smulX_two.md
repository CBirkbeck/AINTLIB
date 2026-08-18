# /mathlibable report — `WeierstrassCurve.Universal.Affine.smulX_two`

## Verdict: **NO-composable-from-mathlib**

One-line rationale: a one-line `simp` specialization of the sibling lemma
`smulX_eq` at the concrete index `n = 2`; not a standalone mathlib unit.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task; reasoned from source — task-sanctioned)
- decl `WeierstrassCurve.Universal.Affine.smulX_two`: ✓ resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:183`
- kind:                      `lemma`
- has sorry:                 no
- module docstring summary:  ZSMul.lean proves `WeierstrassCurve.zsmul_eq_smulEval`:
  `n • P = (φₙ : ωₙ : ψₙ)` (Jacobian) / `(φₙ/ψₙ², ωₙ/ψₙ³)` (affine) for any `n : ℤ`
  and nonsingular affine point `P` on a Weierstrass curve over a field.

Qualified name verified from source: namespaces `WeierstrassCurve` (line 76) →
`Universal` (line 86) → `Affine` (line 157); `lemma smulX_two` at line 183.
The parsed name `WeierstrassCurve.Universal.Affine.smulX_two` is **correct**.

---

### Statement (Phase 1)

```
lemma smulX_two : smulX 2 = smulX 1 - ψᵤ 3 / (ψᵤ 2) ^ 2 := by
  simp [smulX_eq two_ne_zero, ψᵤ]
```

Mathematically: the **x-coordinate of `2 • (X, Y)`** on the universal Weierstrass
curve, written via division polynomials. It is the **duplication-formula**
instance of the generic relation `x([n]P) = x(P) − ψₙ₊₁ψₙ₋₁/ψₙ²`: putting `n = 2`
gives `x(2P) = x(P) − ψ₃ψ₁/ψ₂² = x(P) − ψ₃/ψ₂²` (since `ψ₁ = 1`). Here:
- `smulX n := polyToField (curve.φ n) / (ψᵤ n)^2` is the project's universal-field
  x-coordinate of `n • (X, Y)` (the sibling `def`, assessed separately);
- `smulX 1 = polyToField (C X)` is the generic point's own x-coordinate;
- `ψᵤ n := polyToField (curve.ψ n)` is the n-th division polynomial in the
  universal function field `Universal.Field = Frac(ℤ[A₁..A₆,X,Y]/⟨W⟩)`.

Variables / typeclasses: **none of its own** — everything (`smulX`, `ψᵤ`,
`Universal.Field`, `curve`) is fixed by the ambient `Universal` namespace. The
scalar is the literal `2 : ℤ`.

Hypotheses: **none.** (The general parent `smulX_eq` carries `n ≠ 0`; at `n = 2`
that side condition is discharged internally by `two_ne_zero`.)

Conclusion: an equation of elements of `Universal.Field`.

Proof: **one line** — `simp [smulX_eq two_ne_zero, ψᵤ]`. It is *literally*
`smulX_eq` evaluated at `n = 2`: `smulX_eq` gives
`smulX n = smulX 1 − ψᵤ(n+1)·ψᵤ(n−1)/ψᵤ n²`; specializing `n := 2` makes
`ψᵤ(2+1) = ψᵤ 3` and `ψᵤ(2−1) = ψᵤ 1 = 1`, and `simp`/`ψᵤ` collapses the `·ψᵤ 1`
factor, yielding the stated form. No new mathematical content beyond the
substitution.

---

### Size classification (Phase 2a)

Verdict: **SMALL** lemma — but a member of a **BIG** development (the
universal-curve / `zsmul_eq_smulEval` track). Per protocol the literature width
is taken **EXHAUSTIVE** anyway (done below), because the surrounding development
is a named main result resting on a structure mathlib lacks.

### One-line check (Phase 2b)

Body line count: **1** (`simp [smulX_eq two_ne_zero, ψᵤ]`).
One-liner verdict: **ONE-LINER** (kind is `lemma`). A one-line `lemma` is a
candidate for *inlining* unless it is a genuinely reusable API fact. Assessment
of its API status: it is a **fixed-numeral specialization** of a sibling general
lemma — exactly the case the protocol treats as "prefer the general lemma; the
concrete instance is `simp`-derivable on demand". See Composition (Phase 6).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "elliptic curve duplication formula x-coordinate 2P division polynomial ψ₃/ψ₂²" | yes | `x(2P) = x − ψ₃/ψ₂²`, as the `n=2` case of `x(nP) = x − ψₙ₊₁ψₙ₋₁/ψₙ²` with `φₙ = xψₙ² − ψₙ₊₁ψₙ₋₁` | Stanford crypto notes (explicit addition formulae), arXiv 1103.4560, 1605.09279 (division by 2), 0706.4379 — fully standard; the *duplication formula* is textbook |
| 2 | WebSearch (general / mathlib) | "mathlib WeierstrassCurve division polynomial multiplication-by-n coordinate formula universal ring zsmul" | partial | `nP = (αₙ:βₙ:γₙ)`, homogeneous division polys in `ℤ[a₁..a₆][x,y,z]` (arXiv 1303.4327) | confirms the *generic-point / universal-ring* device is the standard route; mathlib doc lists `Ψ,Φ,ψ,φ` only — NO nP coordinate formula, NO universal field |
| 3 | ChatGPT MCP | (down per task — substituted by WebSearch ×2 + arXiv + mathlib doc-fetch) | n/a | — | task notes MCP may be down; fallbacks used |
| 4 | Local references | `.mathlib-quality/references/` for NagellLutz | n/a | (dir absent; only `overview/` present) | recorded n/a |
| 5 | nLab / Stacks | "division polynomial", "elliptic curve multiplication" | no | abstract EC theory only; no explicit duplication-formula coordinate page | explicit-formula material is out of scope there |
| 6 | recent arXiv (≤5y) | EDS / division-polynomial recurrences, "division by 2" | yes (1303.4327, 1605.09279, 2503.15428) | same `x(nP)=φₙ/ψₙ²`; `n=2` duplication is the elementary case | confirms standard form |

### Literature summary (Phase 3)

Concept identified as: **the duplication formula** `x(2P) = x − ψ₃/ψ₂²` — the
`n = 2` instance of `x(nP) = x − ψₙ₊₁ψₙ₋₁/ψₙ²` — for the generic point on the
universal Weierstrass curve.

Sources agree on the standard form: **yes**, verbatim and elementary. The
duplication formula is the very first nontrivial case taught after the recurrence
for `ψₙ`; no source treats `x(2P)` as a named standalone result — it is a
one-substitution corollary of the general formula. The universal-curve-over-ℤ
device (prove the identity once for the generic point, specialize by a ring hom)
is standard folklore and is cited as motivation in mathlib's own
`DivisionPolynomial/Basic.lean` docstring.

Most general standard form: the **general** lemma is `smulX_eq`
(`x(nP) = x − ψₙ₊₁ψₙ₋₁/ψₙ²` for `n ≠ 0`); `smulX_two` is strictly its `n = 2`
shadow.

Disagreement with the literature: none.

---

### Generality analysis — `smulX_two`

Literature-standard form: the **general** `smulX_eq` (any `n ≠ 0`).

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker/more-general form exists? | Reason |
|---|------------------------|-------------------|--------------------------|----------------------------------|--------|
| 1 | scalar index | the literal `2 : ℤ` | arbitrary `n ≠ 0` | **YES — `smulX_eq`** | the lemma is a *fixed-numeral* specialization; the general `n` version already exists one line above it (`smulX_eq`, line 176). |
| 2 | base ring (implicit) | universal ring `ℤ[A₁..A₆,X,Y]/⟨W⟩` (`Universal.Field`) | same (maximal base) | NO | universal ring is already the initial object; nothing more general. |

### Generality verdict (Phase 4b)

The current form is: **a specialization of an already-present more general lemma**
(`smulX_eq`). Number of generalization opportunities: 1 (the obvious one — and it
is *already realized* by the sibling `smulX_eq`). This is the decisive structural
fact: `smulX_two` adds no generality and no content over `smulX_eq`; it is a
convenience instance at `n = 2`.

### Modern-idiom check (Phase 4c)

No idiom move applies — it is a concrete equation, not a "let X be a foo" /
sequence-vs-filter / bundling situation. The only relevant observation is the
generality one above (it is the `n=2` case of `smulX_eq`).

---

### Diamond / defeq risk (Phase 4.5)

N/A in substance — it is a `lemma` (a Prop), not a `def`/instance. No typeclass
diamond, no reducibility leak, no coercion or universe concern. Risk: **NONE**.

---

### Mathlib search-status: `WeierstrassCurve.Universal.Affine.smulX_two`

[A] Lean-Finder       (index unavailable locally; substituted by grep over vendored mathlib + doc-fetch) — n/a
[B] Loogle            pattern `smulX _ = smulX _ - ψᵤ _ / (ψᵤ _)^2` over a universal EC field — the *types* (`smulX`, `ψᵤ`, `Universal.Field`) do not exist in mathlib → no hits possible
[C] LeanSearch        "x-coordinate of 2P duplication formula elliptic curve division polynomial" — mathlib has the division polynomials (`WeierstrassCurve.φ/ψ/Ψ/Φ`) but NO point-coordinate / duplication formula → no hit on the statement
[D] Grep mathlib src  `grep -rln "smulX|Universal.Field|def ψᵤ|smulEval" .lake/packages/mathlib/Mathlib/` → **no hits.** Only `Basic.lean` + `Degree.lean` exist in the DivisionPolynomial dir.
[E] Doc-fetch (Basic.html) confirmed: defines `ψ, ψ₂, φ, Ψ, preΨ, ΨSq, Φ` only; **explicitly no** universal field, **no** n•P coordinate formula, **no** 2•P duplication formula, not even `ω` (a TODO).

Searched for:
  - current form (`smulX_two`) — **absent** (its very vocabulary is absent).
  - the general parent `smulX_eq` — **also absent** from mathlib.
  - the literature-standard duplication / `x(nP)` coordinate formula — **absent**
    (mathlib has the polynomials but not their geometric coordinate identities).

Concluded: **not in mathlib** — neither `smulX_two`, nor its parent `smulX_eq`,
nor any n•P/2•P coordinate formula, nor the universal-field layer they require.

---

### Call sites — `smulX_two`

Internal use (NagellLutz, excluding the declaring `ZSMul.lean`): used **only
inside `ZSMul.lean`**. Direct consumers (from the inventory): `addX_smul_one_smul_one`
(line 265) and `addY_smul_one_smul_one` (line 280) — both *internal computational
steps* in deriving the `2 • (X,Y)` coordinates via the addition formula, where
`2 • P` is written as `(m=1)+(m+1=1)`. No other NagellLutz file imports it.

External-to-file: the **HasseWeil project carries a verbatim duplicate** —
`projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:274–275`
(identical statement and identical `simp [smulX_eq two_ne_zero, ψᵤ]` proof), with
the same two downstream uses (lines 336, 351). This is fork/duplicate code, not
independent reuse.

Composability signal: 2 internal uses, both as a local convenience for the
`addX/addY` derivation; the duplicate is a copy, not a second independent client.
This is "helper for the `n=2` group-law step", not a broadly-reused API fact.

---

### Composition check (Phase 6)

Can `smulX_two` be derived in ≤3 chained calls?

- **From mathlib directly: NO** — the statement cannot even be *written* in
  mathlib: `smulX`, `ψᵤ`, and `Universal.Field` do not exist upstream (Phase 5).
  So in the literal "compose from current mathlib" sense it is **NOT-COMPOSABLE**,
  exactly like its parent `def smulX` — because it presupposes the
  missing universal-curve layer.

- **From the project's own already-present general lemma: YES, trivially** — it is
  **1 call**: `smulX_eq two_ne_zero` followed by `simp`-normalizing `ψᵤ 1 = 1`.
  That is literally its proof. The general lemma `smulX_eq` (which *is* the
  reusable, literature-standard object) makes `smulX_two` a zero-content
  numeral specialization.

This split is the crux of the verdict. The question "does mathlib want
`smulX_two`?" is **not** the same as "does mathlib want the universal-curve n•P
formula?" (that is the parent `smulX`/`smulX_eq`/`zsmul_eq_smulEval` question,
already routed to a human in `smulX.md`). Conditional on that whole development
being upstreamed, the reusable export is `smulX_eq` (the general `n` lemma); the
concrete `x(2P)` value is then a one-`simp` corollary that a mathlib reviewer
would inline at its single use-site rather than ship as a named lemma. A
fixed-numeral specialization of an in-library general lemma is the textbook
**NO-composable-from-mathlib** shape (here: composable from the project's own
`smulX_eq` in 1 step).

Conclusion: **COMPOSABLE from the general lemma in 1 step** ⇒ not a standalone
mathlib unit.

---

## Verdict: `WeierstrassCurve.Universal.Affine.smulX_two`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Statement (Phase 1): `smulX 2 = smulX 1 − ψᵤ 3/(ψᵤ 2)²` — the **duplication
  formula**, i.e. the `n = 2` case of `smulX_eq`. Proof is the single line
  `simp [smulX_eq two_ne_zero, ψᵤ]`: pure substitution, no new content.
- Literature (Phase 3): `x(2P) = x − ψ₃/ψ₂²` is textbook and is never a named
  standalone result — it is the elementary instance of `x(nP) = x − ψₙ₊₁ψₙ₋₁/ψₙ²`.
- Generality (Phase 4): the more-general form (`smulX_eq`, arbitrary `n ≠ 0`)
  **already exists one line above** in the same file. `smulX_two` adds zero
  generality.
- Mathlib search (Phase 5): not in mathlib — and neither is its parent
  `smulX_eq` nor any n•P/2•P coordinate formula; mathlib's
  `DivisionPolynomial/Basic.lean` has only `ψ, φ, Ψ, Φ, preΨ, ΨSq` (doc-confirmed,
  not even `ω`).
- Composition (Phase 6): derivable from the project's own general lemma
  `smulX_eq` in **1 call** (its actual proof). It is a fixed-`n=2` specialization,
  the canonical NO-composable shape.

**Rationale:**

`smulX_two` is a convenience instance, not an independent theorem. The
mathlib-worthy mathematical object here is the **general** formula
`x([n]P) = x(P) − ψₙ₊₁ψₙ₋₁/ψₙ²` (the lemma `smulX_eq`) together with the universal
curve machinery — whose upstreaming decision is handled in `smulX.md`
(BORDERLINE-needs-human, with `smulX`/`smulX_eq`/`zsmul_eq_smulEval` as the real
unit). Once that development is upstreamed, the value of `2 • P` is obtained from
the general lemma by one `simp` at the literal `n = 2`; mathlib would not carry a
separate named `x(2P)` lemma for a single internal group-law step (it would
inline it, exactly as the proof does). So `smulX_two` does **not** warrant its own
mathlib entry.

Why not the other buckets:
- **NO-mathlib-has-it** — rejected: mathlib has neither `smulX_two` *nor* its
  parent `smulX_eq` nor any nP-coordinate formula; the duplication formula is not
  in mathlib in any form (Phase 5).
- **BORDERLINE-needs-human** — rejected for *this* decl: unlike the sibling `def
  smulX`, there is **no packaging judgment** to defer. A fixed-numeral
  specialization of an already-present general lemma is never itself the
  upstreaming unit; the human-judgment call lives entirely with the parent
  `smulX`/`smulX_eq` development (already captured in `smulX.md`). Recording this
  one as BORDERLINE would just re-raise that same question redundantly.
- **YES-add-as-is / YES-but-generalise-first** — rejected: the general form
  already exists (`smulX_eq`); adding the `n=2` shadow as a mathlib lemma would be
  redundant API.

**Cross-references / follow-ups (inherited, not new):**
- The *development-level* upstreaming question (should the whole `Universal`
  curve + `smulX_eq` + `zsmul_eq_smulEval` go to mathlib, and is Junyan Xu
  already preparing a PR?) is owned by `smulX.md`, Q1–Q3. `smulX_two` rides along
  with that decision; it should **not** be a separate PR target.
- The **NagellLutz ↔ HasseWeil verbatim duplication** (this lemma is copied at
  `HasseWeil/.../DivisionPolynomial.lean:274–275`) is an AINTLIB dedup/consolidation
  concern that holds regardless of the mathlib decision — file/track it as a
  `Common/` dedup ticket (same follow-up already noted in `smulX.md` Q4).

**Next action:** none specific to `smulX_two`. If the universal-curve development
is upstreamed (per `smulX.md`), keep `smulX_eq` as the exported general lemma and
let `x(2P)` be a `simp`/inline corollary; independently, consolidate the
NagellLutz↔HasseWeil duplicate into AINTLIB `Common/`.
