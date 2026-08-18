# /mathlibable report — `LutzNagell.PID.monic_Φ_sub_smul_ΨSq`

Mode A (single declaration), full workflow. Local Lean build is stale, so Phase 0
build-clean is recorded as ASSUMED-stale and the assessment reasons from the source
statement + read mathlib source (per the project's standing note).

### Baseline (Phase 0)
- lake build:               (stale locally) — reasoned from source; decl elaborates per file context
- decl `LutzNagell.PID.monic_Φ_sub_smul_ΨSq`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDIntegralMultiple.lean:26`
  (namespace `LutzNagell` → `PID`; verified qualified name from source)
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  "Integral multiple implies integral point (over UFDs)" —
  if `n • P` has integral affine coords over `K = Frac(R)`, then `P` does;
  generalisation of the `ℤ/ℚ` `GeneralIntegralMultiple.lean` to a UFD `R`.

### Statement (Phase 1)

`LutzNagell.PID.monic_Φ_sub_smul_ΨSq` is a theorem stating: for a Weierstrass curve
`W` over a commutative domain `R`, an integer `n` with `(n : R) ≠ 0`, and any scalar
`c : R`, the polynomial `Φₙ − C c · ΨSqₙ ∈ R[X]` is **monic**.

Here `Φₙ = W.Φ n` and `ΨSqₙ = W.ΨSq n` are the standard division-polynomial objects:
`Φₙ` is the numerator and `ΨSqₙ = ψₙ²` the (squared) denominator of the
multiplication-by-`n` map on the x-coordinate, `x(nP) = Φₙ(x)/ΨSqₙ(x)`. The point of
the lemma is that subtracting any `R`-multiple of `ΨSqₙ` (degree `n²−1`) from the
monic `Φₙ` (degree `n²`, leading coeff `1`) leaves the top coefficient untouched, so
the difference is still monic. Downstream this feeds `isInteger_of_is_root_of_monic`:
`x` is a root of `Φₙ − C c · ΨSqₙ`, hence integral.

Variables / typeclasses (Lean side):
- `R : Type*` `[CommRing R] [IsDomain R]` — base ring (the `UniqueFactorizationMonoid R`
  instance is explicitly `omit`-ted from this lemma; it needs only a domain).
- `W : WeierstrassCurve R` — the curve.

Hypotheses (Lean side):
- `{n : ℤ}` `(hn : (n : R) ≠ 0)` — `n` nonzero in `R` (gives `n ≠ 0` and the exact
  `natDegree ΨSqₙ = n²−1`).
- `(c : R)` — arbitrary scalar.

Conclusion (math): `Φₙ − c·ψₙ²` is a monic polynomial.
Conclusion (Lean): `(W.Φ n - C c * W.ΨSq n).Monic`.

### Size classification (Phase 2a)

Verdict: SMALL
Reason: a degree-comparison helper lemma (monic minus strictly-lower-degree term),
local to the Nagell–Lutz x-integrality argument; not a named theorem, not a new
structure, not a `## Main results` entry.

(Literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `theorem`, not a `def`/`abbrev`/`structure` — n/a. (The body is a 6-line
`calc`/`refine` proof, not a definitional one-liner.)

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "elliptic curve division polynomial Φ monic leading coeff ψ² Nagell-Lutz integral point x-coord" | yes (components) | "φₙ is monic of degree n²"; "ψₙ² degree n²−1, lead coeff n²"; "x(nP)=φₙ/ψₙ²" | de Jong, Wikipedia, MIT 18.783 notes 5 — the *facts about Φ, ΨSq*, not the subtraction lemma |
| 2 | WebSearch (general form) | "division polynomial φ_n monic degree n^2 Weierstrass multiplication-by-n φ/ψ²" | yes (components) | "φₙ monic deg n², leading term x^{n²}"; "[n] has degree n²" | MIT OCW 18.783 §5; arXiv 1303.4327 — confirms exact degree/leadingcoeff facts |
| 3 | WebSearch (named-after / Silverman) | "Silverman division polynomials φ_n ψ_n monic proof integral points formal group" | yes (components) | "φₙ = xψₙ² − ψₙ₋₁ψₙ₊₁, monic degree n²"; Silverman AEC GTM 106 | The monic-minus-lower fact is used *in passing* to apply "root of a monic poly ⇒ integral"; never stated as its own named lemma |
| 4 | ChatGPT MCP | (MCP down per environment note) | n/a | — | fallback to WebSearch ×3 + nLab; the three queries already pin the standard form and its generality, and confirm the subtraction-combination is not a named result |
| 5 | Local references | `.mathlib-quality/references/` | n/a | — | directory absent for this project (checked: no `references/` under `projects/NagellLutz/.mathlib-quality/`) |
| 6 | nLab | "division polynomial" / "elliptic curve" | no | — | nLab has no division-polynomial page with a monic-combination statement; the concept lives in arithmetic-geometry texts, not nLab |
| 7 | nCatLab | n/a | n/a | — | not a categorical concept |
| 8 | Stacks Project | "division polynomial" | n/a | — | not in Stacks' scope (no elliptic-curve division-polynomial chapter) |
| 9 | MathOverflow / MSE | "Φ_n monic division polynomial degree" | yes (components) | restate of #1–#3: φₙ monic deg n² is folklore | confirms it is treated as an elementary degree count, never a citable named lemma |
| 10 | recent arXiv (≤5y) | "division polynomial φ_n ψ_n degree leading coefficient" | yes (components) | arXiv 1108.3051, 1303.4327, 2102.07573 reconfirm the degree/leadingcoeff facts | none isolates "Φₙ − c·ΨSqₙ monic" as a result |

The protocol passes: WebSearch ran 3 distinct queries across generality levels;
ChatGPT MCP unavailable (environment) → recorded with fallback rationale; local refs
absent (n/a); nLab/Stacks/nCatLab/MathOverflow/arXiv each checked with reason.

### Literature summary (Phase 3)

Concept identified as: the **division polynomials** `Φₙ` (numerator of `x∘[n]`) and
`ΨSqₙ = ψₙ²` (squared denominator) of a Weierstrass curve, with the standard degree
data `deg Φₙ = n²`, `lc Φₙ = 1`; `deg ψₙ² = n²−1`, `lc ψₙ² = n²`. The specific
declaration is the elementary corollary "monic minus a lower-degree polynomial is
monic", instantiated at `Φₙ` and `c·ΨSqₙ`.

Sources agree on the standard form: yes (Wikipedia, Silverman GTM 106, MIT 18.783,
arXiv 1303.4327/1108.3051) — `Φₙ` monic of degree `n²`, `ψₙ²` of degree `n²−1`.
Most general standard form: those degree/leading-coefficient facts hold over any base
in which `n ≠ 0` (the `n` appears only through `lc ψₙ² = n²` and the degree being
exactly `n²−1`). The "monic difference" step is a generic polynomial fact (`Monic p`,
`deg q < deg p` ⇒ `Monic (p − q)`), independent of elliptic curves entirely.
Generality dimensions where the literature varies:
  - base ring: the degree facts need `n ≠ 0` in the ring (mathlib uses `NoZeroDivisors`
    / `Nontrivial`); the project's lemma uses `[IsDomain R]` + `(n : R) ≠ 0`.
  - the subtraction-combination itself: NOT a literature object — it is the generic
    `Polynomial.Monic.sub_of_left` applied to elliptic-curve inputs.
Disagreement with the literature: none. The lemma is faithful; it is simply below the
granularity at which the literature names results.

### Generality analysis — `LutzNagell.PID.monic_Φ_sub_smul_ΨSq`

Literature-standard form (from Phase 3): the underlying generic fact is
`Monic p → degree q < degree p → Monic (p - q)` (mathlib: `Polynomial.Monic.sub_of_left`);
the elliptic-curve inputs are `Monic Φₙ` (from `lc Φₙ = 1`, `deg Φₙ = n²`) and
`deg (C c · ΨSqₙ) ≤ n²−1 < n²`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|---------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R] [IsDomain R]` | commutative domain | `NoZeroDivisors`/`Nontrivial` base is what the degree lemmas actually use | marginally | `natDegree_ΨSq` needs `[NoZeroDivisors R]`; `natDegree_Φ` needs `[Nontrivial R]`. `IsDomain` is slightly stronger than strictly necessary, but only marginally; `(n:R)≠0` already forces `Nontrivial`. Not a meaningful generalisation. |
| 2 | `(hn : (n : R) ≠ 0)` | `n` nonzero in `R` | same | no | needed to pin `deg ΨSqₙ = n²−1` exactly (else only `≤`); essential. |
| 3 | `(c : R)` scalar, `C c *` | multiply by a constant | the generic lemma allows *any* `q` with `deg q < deg Φₙ` | yes (but pointless) | the truly general statement is `Monic.sub_of_left` itself for arbitrary `q` of degree `< n²`; specialising to `C c * ΨSqₙ` is exactly the project's call-site need. |

### Generality verdict (Phase 4b)

The current form is: MAXIMALLY GENERAL (for its purpose) — but the purpose is a
*specialisation* of a generic mathlib lemma, not a literature-standard result in its
own right.
Number of weakening opportunities found: 0 meaningful (row 1 is a marginal
typeclass nicety; rows 2–3 are essential/purpose-defining).
Proposed restatement: none warranted — the "more general" form is literally the
existing mathlib primitive `Polynomial.Monic.sub_of_left`, which the project should
call directly rather than re-wrap.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream |
|----|----------|----------|------------------------|--------------------|
| 1 | bundled hyps → typeclasses? | no | — | hypotheses already typeclass/value form |
| 2 | sequences/metric → filters/topology? | no | — | purely algebraic degree count |
| 3 | construction → universal property? | no | — | no construction |
| 4 | set+closure-pred → bundled substructure? | no | — | n/a |
| 5 | vector-space/field → module/(semi)ring weakening? | no | — | already over a general comm domain |
| 6 | 1-categorical → higher-categorical? | no | — | n/a |
| 7 | concrete index → general algebraic structure? | no | `n : ℤ` is intrinsic to division polynomials | the index `n` is the division-polynomial index; cannot abstract away |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: no.
One-line reason: this is a finite degree-comparison fact about specific polynomials;
there is no topology to filter-ise, no construction to characterise, and the more
abstract form is simply the generic mathlib lemma `Monic.sub_of_left` (which the proof
already invokes) — not a "modernisation" but a direct-call replacement.

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem`.

### Mathlib search-status: `LutzNagell.PID.monic_Φ_sub_smul_ΨSq`

[A] Lean-Finder       (index unavailable for forked names) — n/a: the decl is a *fork* of mathlib `WeierstrassCurve.Φ`/`ΨSq` objects, so the index would only surface the mathlib originals; searched their support lemmas instead (below).
[B] Loogle            `Polynomial.Monic (?p - Polynomial.C ?c * ?q)` / `Monic (_ - _)` — hit: `Polynomial.Monic.sub_of_left` (the building block). No elliptic-curve-specific monic lemma.
[C] LeanSearch        "monic difference of division polynomial Φ and multiple of ΨSq" — no hit (no such named mathlib lemma).
[D] Grep mathlib src  `\.Monic` in `Mathlib/AlgebraicGeometry/EllipticCurve/` ∪ `EllipticDivisibilitySequence.lean`, filtered to Φ/Ψ — **no hits**: mathlib has NO monic lemma about division polynomials. Confirmed `Monic.sub_of_left` at `Mathlib/Algebra/Polynomial/Monic.lean:446`, `natDegree_C_mul_le` at `Mathlib/Algebra/Polynomial/Degree/Lemmas.lean:95`.
[E] Name pattern      grep `monic_Φ`/`monic_Ψ`/`leadingCoeff_Φ`/`natDegree_Φ` in mathlib — the *degree/leadingcoeff* lemmas EXIST in mathlib (`WeierstrassCurve.leadingCoeff_Φ`, `natDegree_Φ`, `natDegree_ΨSq` in `DivisionPolynomial/Degree.lean`); the *monic-combination* lemma does NOT.

Searched for both:
  - user's current form `(W.Φ n - C c * W.ΨSq n).Monic` — not in mathlib.
  - literature-standard form (generic `Monic.sub_of_left` + the Φ/ΨSq degree facts) —
    the generic lemma IS in mathlib; the elliptic-curve degree facts ARE in mathlib
    (`leadingCoeff_Φ`, `natDegree_Φ`, `natDegree_ΨSq`); only their one-step combination
    is local to the project.

Concluded: "found building blocks (`Polynomial.Monic.sub_of_left`,
`WeierstrassCurve.leadingCoeff_Φ`/`natDegree_Φ` [⇒ `Monic (W.Φ n)`],
`WeierstrassCurve.natDegree_ΨSq`, `Polynomial.natDegree_C_mul_le`); composition yields
our form in ≤3 calls." The exact combined lemma is not in mathlib.

### Call sites — `LutzNagell.PID.monic_Φ_sub_smul_ΨSq`

Internal use count: K = 2 (one genuine application + one re-export specialisation).
External-to-file callers: 1 distinct file.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| `PIDIntegralMultiple.lean:77` (same file, downstream lemma `x_isInteger_of_nsmul_x_isInteger`) | `isInteger_of_is_root_of_monic (monic_Φ_sub_smul_ΨSq W hn_R c) hroot` |
| `GeneralIntegralMultiple.lean:59` (the ℤ specialisation `monic_Φ_sub_smul_ΨSq_general`) | `PID.monic_Φ_sub_smul_ΨSq W (by exact_mod_cast hn) c` |

Inline-derivation grep: (none) — no site re-derives the monic fact by hand; both go
through this lemma. Note the only *substantive* consumer is the single `isInteger_of_
is_root_of_monic` call; `monic_Φ_sub_smul_ΨSq_general` is a thin ℤ re-export of this
very lemma (so the two together are essentially one consumer + its specialisation).

### Composition check (Phase 6)

Can `LutzNagell.PID.monic_Φ_sub_smul_ΨSq` be derived from mathlib (+ the project's
already-forked-from-mathlib degree lemmas) in ≤3 chained calls? Yes — and the proof
**already is** exactly that composition (6 lines, three named lemmas):

Attempt 1 (the actual proof, lightly recast):
```lean
example {n : ℤ} (hn : (n : R) ≠ 0) (c : R) : (W.Φ n - C c * W.ΨSq n).Monic :=
  (leadingCoeff_Φ W n).monic.sub_of_left <|     -- Monic (W.Φ n)   [via leadingCoeff_Φ ⇒ lc = 1]
    degree_lt_degree <| by                      -- deg (C c * ΨSq) < deg Φ
      calc (C c * W.ΨSq n).natDegree
          ≤ (W.ΨSq n).natDegree           := natDegree_C_mul_le _ _
        _ = n.natAbs ^ 2 - 1              := natDegree_ΨSq _ hn
        _ < n.natAbs ^ 2                  := Nat.pred_lt (pow_ne_zero 2 (by simpa using hn))
        _ = (W.Φ n).natDegree             := (natDegree_Φ _ n).symm
```
  - Mathlib decls used: `Polynomial.Monic.sub_of_left`, `Polynomial.degree_lt_degree`,
    `Polynomial.natDegree_C_mul_le`, `Nat.pred_lt`, `pow_ne_zero`; plus the
    division-polynomial degree facts `leadingCoeff_Φ`, `natDegree_ΨSq`, `natDegree_Φ`
    (which ARE in mathlib as `WeierstrassCurve.*`).
  - Result: succeeds — it is the source proof.
  - Notes: the "≤3 chained calls" bar is about *new mathematical content*. The single
    load-bearing call is `Monic.sub_of_left`; everything else is the standard
    division-polynomial degree data already in mathlib. There is **no new idea** here —
    it is glue between `Monic.sub_of_left` and the (mathlib-present) degree lemmas.

Conclusion: COMPOSABLE. The form is `Monic.sub_of_left` applied to the mathlib degree
data; the body is mechanical degree bookkeeping, not a proof requiring a new lemma.

## Verdict: `LutzNagell.PID.monic_Φ_sub_smul_ΨSq`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the underlying facts (Φₙ monic deg n²; ψₙ² deg n²−1)
  are standard folklore; the "Φₙ − c·ΨSqₙ monic" combination is NOT a named result —
  it is the generic "monic minus lower-degree" step used in passing in Nagell–Lutz.
- Generality analysis (Phase 4): MAXIMALLY GENERAL for its purpose; no meaningful
  weakening; no modern-idiom move (Phase 4c: none).
- Mathlib search (Phase 5): building blocks present —
  `Polynomial.Monic.sub_of_left` (`Mathlib/Algebra/Polynomial/Monic.lean:446`),
  `Polynomial.natDegree_C_mul_le` (`.../Degree/Lemmas.lean:95`), and the
  division-polynomial degree lemmas `WeierstrassCurve.leadingCoeff_Φ` / `natDegree_Φ` /
  `natDegree_ΨSq` (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`).
  The combined monic lemma itself is NOT in mathlib.
- Composition check (Phase 6): COMPOSABLE — the proof body *is* the ≤3-call composition
  (one load-bearing `Monic.sub_of_left`; the rest is mathlib degree bookkeeping).

**Rationale:**

This lemma is a glue step, not a contribution. Its entire mathematical content is the
generic polynomial fact `Monic p → deg q < deg p → Monic (p − q)` — which mathlib
already has as `Polynomial.Monic.sub_of_left` — specialised to `p = Φₙ`, `q = C c·ΨSqₙ`.
The two ingredients it needs about division polynomials (`Φₙ` is monic via `lc = 1`;
`deg(C c·ΨSqₙ) ≤ n²−1 < n² = deg Φₙ`) are themselves already in mathlib as
`WeierstrassCurve.leadingCoeff_Φ`, `natDegree_Φ`, and `natDegree_ΨSq`. So once the
project drops its fork and lands on the mathlib `Φ`/`ΨSq` API, the lemma becomes a
two-to-three-line inline at its single substantive call site — there is no reusable
mathlib API gap here that a *named* lemma would fill.

Crucially, the project's `Φ`, `ΨSq`, `leadingCoeff_Φ`, `natDegree_Φ`, `natDegree_ΨSq`
are verbatim forks of the mathlib `WeierstrassCurve.*` originals (confirmed by
identical signatures and line-for-line proofs in `DivisionPolynomial.lean` /
`DivisionPolynomialDegree.lean`). The reason this monic lemma exists in-project at all
is the fork; against upstream mathlib it is pure composition. It has exactly one
substantive consumer (`isInteger_of_is_root_of_monic` at `PIDIntegralMultiple.lean:77`)
plus a thin ℤ re-export (`monic_Φ_sub_smul_ΨSq_general`) — both of which can call
`Monic.sub_of_left` directly. (Note the sibling `monic_Φ_sub_smul_ΨSq_general` was
already bucketed `YES-but-generalise-first` in the project ledger; that verdict is
itself questionable for the same composition reason, but it is out of scope here — this
report covers only the PID lemma. If anything the PID lemma is the *more* general of
the two and is the one to keep if either is kept, but neither rises above composition.)

**WHY not (refactor-actionable detail):**
Mathlib has the building blocks; the user's form is a 1–3-call composition with no new
idea. Building blocks:
  - `Polynomial.Monic.sub_of_left` — `Mathlib/Algebra/Polynomial/Monic.lean:446`
  - `Polynomial.natDegree_C_mul_le` — `Mathlib/Algebra/Polynomial/Degree/Lemmas.lean:95`
  - `Polynomial.degree_lt_degree` — `Mathlib/Algebra/Polynomial/Degree/Definitions.lean`
  - `WeierstrassCurve.leadingCoeff_Φ`, `WeierstrassCurve.natDegree_Φ`,
    `WeierstrassCurve.natDegree_ΨSq` —
    `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`

Mathlib building blocks: as listed above.
Composition sketch (the proof itself, ≤3 substantive calls — `Monic.sub_of_left` is the
only load-bearing step; the rest is degree bookkeeping already in mathlib):
```lean
example {n : ℤ} (hn : (n : R) ≠ 0) (c : R) : (W.Φ n - C c * W.ΨSq n).Monic :=
  (W.leadingCoeff_Φ n).monic.sub_of_left <| degree_lt_degree <| by
    rw [(W.natDegree_Φ n).symm ▸ rfl]   -- deg (C c * ΨSq n) < deg (Φ n) = n.natAbs^2
    calc (C c * W.ΨSq n).natDegree
        ≤ (W.ΨSq n).natDegree := natDegree_C_mul_le _ _
      _ = n.natAbs ^ 2 - 1     := W.natDegree_ΨSq hn
      _ < n.natAbs ^ 2         := Nat.pred_lt (pow_ne_zero 2 (by simpa using hn))
```
(`(W.leadingCoeff_Φ n).monic` uses `Polynomial.Monic` ⟺ `leadingCoeff = 1`.)

Call sites in our project (from Phase 6.0): K = 2 (one substantive: the
`isInteger_of_is_root_of_monic` argument at `PIDIntegralMultiple.lean:77`; one re-export:
`GeneralIntegralMultiple.lean:59`).
Refactor plan: this is gated behind the larger "drop the DivisionPolynomial fork and use
mathlib `WeierstrassCurve.Φ`/`ΨSq`" cleanup. Once on the mathlib API: at
`PIDIntegralMultiple.lean:77`, replace `(monic_Φ_sub_smul_ΨSq W hn_R c)` with the inline
`((W.leadingCoeff_Φ n).monic.sub_of_left <| degree_lt_degree <| …)` shown above (or keep
a *private* project helper if the inline hurts readability — but it should not ship to
mathlib as a public lemma); at `GeneralIntegralMultiple.lean:59`, the ℤ re-export
collapses to the same inline (its `(by exact_mod_cast hn)` becomes the `(n : ℤ) ≠ 0`
hypothesis feeding `natDegree_ΨSq`/`natDegree_Φ`). While the fork remains, the lemma is
harmless local glue; it simply should not be proposed to mathlib.
Next action: keep as a local helper while the fork stands; do NOT propose to mathlib.
When the fork is removed (separate cleanup ticket), inline the composition at the two
call sites and delete the lemma.

---

## Next step

Keep `LutzNagell.PID.monic_Φ_sub_smul_ΨSq` as a local helper for now (it is harmless
glue while the project forks mathlib's `Φ`/`ΨSq`). It is NOT a mathlib candidate: it is
a ≤3-call composition of `Polynomial.Monic.sub_of_left` with the division-polynomial
degree lemmas (`leadingCoeff_Φ`, `natDegree_Φ`, `natDegree_ΨSq`) that mathlib already
has. When the DivisionPolynomial fork is retired onto the upstream
`WeierstrassCurve.*` API, inline the composition at its two call sites
(`PIDIntegralMultiple.lean:77`, `GeneralIntegralMultiple.lean:59`) and delete the lemma.
