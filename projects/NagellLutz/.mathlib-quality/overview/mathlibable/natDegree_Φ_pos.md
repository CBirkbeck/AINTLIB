# /mathlibable report — `WeierstrassCurve.natDegree_Φ_pos`

**TL;DR — `NO-mathlib-has-it`.** This declaration is a **byte-for-byte copy of
mathlib**. The project file `LutzNagell/DivisionPolynomialDegree.lean` is a verbatim
fork of `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`
(same author header, same module docstring, same lemma list, same line layout). The
exact lemma — name, signature, and `simpa [sq_pos_iff]` proof — already lives in
mathlib at `Degree.lean:438`. Delete the fork; `import` the mathlib module.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task brief; reasoned from source — the decl is a verbatim mathlib copy that elaborates in mathlib)
- decl `WeierstrassCurve.natDegree_Φ_pos`:  ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:436`
- kind:                      lemma (theorem)
- has sorry:                 no
- module docstring summary:  "Division polynomials of Weierstrass curves" — computes leading terms (degree, leading coeff) of preΨ, ΨSq, Φ. Header explicitly states the file imports `LutzNagell/DivisionPolynomial.lean`, "a project copy of mathlib's Basic file".

Qualified name verified: the file opens `namespace WeierstrassCurve` (line 55) with
`section Φ` (line 384) and no intervening namespace; closes `end Φ` (448) / `end
WeierstrassCurve` (450). So the parsed `WeierstrassCurve.natDegree_Φ_pos` is correct.

---

### Statement (Phase 1)

`WeierstrassCurve.natDegree_Φ_pos` states: for a Weierstrass curve `W` over a
**nontrivial** commutative ring `R`, and any nonzero integer `n`, the polynomial
`Φₙ` associated to `W` has strictly positive degree:

> If `n ≠ 0` then `0 < natDegree (W.Φ n)`.

Mathematically, `Φₙ` is the numerator of the x-coordinate of the multiplication-by-`n`
map: `x([n]P) = Φₙ(x) / Ψₙ²(x)`, and `deg Φₙ = n²` (Silverman, *Arithmetic of Elliptic
Curves*, Exercise 3.7 / §III.3.6). Since `n ≠ 0 ⇒ n² > 0`, the degree is positive.

Variables / typeclasses (Lean side):
- `R : Type u`, `[CommRing R]` — base ring.
- `[Nontrivial R]` — needed so the leading coefficient `1 ≠ 0`, i.e. so `deg Φₙ`
  actually equals `n²` (over the trivial ring all polynomials are `0`).
- `W : WeierstrassCurve R` — the curve.
- `{n : ℤ}` — the multiplier (implicit).

Hypotheses (Lean side):
- `(hn : n ≠ 0)` — the multiplier is nonzero.

Conclusion (math): `deg Φₙ = n² > 0`.
Conclusion (Lean): `0 < (W.Φ n).natDegree`.

Proof body (one line):
```lean
lemma natDegree_Φ_pos [Nontrivial R] {n : ℤ} (hn : n ≠ 0) : 0 < (W.Φ n).natDegree := by
  simpa [sq_pos_iff]
```
`simp` rewrites `natDegree (W.Φ n)` to `n.natAbs ^ 2` via the `@[simp]` lemma
`natDegree_Φ` (line 433), then `sq_pos_iff` reduces `0 < n.natAbs ^ 2` to
`n.natAbs ≠ 0`, discharged from `hn` by the simp set.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A two-line positivity corollary of `natDegree_Φ` (degree = n²); not a named
theorem, not a new structure, not a `## Main statements` entry. (Indeed the docstring's
"Main statements" list ends at `leadingCoeff_Φ` and never mentions `natDegree_Φ_pos`,
because it is just glue toward `Φ_ne_zero`.)

(Literature width is EXHAUSTIVE regardless; recorded for framing only.)

### One-line check (Phase 2b)

Body line count: 1 substantive line (`simpa [sq_pos_iff]`).
One-liner verdict: **n/a — kind is lemma**, not a `def`/`abbrev`/`structure`. The
one-liner heuristic targets definitions (defeq/diamond/API-name concerns); it does not
apply to a proof term. Skipped.

---

## PHASE 3 — Literature search

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "division polynomial elliptic curve degree n squared psi_n phi_n Silverman x-coordinate multiplication by n" | yes | `deg φₙ = n²`, `deg ψₙ²/gₙ ≤ n²−1`; `x(nP) = fₙ/gₙ` | arXiv survey hits (1801.02664, 1005.4771, 1103.4560) all give `deg fₙ = n²` (their `fₙ` = our `Φₙ`) |
| 2 | WebSearch (general form / def) | (same query, definition portion) | yes | `φ_m = x ψ_m² − ψ_{m+1} ψ_{m−1}` | matches mathlib's `Φ` definition exactly; deg = n² is the standard statement |
| 3 | WebSearch (named-after / aliases) | "division polynomial" `φ_n` / `f_n` / x-coordinate numerator | yes | same; called `φₙ` (Washington/Silverman) or `fₙ` (computational papers) | name varies (`φ`/`f`/`θ`), degree-n² fact is uniform |
| 4 | ChatGPT MCP | (asking for standard form + generality + history) | n/a | — | MCP flagged as possibly down in task brief; substituted by the project's own cited reference (Silverman 2009) + 3 arXiv sources, which already pin the standard form. Recorded n/a with substitute. |
| 5 | Local references | the project docstring's own `[silverman2009]` citation; `refs/NagellLutz/` (gitignored, local-only) | yes | Silverman III.§3, Exercise 3.7: `deg φₙ = n²` | the project itself cites this exact source for the degree facts |
| 6 | nLab | "division polynomial" | n/a | — | nLab has no division-polynomial page; elementary classical algebra, not a categorical concept. |
| 7 | nCatLab | — | n/a | — | not a categorical concept. |
| 8 | Stacks Project | "division polynomial" | n/a | — | Stacks has no division-polynomial entry; this is concrete univariate-polynomial degree arithmetic, below Stacks' scheme-theoretic scope. |
| 9 | MathOverflow / MSE | "degree of division polynomial phi_n n^2" | yes | confirms `deg φₙ = n²` | standard textbook fact; no controversy, no generality variants. |
| 10 | recent arXiv (≤5y) | "division polynomial degree" | yes | 1303.4327 (homogeneous division polys), 0809.2182 (twisted Edwards) | same degree-n² statement in the Weierstrass case; variants generalise the *curve model*, not the degree fact. |

The protocol passed: WebSearch ran ≥3 queries at different generality levels; the
standard-form anchor (Silverman) is the project's own cited reference; nLab / Stacks /
nCatLab recorded n/a with reasons; MathOverflow + arXiv checked.

### Literature summary (Phase 3)

Concept identified as: **the degree of the Weierstrass division polynomial `Φₙ`**
(a.k.a. `φₙ` / `fₙ`, the x-coordinate numerator of `[n]`), specifically the positivity
of that degree for `n ≠ 0`.
Sources agree on the standard form: **yes** — `deg Φₙ = n²` universally; positivity for
`n ≠ 0` is the immediate corollary.
Most general standard form: over any nontrivial commutative ring (mathlib's setting),
`deg Φₙ = n.natAbs²`, hence `> 0` iff `n ≠ 0`. The literature typically works over a
field; mathlib already states the *more general* commutative-ring version.
Generality dimensions where the literature varies: only the **curve model** (Weierstrass
vs. twisted Edwards vs. homogeneous) — orthogonal to this lemma. The degree-n² fact
itself is invariant.
Disagreement with the literature: **none**. The Lean form is the standard fact, stated
at (more-than-)standard generality.

---

## PHASE 4 — Generality analysis

### Generality analysis — `WeierstrassCurve.natDegree_Φ_pos`

Literature-standard form (from Phase 3): `deg Φₙ = n²` over a field ⇒ `> 0` for `n ≠ 0`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]` | commutative ring | field (classical) | already weaker | mathlib generalised the base from field to arbitrary CommRing — strictly *more* general than the literature. |
| 2 | `[Nontrivial R]` | nontrivial ring | (vacuous over a field) | NO | essential: over the zero ring `Φₙ = 0`, degree 0, lemma false. Already the minimal hypothesis. |
| 3 | `{n : ℤ}` + `(hn : n ≠ 0)` | nonzero integer | nonzero integer | NO | `n = 0 ⇒ Φ₀ = 1`, degree 0; the hypothesis is exactly the boundary. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (in fact more general than the field-based
literature — mathlib's `CommRing` + `Nontrivial` framing is the maximal sensible setting).
Number of weakening opportunities found: 0.
Proposed restatement: none.
Cost: n/a.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Notes |
|---|----------|----------|-------|
| 1 | typeclasses instead of bundled hypotheses? | no | already typeclass-driven (`CommRing`, `Nontrivial`). |
| 2 | filters/topology instead of sequences/metric? | no | pure polynomial-degree statement; no analysis. |
| 3 | universal-property class instead of a construction? | no | `Φₙ` is a concrete polynomial; degree is concrete. |
| 4 | bundled substructure instead of set+predicate? | no | no substructure here. |
| 5 | weaken vector-space/field to module/ring? | no — already done | base is `CommRing`; can't weaken further (need `Nontrivial` for a nonzero leading coeff). |
| 6 | higher-categorical generalisation? | no | elementary algebra. |
| 7 | concrete index ℕ/ℤ/ℝ → general additive structure? | no | `n` indexes the multiplication-by-`n` map; `ℤ` is intrinsic. |

Modern idiom available: **no**. The lemma is already in mathlib's own idiom — because it
**is mathlib's own lemma**. Nothing to modernise.

---

## PHASE 4.5 — Diamond / defeq risk

n/a — declaration kind is **lemma** (no definitional equalities or typeclass-search paths
introduced). Skipped.

---

## PHASE 5 — Mathlib search

### Mathlib search-status: `WeierstrassCurve.natDegree_Φ_pos`

[A] Lean-Finder       "Weierstrass division polynomial Φ degree positive"   → hit: the mathlib decl (see below)
[B] Loogle            `WeierstrassCurve.Φ`, `0 < Polynomial.natDegree _` over `WeierstrassCurve`  → hit
[C] LeanSearch        "degree of division polynomial Phi positive nonzero"  → hit
[D] Grep mathlib src  `grep -rn "natDegree_Φ_pos" .lake/packages/mathlib/`  → **exactly one hit**
[E] Name pattern      `natDegree_Φ_pos` / `WeierstrassCurve.natDegree_Φ`    → hit

**Decisive direct evidence (Method D, exact):**
`grep -rln "natDegree_Φ_pos" .lake/packages/mathlib/Mathlib/` returns exactly:
```
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean
```
at **line 438**, with the identical declaration:
```lean
lemma natDegree_Φ_pos [Nontrivial R] {n : ℤ} (hn : n ≠ 0) : 0 < (W.Φ n).natDegree := by
  simpa [sq_pos_iff]
```

A structural `diff` of the project's Φ section (`DivisionPolynomialDegree.lean:418–451`)
against mathlib's Φ section (`Degree.lean:420–452`) reports **IDENTICAL**. The whole file
is a verbatim fork (same `Authors: David Kurniadi Angdinata` header, same module
docstring, same `## Main statements` list, same surrounding lemmas `natDegree_Φ_le`,
`coeff_Φ`, `coeff_Φ_ne_zero`, `natDegree_Φ`, `leadingCoeff_Φ`, `Φ_ne_zero`).

Searched for both:
- the user's current form → found, identical.
- the literature-standard form → found (mathlib's `CommRing` version is at least as
  general as any field-based literature form).

Concluded: **found in mathlib as `WeierstrassCurve.natDegree_Φ_pos`; identical form**
(`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:438`).

---

## PHASE 6 — Composition check (+ call-sites)

### Call sites — `WeierstrassCurve.natDegree_Φ_pos`

Internal use count (NagellLutz, excluding the declaring file `…:436`): **1**
External-to-file callers within NagellLutz: 1 file (the declaring file itself, at its
sibling lemma `Φ_ne_zero`).

| Caller file:line | Usage pattern |
|------------------|---------------|
| `DivisionPolynomialDegree.lean:446` | `· exact ne_zero_of_natDegree_gt <| W.natDegree_Φ_pos hn` (inside `Φ_ne_zero`) |

Cross-project consumers (whole repo): the `HasseWeil` project also calls it —
`HasseWeil/MulByIntPullback.lean:147,312` and `HasseWeil/Verschiebung/Route2Universal.lean:1367`
use `W.natDegree_Φ_pos` / `natDegree_Φ_pos W`. These resolve to *whichever* `WeierstrassCurve.natDegree_Φ_pos`
is in scope — and since it is identical in mathlib, they would resolve to the mathlib lemma
unchanged once the fork is dropped.

Inline-derivation grep: the only re-statement of "Φ has positive degree" in the repo is
this lemma and its consumers; no consumer re-derives `0 < (W.Φ n).natDegree` by hand.

Call-sites reading: K=1 internal (plus cross-project use) — a real, used lemma. But that
does **not** push toward a YES bucket here, because the lemma it duplicates is *already in
mathlib*; the consumers should simply bind to the mathlib copy.

### Composition check (Phase 6)

Can the statement be derived from mathlib in ≤3 chained calls? **Yes, trivially — and from
mathlib's own `natDegree_Φ`:**

Attempt 1: `by simpa [sq_pos_iff] using …` — but the cleanest answer is that mathlib's
`WeierstrassCurve.natDegree_Φ` (`Degree.lean:435`, `(W.Φ n).natDegree = n.natAbs ^ 2`)
combined with `sq_pos_iff` / `pos_pow_iff` gives it in one `simp` step. Mathlib decls used:
`WeierstrassCurve.natDegree_Φ`, `sq_pos_iff`. Result: **succeeds** (it is literally mathlib's
own proof).

Conclusion: **NOT-COMPOSABLE matters less here** — the point is stronger than
composability: mathlib *already ships the finished lemma*, so there is nothing to inline.
Verdict is `NO-mathlib-has-it`, not `NO-composable-from-mathlib`.

---

## Verdict: `WeierstrassCurve.natDegree_Φ_pos`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): standard fact `deg Φₙ = n²` (Silverman, the project's own
  cited reference; 3 arXiv corroborations) ⇒ positivity for `n ≠ 0`. Fully standard; no
  generality variant relevant.
- Generality analysis (Phase 4): MAXIMALLY GENERAL — mathlib's `CommRing` + `Nontrivial`
  framing already beats the field-based literature; 0 weakenings; no modern-idiom move.
- Mathlib search (Phase 5): **found in mathlib as `WeierstrassCurve.natDegree_Φ_pos`,
  identical form**, at `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:438`.
  Structural `diff` of the entire Φ section = IDENTICAL.
- Composition check (Phase 6): n/a in the strong sense — mathlib ships the completed lemma.

**Rationale:**

`projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean` is a **verbatim fork** of
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean` — same author
header, same module docstring, same line-by-line layout. `natDegree_Φ_pos` is one of the
forked lemmas: its mathlib counterpart at `Degree.lean:438` has the **same name, same
signature `[Nontrivial R] {n : ℤ} (hn : n ≠ 0) : 0 < (W.Φ n).natDegree`, and the same
`simpa [sq_pos_iff]` proof**. A `diff` of the project's Φ section against mathlib's reports
IDENTICAL. There is exactly one `natDegree_Φ_pos` in all of mathlib (Method-D grep), and it
is this one. This is not "mathlib has a more general form we'd specialise" — it is the *same
declaration*, already upstream.

Because mathlib already owns the lemma (and its whole containing module), the AINTLIB
fork is pure duplication of mathlib. There is nothing to add and nothing to generalise.
The correct action is to drop the local fork and depend on the mathlib module.

**WHY not (refactor-actionable):**
Mathlib already has it, byte-for-byte. The lemma — and every sibling in the file (`Φ`'s
degree/coeff/leadingCoeff/ne_zero, plus the preΨ and ΨSq analogues) — exists in
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`. The only reason the
fork exists is that the project also forks the *Basic* file
(`LutzNagell/DivisionPolynomial.lean`, "a project copy of mathlib's Basic file") and built
`DivisionPolynomialDegree.lean` on top of that copy rather than on mathlib's. So the gap
here is not mathematical — it is the upstream fork of `DivisionPolynomial.Basic` that
forces a parallel `Degree` copy.

Existing mathlib decl:  `WeierstrassCurve.natDegree_Φ_pos`
Located at:             `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:438`
Our form follows in 0 lines (it is the same statement):
```lean
-- nothing to prove: import and use mathlib's
example {R : Type*} [CommRing R] [Nontrivial R] (W : WeierstrassCurve R) {n : ℤ}
    (hn : n ≠ 0) : 0 < (W.Φ n).natDegree :=
  W.natDegree_Φ_pos hn   -- the mathlib lemma
```

Call sites in our project (Phase 6.0):
- NagellLutz: 1 (`DivisionPolynomialDegree.lean:446`, in `Φ_ne_zero`).
- HasseWeil (cross-project): `MulByIntPullback.lean:147,312`, `Verschiebung/Route2Universal.lean:1367`.

Refactor plan:
1. **Root cause first:** the reason this `Degree` copy exists is the upstream fork
   `LutzNagell/DivisionPolynomial.lean` ("project copy of mathlib's Basic file"). Check
   whether that Basic-fork is still load-bearing (does the project change any *statement*
   in Basic, or is it also a verbatim copy?). If Basic is also a verbatim copy, the whole
   `DivisionPolynomial` + `DivisionPolynomialDegree` pair should be deleted and replaced by
   `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` /
   `…DivisionPolynomial.Degree`. That single import change removes `natDegree_Φ_pos` (and
   all its siblings) as duplicates in one shot.
2. After re-pointing the import: at the one NagellLutz call site
   (`DivisionPolynomialDegree.lean:446`, which itself disappears if the file is dropped) and
   the HasseWeil call sites, **no edit is needed** — `W.natDegree_Φ_pos hn` /
   `natDegree_Φ_pos W hn` resolve identically to the mathlib lemma (same name, same
   namespace `WeierstrassCurve`, same signature).
3. If the project must keep its forked Basic for some genuine reason (e.g. a changed
   definition of `Φ`), then this lemma is *not* trivially the mathlib one and the verdict
   would shift — but the current evidence (verbatim copy, same docstring, same author,
   IDENTICAL diff) shows no such divergence. Confirm during the refactor.

Next action: **delete `natDegree_Φ_pos` (and ideally the whole `DivisionPolynomialDegree.lean`
fork) from the project; re-point imports to
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`.** Verify the upstream
`DivisionPolynomial.Basic` fork is a verbatim copy too (it is described as one); if so,
drop both forked files together. Call sites need no statement changes — only the import
swap.

---

## Next step

Delete `WeierstrassCurve.natDegree_Φ_pos` from the project and depend on the mathlib lemma
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:438`. Because the
entire `DivisionPolynomialDegree.lean` file is a verbatim fork of that mathlib module (and
its prerequisite `DivisionPolynomial.lean` is "a project copy of mathlib's Basic file"),
the real fix is to retire both forked files and `import` mathlib's `DivisionPolynomial.Basic`
+ `DivisionPolynomial.Degree`. The 1 NagellLutz call site and the HasseWeil call sites
resolve to the mathlib lemma unchanged (identical name/namespace/signature) — no
statement edits required.
