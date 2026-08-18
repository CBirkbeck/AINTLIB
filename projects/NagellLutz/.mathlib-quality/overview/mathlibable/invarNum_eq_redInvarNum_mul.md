# /mathlibable report — `EllSequence.invarNum_eq_redInvarNum_mul`

Project: NagellLutz (Nagell–Lutz; elliptic curves; division polynomials; EDS).
File: `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1372`.
Date: 2026-06-21.

---

### Baseline (Phase 0)
- lake build:               not run (local build is stale per task brief); assessment reasons from source. Text-grep over the vendored mathlib (`.lake/packages/mathlib/`) is authoritative and build-independent.
- decl `EllSequence.invarNum_eq_redInvarNum_mul`:  ✓ resolved at `EllipticDivisibilitySequence.lean:1372`, inside `namespace EllSequence` (opened line 1356) — so the qualified name is confirmed `EllSequence.invarNum_eq_redInvarNum_mul`.
- kind:                      lemma (theorem).
- has sorry:                 no.
- module docstring summary:  "Elliptic divisibility sequences (EDS) and the construction of normalised EDSs from initial terms." Ref: M. Ward, *Memoir on Elliptic Divisibility Sequences*.

---

### Statement (Phase 1)

`EllSequence.invarNum_eq_redInvarNum_mul` states, for a commutative ring `R` and `b c d : R`, `m : ℤ`:

> The invariant numerator of the canonical normalised EDS `W = normEDS b c d` at scale parameter `s = 1` factors as `redInvarNum b c d m * b`, where `b = W(2)`.

In symbols, with `W = normEDS b c d`:
```
invarNum W 1 m  =  redInvarNum b c d m · b
```
where (definitions in the same file):
- `invarNum W s n := (W(n+2s)·W(n-s)² + W(n+s)²·W(n-2s))·W(s)² + W(n)³·W(2s)²`  (line 140),
  whose purpose is that `invarNum W s n / invarDenom W s n` is independent of `n` (an x-coordinate-style invariant of the elliptic sequence);
- `invarDenom W s n := W(n+s)·W(n)·W(n-s)`  (line 145);
- `redInvarNum b c d m := compl₂EDS b c d m + normEDS b c d m ^ 3 * b + 2 * compl₂EDSAux b c d m`  (line 1364), the "reduced" numerator obtained by cancelling a factor of `b` (`= W₂`; the docstring at line 1362 says it is "obtained by cancelling `W₃W₂ = b*c` from `invarNum`").

The proof is one `simp_rw [...] ; ring`: it unfolds `redInvarNum`, distributes (`right_distrib`), rewrites the three project lemmas `compl₂EDS_mul_b`, `compl₂EDSAux_mul_b`, `invarNum_normEDS` (which supply `compl₂EDS·b`, `compl₂EDSAux·b`, and the explicit `invarNum` of `normEDS`), then closes by `ring`.

Variables / typeclasses (Lean side):
- `R : Type u`, `[CommRing R]` — the coefficient ring (fully general commutative ring).
- `b c d : R` — the three EDS initial parameters (`W₂=b`, `W₃=c`, `W₄=d·b`).
- `m : ℤ` — the index.

Hypotheses: none.

Conclusion (math): the s=1 invariant numerator of `normEDS b c d` has `b` as an explicit factor, with cofactor `redInvarNum`.
Conclusion (Lean): `invarNum (normEDS b c d) 1 m = redInvarNum b c d m * b`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**.
Reason: a helper `ring`-identity bridging two file-local definitions (`invarNum`, `redInvarNum`) for the canonical EDS; not a named theorem, not a `## Main statement` (the file's only listed main statement is `isEllDivSequence_normEDS`), and not the introduction of a new mathematical structure.

(Literature width is EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → one-liner check **n/a**. (The body is a 2-line `simp_rw … ; ring`.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|---------------------|-------|
| 1  | WebSearch (specific form)        | "elliptic divisibility sequence invariant numerator denominator x-coordinate division polynomial psi"  | partial | x(nP)=φ_n/ψ_n², no "invariant numerator = reduced × W₂" identity | Wikipedia EDS, Stange elliptic nets, p-adic-EDS papers; the standard object is φ_n, not this packaging |
| 2  | WebSearch (general/named)         | "Ward EDS W(n) division polynomial x-coordinate formula ψ_{n+1} ψ_{n-1}"                                | partial | φ_n = X·ψ_n² − ψ_{n+1}ψ_{n-1}; core recursion W_{n+m}W_{n−m}W_r²=… | Ward 1940s; confirms φ_n is the canonical x-coord numerator; no "redInvarNum × b" |
| 3  | WebSearch (modern / nLab-style)   | "nLab elliptic divisibility sequence division polynomial recurrence reduced invariant factor"          | no   | (concept name only)  | nLab has no dedicated EDS page; new paper "On Elliptic Sequences over Commutative Rings" (arXiv 2604.05280) studies EDS over CommRing but states no such factorization |
| 4  | WebSearch (mathlib/Angdinata)     | "division polynomial normalised EDS b c d Angdinata Lean mathlib invariant numerator"                  | yes  | mathlib defines ψ_n via normEDS, φ_n := X·ψ_n²−ψ_{n+1}ψ_{n-1} | The mathlib EDS/division-poly API is by Angdinata; it carries φ_n, **not** invarNum/redInvarNum |
| 5  | ChatGPT MCP                      | self-contained question: is "invarNum(normEDS,1,m)=redInvarNum·b" a named/standard result vs internal factorization? | n/a (down) | — | ChatGPT/Codex MCP errored out (warned by task brief). Compensated by channels 1–4 + direct mathlib source reading. |
| 6  | Local references                 | `projects/NagellLutz/.mathlib-quality/references/`                                                      | n/a  | (no references dir)  | dir absent; `refs/` symlink absent — recorded n/a |
| 7  | nLab                             | elliptic divisibility sequence / division polynomial                                                   | no   | —                    | no EDS-specific nLab entry; not a categorical concept |
| 8  | nCatLab (categorical)            | —                                                                                                      | n/a  | —                    | n/a — purely an algebraic identity, nothing categorical |
| 9  | Stacks Project                   | —                                                                                                      | n/a  | —                    | n/a — Stacks has no EDS / division-polynomial-recurrence material |
| 10 | MathOverflow / Math.SE           | (covered by WebSearch #1–3)                                                                             | no   | —                    | no posting states this specific cancellation identity |
| 11 | recent arXiv (≤5 yr)             | "On Elliptic Sequences over Commutative Rings" (2604.05280); "A recurrence relation for EDS" (2102.07573); Stange isogeny division polys (2503.15428) | partial | EDS over CommRing, recurrences, φ_n | These are the closest modern sources; none introduce an "invariant numerator/denominator" pair nor its b-reduction |

**Protocol pass check:** WebSearch ran 4 distinct queries across generality levels (specific packaging, named/Ward, modern/nLab, mathlib-author); ChatGPT MCP attempted (server down — documented); local refs checked (absent); nLab/nCatLab/Stacks/MathOverflow/arXiv each checked or n/a-with-reason. ✓

### Literature summary (Phase 3)

Concept identified as: the **x-coordinate invariant of an elliptic (divisibility) sequence**. The literature-standard object is the division-polynomial x-coordinate numerator `φ_n = X·ψ_n² − ψ_{n+1}·ψ_{n-1}` (with `x(nP) = φ_n/ψ_n²`), together with the Ward recurrence.
Sources agree on the standard form: **yes** for `φ_n`; but the project's `invarNum`/`invarDenom` ("`invarNum/invarDenom` is constant in `n`") is a *non-standard, project-specific repackaging* of the addition/x-coordinate invariant — no surveyed source uses this exact pair.
Most general standard form: `φ_n` over any base ring (mathlib already has it).
Generality dimensions where the literature varies: base ring (ℤ for Ward → arbitrary CommRing in mathlib and arXiv 2604.05280). The project is already at "arbitrary CommRing".
Disagreement with the literature: the *specific factored identity* `invarNum(normEDS,1,m) = redInvarNum·b` is **not present in any source** — it is a formalization-internal cancellation of the common factor `b = W₂`. It is bookkeeping en route to the project's invariant identities, not a textbook lemma.

---

### Generality analysis — `EllSequence.invarNum_eq_redInvarNum_mul`

Literature-standard form: there is no literature statement of this identity to compare against; the comparable mathlib-side object (`φ_n`) is already maximally general (arbitrary base ring).

| # | Parameter / hypothesis | Current Lean form | Literature-standard | Weaker form exists? | Reason |
|---|------------------------|-------------------|---------------------|---------------------|--------|
| 1 | `[CommRing R]`         | arbitrary commutative ring | arbitrary commutative ring | NO | already maximal; the identity is a `ring` fact, needs nothing weaker |
| 2 | `b c d : R`            | free parameters of `normEDS` | same | NO | these ARE the EDS data; can't be weakened |
| 3 | `m : ℤ`               | integer index | integer index | NO | EDS is ℤ-indexed by definition |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (arbitrary `CommRing`, no spurious hypotheses). There are 0 weakening opportunities. This does not, however, argue for inclusion — the statement is *about project-local definitions* (`invarNum`, `redInvarNum`) that do not exist in mathlib.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Reformulation | Downstream |
|---|----------|----------|---------------|------------|
| 1 | bundled-hyp → typeclass? | no | — | no "let X be a foo" preamble; just `ring` data |
| 2 | sequences/metric → filters/topology? | no | — | finite algebraic identity; nothing topological |
| 3 | construction → universal property? | no | — | it's an equation between two expressions, not a construction |
| 4 | set+closure → bundled substructure? | no | — | n/a |
| 5 | vector-space/field-specific → weaker typeclass? | no | — | already arbitrary CommRing |
| 6 | 1-categorical → higher-categorical? | no | — | n/a |
| 7 | concrete index ℕ/ℤ/ℝ → arbitrary monoid? | no | — | EDS is intrinsically ℤ-indexed; generalising the index is not meaningful |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. This is a finite commutative-ring identity between two file-local expressions; there is no Bourbaki-2.0 reformulation that improves mathlib's organisation. (Reason: the only "modern" object in the vicinity is mathlib's already-present `φ_n`, and the right move is to *use* that, not to repackage `invarNum`.)

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or typeclass-search paths introduced). Skipped.

---

### Mathlib search-status: `EllSequence.invarNum_eq_redInvarNum_mul`

[A] Lean-Finder       — (MCP not available in this env) — n/a; compensated by [D]/[E] source grep
[B] Loogle            — (MCP not available in this env) — n/a; compensated by [D]/[E] source grep
[C] LeanSearch        — (MCP not available in this env) — n/a; compensated by [D]/[E] source grep
[D] Grep mathlib src  `invarNum|invarDenom|redInvarNum|redInvarDenom|Rel₃|invar_of_net` over `.lake/packages/mathlib/Mathlib/`  → **0 hits anywhere in mathlib**
[E] Name pattern      `Invar`/`invar` in `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/` and the EDS file  → **0 hits**

Cross-check (what mathlib *does* have): `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` has `normEDS`, `complEDS₂`, `complEDS`, `preNormEDS`, `normEDS_mul_complEDS₂`, `complEDS₂_mul_b`, etc.; `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` has `WeierstrassCurve.ψ` (line 401) and `WeierstrassCurve.φ` (line 448, `= X·ψ_n² − ψ_{n+1}ψ_{n-1}`). **None** of `invarNum`, `invarDenom`, `redInvarNum`, `redInvarDenom` appears — neither the lemma nor the definitions it mentions exist upstream.

Searched for both: (a) the user's exact form — absent; (b) the literature-standard x-coordinate object `φ_n` — present in mathlib, but it is a *different* packaging and there is no `φ_n`-stated analogue of "numerator = reduced × b".

Concluded: **not in mathlib** (grep methods [D]/[E] exhausted; the defining objects `invarNum`/`redInvarNum` are project-original; the related standard object `φ_n` exists but carries no analogous factorization lemma).

---

### Call sites — `EllSequence.invarNum_eq_redInvarNum_mul`

Internal use count (NagellLutz, excluding the declaring file): **0**.
In-file use: **1** — `EllipticDivisibilitySequence.lean:1504`, inside `redInvarNum_eq_redInvarDenom_mul`:
```
rw […, ← invarNum_eq_redInvarNum_mul, invar₂_normEDS, invarDenom_eq_redInvarDenom_mul]
```
External-to-project callers: 0 (NagellLutz).

| Caller file:line | Usage pattern |
|------------------|---------------|
| LutzNagell/EllipticDivisibilitySequence.lean:1504 | `← invarNum_eq_redInvarNum_mul` (rewrite, same file) |

Inline-derivation grep (re-derived elsewhere without using this lemma?):
- **Duplicate found (separate project):** `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:860–863` is the SAME lemma (`EllSequence.invarNum (normEDS b c d) 1 m = redInvarNum b c d m * b`, same `ring` proof via `complEDS₂_mul_b`/`complEDSAux₂_mul_b`/`invarNum_normEDS`), used identically at HasseWeil:993. This is the project's known duplicated cross-project fork track — confirming the lemma is bespoke EDS-invariant scaffolding copied between two NT projects, **not** a mathlib import.

What the call-site pattern tells us: K=0 external + exactly one same-file consumer (and a hand-copied twin in HasseWeil). Per the Phase-6 table this is the "wrong-abstraction / could-be-inlined" signal — a private bridge lemma, not a reusable public API.

---

### Composition check (Phase 6)

Can `invarNum_eq_redInvarNum_mul` be derived in ≤3 chained calls?

Attempt 1 — **from mathlib primitives:** impossible. Mathlib has neither `invarNum` nor `redInvarNum` (Phase 5), so there is no mathlib expression whose composition could even state this, let alone prove it. Result: **fails** (the objects are project-only).

Attempt 2 — **from the project's own exported API:** the lemma is `redInvarNum`-unfold + `compl₂EDS_mul_b` + `compl₂EDSAux_mul_b` + `invarNum_normEDS`, then `ring`. That is a trivial ≤4-rewrite `ring` glue between file-local lemmas. Within the project it is essentially a one-step consequence of definitions; it is not standalone mathematical content.

Conclusion: **NOT-COMPOSABLE-from-mathlib** (because the requisite building blocks `invarNum`/`compl₂EDS_mul_b`/… are absent from mathlib), AND trivially composable from the project's own local lemmas (so within the project it is mere glue). Both facts point the same way: this is internal scaffolding, not a mathlib candidate.

---

## Verdict: `EllSequence.invarNum_eq_redInvarNum_mul`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the standard object is `φ_n = X·ψ_n² − ψ_{n+1}ψ_{n-1}`; no source states an "invarNum = redInvarNum · W₂" cancellation — it is a formalization-internal factoring of the common factor `b = W₂`.
- Generality analysis (Phase 4): MAXIMALLY GENERAL (arbitrary CommRing), but about project-only definitions; no modern-idiom improvement.
- Mathlib search (Phase 5): not in mathlib; moreover the definitions it mentions (`invarNum`, `redInvarNum`) are absent from mathlib (0 grep hits), while mathlib's analogous `φ_n` carries no such lemma.
- Composition check (Phase 6): NOT-COMPOSABLE from mathlib primitives (the building blocks don't exist upstream); trivially composable from the project's own `compl₂EDS_mul_b` + `compl₂EDSAux_mul_b` + `invarNum_normEDS` + `ring`.

**Rationale:**

This lemma is internal bookkeeping for the NagellLutz EDS development, not a mathlib candidate. Its statement is phrased entirely in terms of two definitions — `invarNum` and `redInvarNum` — that exist only in this project (and its hand-copied HasseWeil twin); mathlib has neither, and instead works with the standard division-polynomial x-coordinate numerator `WeierstrassCurve.φ`. The mathematical content is the trivial observation that the s=1 invariant numerator of the canonical normalised EDS contains a factor of `b = W₂`, which the project divides out to define `redInvarNum`; the proof is a single `ring` after rewriting three project lemmas. It has zero external call sites, exactly one same-file consumer, and is duplicated verbatim in another project — the textbook profile of a private glue lemma. There is nothing here for mathlib to "have": the right upstream object (`φ_n`) is already present, and this identity is a step the project introduces purely to manage its own `invarNum`/`redInvarNum` API.

I classify it **NO-composable-from-mathlib** with one honest caveat, recorded explicitly so the verdict is not over-claimed: the ≤3-call composition that discharges it uses the *project's own* lemmas, not mathlib's (mathlib lacks the `invarNum` machinery entirely). The actionable consequence is therefore **not** "inline a mathlib composition at call sites" but rather **"keep it local; do not upstream"** — the lemma should remain a private helper inside the project's EDS file. (It is not a `NO-mathlib-has-it`, since mathlib provably does not have it; and it is not `BORDERLINE`, since there is no genuine taste/policy judgment to escalate — it is unambiguously project-internal scaffolding about non-mathlib definitions.)

**WHY not (refactor-actionable):**
- Mathlib does not, and should not, carry `invarNum`/`redInvarNum`; the standard, already-present object is `WeierstrassCurve.φ` (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:448`). The lemma is a `ring` bridge between two file-local defs, used once, in the same file.
- Building blocks (all **project-local**, NOT mathlib): `EllSequence.compl₂EDS_mul_b` (line 1062), `EllSequence.compl₂EDSAux_mul_b` (line 1025), `EllSequence.invarNum_normEDS` (line 972), plus `def redInvarNum` (line 1364).
- Composition sketch (already the actual proof, ≤4 rewrites + `ring`):
  ```lean
  example : invarNum (normEDS b c d) 1 m = redInvarNum b c d m * b := by
    simp_rw [redInvarNum, right_distrib, compl₂EDS_mul_b, mul_assoc 2 _ b,
      compl₂EDSAux_mul_b, invarNum_normEDS]; ring
  ```
- Call sites in the project (Phase 6.0): K = 0 external; 1 same-file (`:1504`).
- Refactor plan: **none toward mathlib.** Leave the lemma where it is as a private helper (consider marking `private`/`@[local]` consistent with neighbouring helpers, and de-duplicating against the identical HasseWeil copy if the projects are ever consolidated — a *cross-project dedup* cleanup ticket, not a mathlib PR).
- Next action: **do not submit to mathlib.** Optionally file an AINTLIB `lane:cleanup` dedup ticket to unify the NagellLutz and HasseWeil copies of the `invarNum`/`redInvarNum` block.

---

## Next step

Do not upstream. Keep `EllSequence.invarNum_eq_redInvarNum_mul` as a local helper in the project's EDS file. If desired, open an AINTLIB cross-project dedup cleanup ticket to merge the duplicated `invarNum`/`redInvarNum` machinery shared with `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean`.
