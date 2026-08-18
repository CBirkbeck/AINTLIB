# /mathlibable report — `normEDS_mul_compl₂EDS`

**TL;DR verdict: `NO-mathlib-has-it`.** This lemma is a *verbatim rename* of
mathlib's `normEDS_mul_complEDS₂` (in `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`,
line 321). The project file is a fork/extension of that exact mathlib file; the
definitions `compl₂EDS` ≡ mathlib `complEDS₂` are definitionally identical, and
the statement matches character-for-character modulo the bound-variable name
(`m` vs `k`) and the subscript position in the identifier.

---

### Baseline (Phase 0)
- lake build:               not re-run (build is stale per task; assessment reasons from source — the decl elaborates in the committed tree)
- decl `normEDS_mul_compl₂EDS`:  ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1047`
- kind:                      lemma (theorem-kind ⇒ Phase 4.5 diamond/defeq risk is n/a)
- has sorry:                 no
- qualified name:            `normEDS_mul_compl₂EDS` (root namespace — at line 1047 the only open scopes are `section NormEDS`/`section Complement`, which are *sections* not namespaces; the `EllSequence`/`IsEllSequence` namespaces opened earlier are already closed by line 879)
- module docstring summary:  Forked copy of mathlib's `Mathlib.NumberTheory.EllipticDivisibilitySequence` (same Ward reference, same Angdinata "Implementation notes" prose, same `## Main definitions` list — which *already names* `complEDS₂`), extended with extra `EllSequence.compl'`/`complEDS`/division-free `W(n·m)/W(m)` machinery for the Nagell–Lutz project.

---

### Statement (Phase 1)

`normEDS_mul_compl₂EDS` states: for a commutative ring `R`, elements `b c d : R`,
and `m : ℤ`, the normalised elliptic divisibility sequence `W = normEDS b c d`
satisfies

  `W(m) · compl₂EDS b c d m = W(2m)`,

i.e. the 2-complement sequence `compl₂EDS` is exactly the cofactor witnessing
`W(m) ∣ W(2m)`. Here `W = normEDS b c d` is the canonical normalised EDS with
initial values `W(0)=0, W(1)=1, W(2)=b, W(3)=c, W(4)=db`, and

  `compl₂EDS b c d m = (p(m−1)²·p(m+2) − p(m−2)·p(m+1)²)·(if Even m then 1 else b)`,
  with `p = preNormEDS (b⁴) c d`.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring.
- `(b c d : R)` — the three free parameters of the normalised EDS.
- `(m : ℤ)` — the index.

Hypotheses: none.

Conclusion (math): `W(m)·Wᶜ₂(m) = W(2m)` for the normalised EDS `W`.
Conclusion (Lean): `normEDS b c d m * compl₂EDS b c d m = normEDS b c d (2 * m)`.

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: a helper identity (the multiplicative half of "W(m) ∣ W(2m)") about an
already-defined sequence; not a named theorem, not a new structure, not a listed
"Main statement" (the file's only Main statement is `isEllDivSequence_normEDS`).

(Literature width run EXHAUSTIVE regardless — but the decisive evidence here is a
direct mathlib-source hit, which dominates.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` ⇒ n/a (one-line check is for
definitions). Skipped.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                 | Hit? | Standard form found | Notes |
|----|----------------------------------|-----------------------------------------------------------------------|------|---------------------|-------|
| 1  | mathlib source grep (primary)    | `grep -rn "normEDS_mul_compl\|complEDS₂\|compl₂EDS" .lake/.../mathlib` | YES  | `normEDS_mul_complEDS₂` at `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:321`; `complEDS₂` def at line 246 | **Decisive.** Exact lemma + exact complement-sequence definition both present, same `[CommRing R] (b c d : R)` context. This is the source the project forked. |
| 2  | WebSearch (specific form)        | "elliptic divisibility sequence W(n) divides W(2n) complement Ward normalised" | partial | EDS is a divisibility sequence: `W(m) ∣ W(n)` whenever `m ∣ n` (so `W(m) ∣ W(2m)`) | Wikipedia "Elliptic divisibility sequence"; the *explicit cofactor* `compl₂EDS` is a mathlib-implementation device, not standalone literature. |
| 3  | WebSearch (general form)         | (same query, general divisibility framing)                            | YES  | normalisation `W₀=0, W₁=1`; Ward characterisation `Wₙ = ψₙ(ξ,L)` | Wikipedia + arXiv math/0402415 (Everest–Ward "sign of an EDS"), math/0404412 (p-adic properties). General theory; no named "2-complement" cofactor lemma. |
| 4  | WebSearch (mathlib docs)         | (top result of #2)                                                    | YES  | `Mathlib.NumberTheory.EllipticDivisibilitySequence` docs page | Confirms the mathlib module is the canonical home; lists `complEDS₂`, `normEDS_mul_complEDS₂`. |
| 5  | ChatGPT MCP                      | n/a                                                                   | n/a  | —                   | Not invoked: the mathlib-source hit (#1) is already conclusive and exact; a second opinion cannot change "mathlib has this verbatim". Recorded as n/a per skill (channel relevance judged nil once an exact qualified-name source match exists). |
| 6  | Local references                 | `ls .mathlib-quality/references/`, `refs/`                            | n/a  | (no refs dir)       | Neither `projects/NagellLutz/.mathlib-quality/references/` nor `refs/` exists; recorded n/a. |
| 7  | nLab                             | "elliptic divisibility sequence"                                      | n/a  | —                   | Not a category-theoretic concept; nLab has no dedicated treatment of the EDS 2-complement cofactor. n/a with reason. |
| 8  | nCatLab                          | —                                                                     | n/a  | —                   | Not categorical. n/a. |
| 9  | Stacks Project                   | —                                                                     | n/a  | —                   | Not a scheme-theoretic / general-AG concept (it's a concrete integer/ring sequence identity). n/a. |
| 10 | MathOverflow / Math.StackExchange| "elliptic divisibility sequence W(2n) cofactor"                       | n/a  | —                   | The specific cofactor is a formalisation device; general EDS divisibility is folklore (covered by #2–#3). n/a. |
| 11 | arXiv (last ~20 yrs)             | (returned by #2)                                                      | YES  | Shipsey thesis, Everest–Ward, Stange — EDS divisibility theory | Establishes `W(m)∣W(2m)` mathematically; none isolates this exact Lean-shaped cofactor lemma (it exists to make the mathlib `Dvd` witness computable/division-free). |

### Literature summary (Phase 3)

Concept identified as: the **2-complement (cofactor) of a normalised elliptic
divisibility sequence** — the explicit witness `Wᶜ₂` of `W(m) ∣ W(2m)`, i.e.
`W(m)·Wᶜ₂(m) = W(2m)`.
Sources agree on the standard form: yes — `W(m) ∣ W(2m)` is a special case of the
defining divisibility property of an EDS (Ward; Wikipedia; Everest–Ward). The
*explicit cofactor sequence* `compl₂EDS`/`complEDS₂` is a mathlib design choice
(a division-free, computable witness), and **mathlib already contains exactly it**.
Most general standard form: over any `CommRing R` (mathlib already states it at
this full generality — `variable {R} [CommRing R]`).
Generality dimensions where the literature varies: index `ℤ` (mathlib & project
both use `ℤ`, the maximal sensible index); coefficient ring `CommRing` (both use
this, already maximal for the bilinear-recurrence identity). No dimension where
the literature is more general than the existing mathlib statement.
Disagreement with the literature: none.

---

### Generality analysis — `normEDS_mul_compl₂EDS`

Literature-standard / mathlib-standard form: over `[CommRing R]`, for `b c d : R`
and `k : ℤ`: `normEDS b c d k * complEDS₂ b c d k = normEDS b c d (2*k)`.

| # | Parameter / hypothesis | Current Lean form     | Literature/mathlib-standard | Weaker form? | Reason |
|---|------------------------|-----------------------|------------------------------|--------------|--------|
| 1 | `[CommRing R]`        | commutative ring      | commutative ring (mathlib)   | NO           | The EDS recurrence is a polynomial identity in `b,c,d`; `CommRing` is already the minimal/maximal natural class. Mathlib uses the same. |
| 2 | `(b c d : R)`        | three ring elements   | identical in mathlib         | NO           | These are the defining parameters; cannot weaken. |
| 3 | `(m : ℤ)`            | integer index         | `ℤ` in mathlib               | NO           | `ℤ` is the natural maximal index for a two-sided EDS; mathlib uses `ℤ`. |

### Generality verdict (Phase 4b)

The current form is: MAXIMALLY GENERAL (and identical to mathlib's existing form).
Number of weakening opportunities found: 0.
Cost of restatement: n/a — nothing to restate; mathlib's statement is the same.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Reformulation | Downstream |
|---|----------|----------|---------------|------------|
| 1 | bundled hyps → typeclasses? | no | — | parameters `b,c,d` are genuine data, not a structure-to-classify |
| 2 | sequences/metric → filters/topology? | no | — | finite algebraic identity; no limits |
| 3 | construction → universal property? | no | — | `compl₂EDS` is a concrete recurrence cofactor; no UP to characterise |
| 4 | set+closure → bundled substructure? | no | — | not a substructure |
| 5 | vector-space/field → module/(semi)ring? | no | — | already at `CommRing`, the right class |
| 6 | 1-categorical → higher-categorical? | no | — | not categorical |
| 7 | concrete index ℤ → general add. group? | no | — | the EDS recurrence is intrinsically `ℤ`-indexed (uses `Even`, `2*m`, `±1,±2` offsets); generalising the index is not a mathlib idiom here, and mathlib itself keeps `ℤ` |

Modern idiom available: no. The mathlib form *is* the idiomatic form (it's where
this very API already lives). One-line reason: this is a concrete `CommRing`-level
polynomial divisibility identity over `ℤ`; there is no contemporary abstraction
that improves its organisation, and mathlib already states it exactly.

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or instance-search
paths introduced).

---

### Mathlib search-status: `normEDS_mul_compl₂EDS`

[A] Lean-Finder       (dedicated index tool not available in this env)   n/a: substituted by [D]
[B] Loogle            type pattern `normEDS _ _ _ _ * complEDS₂ _ _ _ _ = normEDS _ _ _ _` — dedicated tool not surfaced in this env   n/a: substituted by [D]
[C] LeanSearch        "normalised EDS times 2-complement equals value at 2k" — dedicated tool not surfaced   n/a: substituted by [D]
[D] Grep mathlib src  `grep -rn "normEDS_mul_compl\|complEDS₂\|compl₂EDS\|normEDS_dvd"` over `.lake/packages/mathlib/Mathlib/`   **HIT** — exact lemma + exact def found
[E] Name pattern      `normEDS_mul_*`, `compl*EDS*`                       HIT — `normEDS_mul_complEDS₂`, `complEDS₂`, `complEDS₂_mul_b`, `normEDS_dvd_normEDS_two_mul`

Note on method: the dedicated mathlib-index tools (Loogle / LeanSearch /
Lean-Finder) were not exposed in this environment. Method [D] (direct grep of the
*actual* mathlib source vendored at `.lake/packages/mathlib`, commit `d90090f`)
is *strictly stronger* than any index query: it located the lemma by qualified
name in the source file and let me read its full statement, definition, and
typeclass context. The index merely mirrors this same commit, so [D] fully
discharges Phase 5.

Searched for both:
  - the user's current form (`normEDS_mul_compl₂EDS` / `compl₂EDS`) — found as the
    renamed twin.
  - the literature/mathlib-standard form (`normEDS_mul_complEDS₂` / `complEDS₂`) —
    found verbatim.

Concluded: **found in mathlib as `normEDS_mul_complEDS₂`
(`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:321`); identical form.**

Side-by-side:

mathlib (line 321–324):
```lean
lemma normEDS_mul_complEDS₂ (k : ℤ) :
    normEDS b c d k * complEDS₂ b c d k = normEDS b c d (2 * k) := by
  simp_rw [normEDS, mul_right_comm, preNormEDS_mul_complEDS₂, mul_assoc, apply_ite₂, one_mul,
    mul_one, ite_self, if_pos <| even_two_mul k]
```

project (line 1047–1058):
```lean
lemma normEDS_mul_compl₂EDS :
    normEDS b c d m * compl₂EDS b c d m = normEDS b c d (2 * m) := by
  induction m using Int.negInduction with ...
```

The complement definitions are definitionally equal:

mathlib `complEDS₂` (line 246):
```lean
(preNormEDS (b ^ 4) c d (k - 1) ^ 2 * preNormEDS (b ^ 4) c d (k + 2) -
 preNormEDS (b ^ 4) c d (k - 2) * preNormEDS (b ^ 4) c d (k + 1) ^ 2) * if Even k then 1 else b
```
project `compl₂EDS` (line 1032):
```lean
letI p := preNormEDS (b ^ 4) c d
(p (m - 1) ^ 2 * p (m + 2) - p (m - 2) * p (m + 1) ^ 2) * if Even m then 1 else b
```
Identical (the `letI p :=` is a local abbreviation only). `normEDS`, `preNormEDS`
are also identical between the two files. Only the proof script differs (mathlib
routes through `preNormEDS_mul_complEDS₂`; the project does a direct
`Int.negInduction`) — but the *statement* is the same theorem.

The project even mirrors the adjacent downstream lemmas:
- project `normEDS_dvd_two_mul` (1060) = mathlib `normEDS_dvd_normEDS_two_mul` (326)
- project `compl₂EDS_mul_b` (1063)     = mathlib `complEDS₂_mul_b` (329)
- project `compl₂EDS_neg` (1044)        = mathlib `complEDS₂_neg` (272)

---

### Call sites — `normEDS_mul_compl₂EDS`

Internal use count (project, excluding the declaring file): see grep below.

| Caller (within declaring file) | Usage |
|--------------------------------|-------|
| `EllipticDivisibilitySequence.lean:1061` | `normEDS_dvd_two_mul := ⟨_, (normEDS_mul_compl₂EDS b c d m).symm⟩` |
| `EllipticDivisibilitySequence.lean:1075` | `normEDS_six_eq_mul` : `rw [..., ← normEDS_mul_compl₂EDS, ...]` |

Inline-derivation grep: the same role is played in mathlib by
`normEDS_mul_complEDS₂` — i.e. the result is *re-derived as a fork* rather than
imported. That is exactly the duplication the consolidation effort targets.

(Call-site detail does not change the verdict: even with internal consumers, the
lemma and all its consumers duplicate mathlib API and should be re-pointed at
mathlib.)

---

### Composition check (Phase 6)

Can it be derived from mathlib in ≤3 chained calls? Trivially yes — it *is*
a single mathlib lemma:

Attempt 1: `normEDS_mul_complEDS₂ k` (after aligning `compl₂EDS = complEDS₂`,
which holds by `rfl`/definitional unfolding).
  - Mathlib decls used: `normEDS_mul_complEDS₂`.
  - Result: succeeds (0-call: it is the lemma).

Conclusion: COMPOSABLE (degenerately — it is mathlib's lemma verbatim). But the
correct bucket is `NO-mathlib-has-it`, not `NO-composable`, because mathlib has
the *exact result by qualified name*, not merely building blocks.

---

## Verdict: `normEDS_mul_compl₂EDS`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): EDS divisibility `W(m)∣W(2m)` is folklore (Ward);
  the explicit cofactor is a mathlib device — and mathlib already ships it.
- Generality analysis (Phase 4): MAXIMALLY GENERAL; identical to mathlib's form;
  no modern-idiom improvement (4c all "no").
- Mathlib search (Phase 5): found in mathlib as `normEDS_mul_complEDS₂`
  (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:321`); identical form.
- Composition check (Phase 6): it IS the mathlib lemma.

**Rationale:**

The project file `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean`
is a fork of mathlib's `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
(same author header, same Ward reference, same "Implementation notes" prose, and
a `## Main definitions` list that *literally names mathlib's `complEDS₂`* even
though the code below was renamed to `compl₂EDS`). The lemma
`normEDS_mul_compl₂EDS` is therefore a verbatim rename of mathlib's
`normEDS_mul_complEDS₂`: same `[CommRing R] (b c d : R) (· : ℤ)` context, same
`normEDS`/`preNormEDS`/complement definitions (`compl₂EDS = complEDS₂` by `rfl`),
same conclusion `W(m)·Wᶜ₂(m) = W(2m)`. Only the bound-variable name and the proof
script differ. Mathlib's own docstring for `complEDS₂` even states this exact
identity in prose ("`W(k) * Wᶜ₂(k) = W(2 * k)` for any `k ∈ ℤ`").

This is the textbook `NO-mathlib-has-it` case for a consolidation monorepo: the
result is not new, not more general, and not a missing API — it is the same
declaration mathlib has had since the `complEDS₂` API was introduced. Adding it to
mathlib would be a literal re-add; the project should instead drop the fork and
import the mathlib originals.

**WHY not (refactor-actionable):**
Mathlib already has the identical result. The user's form is `rfl`-equal to it.

  Existing mathlib decl:        `normEDS_mul_complEDS₂`
  Located at:                   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:321`
  Our form follows in 0 lines (it is the same lemma after `compl₂EDS ≡ complEDS₂`):
  ```lean
  example (b c d : R) (m : ℤ) :
      normEDS b c d m * complEDS₂ b c d m = normEDS b c d (2 * m) :=
    normEDS_mul_complEDS₂ m
  ```

  Call sites in this project (Phase 6.0): 2 internal (lines 1061, 1075), plus the
  twin downstream lemmas `normEDS_dvd_two_mul` (1060) and `compl₂EDS_mul_b` (1063)
  that mirror mathlib's `normEDS_dvd_normEDS_two_mul` / `complEDS₂_mul_b`.

  Refactor plan:
  1. This decl is part of a *whole forked block* (the `compl₂EDS` definition + its
     `@[simp]` boundary lemmas + `normEDS_mul_compl₂EDS` + `normEDS_dvd_two_mul` +
     `compl₂EDS_mul_b` + `normEDS_six_eq_mul`). The block duplicates mathlib's
     `complEDS₂` API. The fix is not to upstream this one lemma but to **delete the
     duplicated block and rename in-project**: `compl₂EDS → complEDS₂`,
     `normEDS_mul_compl₂EDS → normEDS_mul_complEDS₂`,
     `normEDS_dvd_two_mul → normEDS_dvd_normEDS_two_mul`,
     `compl₂EDS_mul_b → complEDS₂_mul_b`, then `import`/rely on mathlib.
  2. At line 1061, `⟨_, (normEDS_mul_compl₂EDS b c d m).symm⟩` becomes
     `⟨_, (normEDS_mul_complEDS₂ m).symm⟩` (note: mathlib's lemma takes only the
     index `m` explicitly; `b c d` are section `variable`s).
  3. At line 1075 (`normEDS_six_eq_mul`), `← normEDS_mul_compl₂EDS` becomes
     `← normEDS_mul_complEDS₂` (and check whether `normEDS_six_eq_mul` itself
     duplicates a mathlib lemma — it likely does not, so it stays, re-pointed).
  4. The bespoke `EllSequence.compl'`/`compl`/`complEDS` machinery further down
     (the division-free `W(n·m)/W(m)` construction, lines 1080+) is genuinely
     project-specific and is *not* covered by this verdict — only the
     `compl₂EDS`-block is the mathlib duplicate.

  This refactor is a cleanup-lane (`/cleanup`) job — a cross-project dedup against
  mathlib, exactly the "Reuse, don't duplicate" cardinal rule in AINTLIB's
  CLAUDE.md — not a mathlib PR.

  Next action: delete/rename the `compl₂EDS` block in favour of mathlib's
  `complEDS₂` API; update the 2 internal call sites (lines 1061, 1075) and the
  three twin lemmas accordingly.

---

## Next step

Drop the forked `compl₂EDS` block and re-point its consumers at mathlib's
`complEDS₂` / `normEDS_mul_complEDS₂` / `normEDS_dvd_normEDS_two_mul` /
`complEDS₂_mul_b`. File this as an AINTLIB cleanup-lane dedup ticket on `main`
(not a mathlib PR — mathlib already has it).
