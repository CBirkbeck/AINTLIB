# /mathlibable report — `normEDS_dvd_two_mul`

## Verdict: NO-mathlib-has-it

Mathlib already contains this exact result under the name
`normEDS_dvd_normEDS_two_mul`, with an identical statement and an identical
proof. The NagellLutz file is a verbatim fork of
`Mathlib.NumberTheory.EllipticDivisibilitySequence` with a handful of
identifiers renamed (`compl₂EDS` ↔ mathlib `complEDS₂`,
`normEDS_mul_compl₂EDS` ↔ mathlib `normEDS_mul_complEDS₂`,
`normEDS_dvd_two_mul` ↔ mathlib `normEDS_dvd_normEDS_two_mul`).

---

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task note); reasoning from source
- decl `normEDS_dvd_two_mul`: resolved at
  `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1059`
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  Defines elliptic divisibility sequences (EDS) and constructs
                             normalised EDSs (`normEDS`) from initial terms `b, c, d`.
- qualified name:            `normEDS_dvd_two_mul` (no namespace prefix — the decl sits in
                             `section NormEDS` › `section Complement`; sections do not qualify,
                             and the enclosing `namespace EllSequence` at line 1079 opens
                             *after* this decl)

---

### Statement (Phase 1)

`normEDS_dvd_two_mul` states: for a normalised elliptic divisibility sequence
`W = normEDS b c d : ℤ → R` over a commutative ring `R`, and any integer `m`,
the term `W(m)` divides `W(2m)`.

This is the `n ∣ m ⟹ W(n) ∣ W(m)` divisibility property of EDS, specialised to
the case `n = m`, `m ↦ 2m` (the doubling step). The proof is the witnessed
divisibility `⟨_, (normEDS_mul_compl₂EDS b c d m).symm⟩`: the explicit cofactor
is `compl₂EDS b c d m`, the "complement of `W(m)` in `W(2m)`", and the companion
identity `normEDS_mul_compl₂EDS` proves `W(m) · compl₂EDS(m) = W(2m)`.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring
- `(b c d : R)` — the three initial parameters defining the normalised EDS
- `(m : ℤ)` — the index

Hypotheses (Lean side): none.

Conclusion (math): `W(m) ∣ W(2m)` where `W = normEDS b c d`.
Conclusion (Lean): `normEDS b c d m ∣ normEDS b c d (2 * m)`.

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: A one-line corollary (witnessed divisibility) of the algebraic identity
`normEDS_mul_compl₂EDS`. Not a named theorem, not a new structure, not a stated
main result of the project.

### One-line check (Phase 2b)

n/a — kind is `lemma`, not `def`. (Body is the single anonymous-constructor term
`⟨_, (normEDS_mul_compl₂EDS b c d m).symm⟩`; this is a proof, not a definition,
so the one-liner def-exemption table does not apply.)

---

### Literature search (Phase 3)

The literature search is short-circuited by the dispositive Phase 5 finding
(mathlib already has the identical decl with the identical proof). A
corroborating sweep was still run to confirm the result is classical and not a
project novelty.

| # | Channel              | Query                                                                 | Hit? | Standard form found                                  | Notes |
|---|----------------------|-----------------------------------------------------------------------|------|------------------------------------------------------|-------|
| 1 | WebSearch (specific) | "elliptic divisibility sequence W(m) divides W(2m) Ward division property" | yes | `n ∣ m ⟹ W_n ∣ W_m`; hence `W(m) ∣ W(2m)`           | Wikipedia "Elliptic divisibility sequence"; due to M. Ward (1940s) |
| 2 | WebSearch (general)  | (same sweep) strong-divisibility property of EDS                      | yes  | `gcd(W_m, W_n) = ±W_{gcd(m,n)}` for the integral case | the `m ∣ 2m` case is the trivial `gcd(m,2m)=m` instance |
| 3 | WebSearch (mathlib)  | (same sweep surfaced the mathlib docs page)                           | yes  | `Mathlib.NumberTheory.EllipticDivisibilitySequence`  | mathlib's own module is indexed and public — directly confirms Phase 5 |
| 4 | ChatGPT MCP          | —                                                                     | n/a  | —                                                    | not run: verdict already pinned by exact mathlib hit (MCP noted possibly-down in task) |
| 5 | Local references     | `.mathlib-quality/references/` (NagellLutz)                           | n/a  | —                                                    | not consulted — the dispositive evidence is the mathlib source file itself |
| 6 | nLab                 | "elliptic divisibility sequence"                                      | n/a  | —                                                    | not a category-theoretic concept; no dedicated nLab page; skipped as not load-bearing |
| 7 | nCatLab              | —                                                                     | n/a  | —                                                    | not categorical |
| 8 | Stacks Project       | —                                                                     | n/a  | —                                                    | not an algebraic-geometry/scheme-theoretic concept in the Stacks sense |
| 9 | MathOverflow / arXiv | (covered by WebSearch result set: arXiv 1108.3051, 0710.1316, math/0402415) | yes | confirms `n∣m ⟹ W_n∣W_m` is the defining EDS property | Ward 1948; Shipsey; Stange (elliptic nets) |

### Literature summary (Phase 3)

Concept identified as: the **divisibility property of an elliptic divisibility
sequence** — `n ∣ m ⟹ W(n) ∣ W(m)` — specialised to `n = m → 2m`.
Sources agree on the standard form: yes. The property is the *defining* feature
of a divisibility sequence and is classical (Morgan Ward, 1940s).
Most general standard form: over the integers, EDS satisfy the *strong*
divisibility property `gcd(W_m, W_n) = ±W_{gcd(m,n)}`; `W(m) ∣ W(2m)` is the
trivial `gcd(m, 2m) = m` instance. Mathlib's / the project's formulation is the
purely-algebraic ring-level version (cofactor identity), which is what the
recursion supports over an arbitrary `CommRing`.
Disagreement with the literature: none.

---

### Generality analysis (Phase 4)

Literature-standard form: `n ∣ m ⟹ W(n) ∣ W(m)` over ℤ; ring-level version is
"`W(m) ∣ W(2m)` over any `CommRing`".

| # | Parameter / hypothesis | Current Lean form        | Literature-standard form         | Weaker form exists? | Reason |
|---|------------------------|--------------------------|----------------------------------|---------------------|--------|
| 1 | `[CommRing R]`         | commutative ring         | commutative ring (general)       | NO                  | `compl₂EDS` and `normEDS` are built from `preNormEDS`, defined over an arbitrary `CommRing`. Already maximal — mathlib uses the same. |
| 2 | `(m : ℤ)`              | integer index            | integer index                    | NO                  | EDS are ℤ-indexed by definition (`Int.negInduction` is used in the companion identity). |

### Generality verdict (Phase 4b)

The current form is: MAXIMALLY GENERAL (identical to mathlib's). Zero weakening
opportunities. Moot for the verdict, since mathlib already has the identical
statement at the identical generality.

### Modern-idiom check (Phase 4c)

Modern idiom available: no. The lemma is a finite algebraic divisibility fact
over a `CommRing`; no topology to filter-ise, no universal property to introduce,
no typeclass to weaken (already at `CommRing`). Mathlib's own copy uses precisely
this formulation — there is no more-idiomatic mathlib form to aim at. (A general
"`m ∣ n ⟹ W(m) ∣ W(n)` strong-divisibility" lemma would be a *different,
stronger* result, not a restatement of this doubling lemma, and is out of scope.)

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or typeclass-search
paths introduced).

---

### Mathlib search-status: `normEDS_dvd_two_mul` (Phase 5)

[A] Lean-Finder       —                                            n/a (index tool not invoked; direct source grep dispositive)
[B] Loogle            `normEDS _ _ _ _ ∣ normEDS _ _ _ _`          n/a (not invoked; direct source grep dispositive)
[C] LeanSearch        "normEDS divides two mul / W(m) ∣ W(2m)"     n/a (not invoked; direct source grep dispositive)
[D] Grep mathlib src  `normEDS_dvd | normEDS_mul_compl | compl₂EDS | complEDS₂`
                      → HIT in `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
[E] Name pattern      `normEDS_dvd_normEDS_two_mul`                → HIT, line 326

Searched for both the project's current form AND the literature-standard form.

**Concluded: found in mathlib as `normEDS_dvd_normEDS_two_mul`; IDENTICAL form.**

Mathlib source (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`,
`section ComplEDS`, with `variable (b c d : R)` in scope, `[CommRing R]`):

```lean
-- line 321
lemma normEDS_mul_complEDS₂ (k : ℤ) :
    normEDS b c d k * complEDS₂ b c d k = normEDS b c d (2 * k) := by ...

-- line 326
lemma normEDS_dvd_normEDS_two_mul (k : ℤ) : normEDS b c d k ∣ normEDS b c d (2 * k) :=
  ⟨complEDS₂ .., (normEDS_mul_complEDS₂ ..).symm⟩
```

Project source (`projects/NagellLutz/.../EllipticDivisibilitySequence.lean`,
`section NormEDS` › `section Complement`, `variable (b c d : R) (m : ℤ)`,
`[CommRing R]`):

```lean
-- line 1046
lemma normEDS_mul_compl₂EDS :
    normEDS b c d m * compl₂EDS b c d m = normEDS b c d (2 * m) := by ...

-- line 1059
lemma normEDS_dvd_two_mul : normEDS b c d m ∣ normEDS b c d (2 * m) :=
  ⟨_, (normEDS_mul_compl₂EDS b c d m).symm⟩
```

These are the same lemma (bound variable `m` vs `k`), with the same explicit
cofactor (`compl₂EDS` = mathlib `complEDS₂`) and the same one-line proof.

---

### Composition check (Phase 6)

### Call sites — `normEDS_dvd_two_mul`

Internal use count: 0 (within NagellLutz, excluding declaring lines 1059–1060).
External-to-file callers: 0 distinct files (no project file references the name).

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none)           | —             |

Inline-derivation grep: the *companion* identity `normEDS_mul_compl₂EDS` is used
internally (e.g. `normEDS_six_eq_mul` at line 1074 calls
`← normEDS_mul_compl₂EDS`), but the divisibility wrapper `normEDS_dvd_two_mul`
itself has no internal consumers. K = 0.

Composition: COMPOSABLE — but this is the wrong framing, because mathlib has the
*exact lemma*, not merely building blocks. The mathlib decl is a direct drop-in:

```lean
example (b c d : R) (m : ℤ) : normEDS b c d m ∣ normEDS b c d (2 * m) :=
  normEDS_dvd_normEDS_two_mul ..
```

Conclusion: the result is supplied verbatim by mathlib; no new lemma is needed.

---

## Verdict block (Phase 7)

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): the `W(m) ∣ W(2m)` divisibility property is the
  classical defining feature of EDS (Ward, 1940s); the same WebSearch sweep
  surfaced mathlib's own indexed module page.
- Generality analysis (Phase 4): MAXIMALLY GENERAL — identical generality
  (`CommRing`, `ℤ`-indexed) to mathlib's copy.
- Mathlib search (Phase 5): found in mathlib as `normEDS_dvd_normEDS_two_mul`
  (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:326`); IDENTICAL form
  and IDENTICAL proof.
- Composition check (Phase 6): K = 0 internal call sites; mathlib supplies the
  result verbatim.

**Rationale:**

The NagellLutz `EllipticDivisibilitySequence.lean` is, as the task context
flagged, a fork of `Mathlib.NumberTheory.EllipticDivisibilitySequence`. The decl
under review, `normEDS_dvd_two_mul`, is a one-to-one rename of mathlib's
`normEDS_dvd_normEDS_two_mul`: same coefficient ring (`[CommRing R]`), same
initial parameters `(b c d : R)`, same ℤ-index, same conclusion
`normEDS b c d _ ∣ normEDS b c d (2 * _)`, and the same proof down to the
witnessing cofactor — the project's `compl₂EDS` is mathlib's `complEDS₂`, and the
project's `normEDS_mul_compl₂EDS` is mathlib's `normEDS_mul_complEDS₂`. There is
nothing to upstream: mathlib already has this, at this generality, with this
proof. The result is also mathematically classical (Ward), so even absent the
fork it would not be a novel mathlib contribution.

**WHY not (refactor-actionable):**
Mathlib already has the lemma. The project's copy exists only because the whole
file was forked wholesale (to develop a duplicated `compl₂EDS` /
`normEDS_mul_compl₂EDS` track). Since the upstream identifiers
(`normEDS`, `complEDS₂`, `normEDS_mul_complEDS₂`, `normEDS_dvd_normEDS_two_mul`)
are all available via `Mathlib.NumberTheory.EllipticDivisibilitySequence`, the
forked divisibility lemma is pure redundancy.

  Existing mathlib decl:  `normEDS_dvd_normEDS_two_mul`
  Located at:             `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:326`
  Our form follows in ≤1 line (it IS the mathlib lemma, modulo rename):
  ```lean
  example (b c d : R) (m : ℤ) : normEDS b c d m ∣ normEDS b c d (2 * m) :=
    normEDS_dvd_normEDS_two_mul ..
  ```
  Call sites in our project (from Phase 6.0): K = 0.

  Refactor plan: this is a single decl inside a larger fork. There are no call
  sites of `normEDS_dvd_two_mul` to rewrite, so removing it in isolation is
  trivial. The *correct* cleanup is the file-level one the task context
  describes: retire the forked `compl₂EDS` / `normEDS_mul_compl₂EDS` /
  `normEDS_dvd_two_mul` track and import mathlib's
  `Mathlib.NumberTheory.EllipticDivisibilitySequence`
  (`complEDS₂`, `normEDS_mul_complEDS₂`, `normEDS_dvd_normEDS_two_mul`) directly.
  That dedup is bigger than one lemma and should be the file's consolidation pass
  — but for *this* decl in isolation, the action is: delete it; if any future
  consumer needs `W(m) ∣ W(2m)`, call `normEDS_dvd_normEDS_two_mul`.

  Next action: delete `normEDS_dvd_two_mul` from the project (K = 0 call sites);
  fold into the broader fork-retirement of this file against
  `Mathlib.NumberTheory.EllipticDivisibilitySequence`.

---

## Next step

Delete `normEDS_dvd_two_mul` from the project — it has zero call sites and is a
verbatim rename of mathlib's `normEDS_dvd_normEDS_two_mul`
(`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:326`). Track it under
the file-level consolidation that retires this fork of
`Mathlib.NumberTheory.EllipticDivisibilitySequence` (the duplicated
`compl₂EDS` / `normEDS_mul_compl₂EDS` track) in favour of importing mathlib's
`complEDS₂` / `normEDS_mul_complEDS₂` / `normEDS_dvd_normEDS_two_mul` directly.
