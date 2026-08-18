# /mathlibable report — `complEDS_eq_aeval`

_Refreshed full single-decl /mathlibable workflow, 2026-06-21. (Supersedes the 2026-06-18 run, which reached the same NO-composable verdict; this revision verifies the root namespace, records the HasseWeil-duplicate call site, and pins current mathlib line numbers.)_

Project: NagellLutz (Nagell–Lutz; elliptic curves; division polynomials; EDS).
File: `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1196`.
This file **forks** `Mathlib.NumberTheory.EllipticDivisibilitySequence` and adds a
`universalNormEDS` / `MvPolynomial Param ℤ` specialization layer that mathlib does
not have. `complEDS_eq_aeval` is part of that layer.

### Baseline (Phase 0)
- lake build:               not re-run (local build stale, per task brief); reasoning from source. Decl elaborates as written (1-line `simp_rw` proof).
- decl `complEDS_eq_aeval`:  ✓ resolved at `EllipticDivisibilitySequence.lean:1196`
- kind:                      lemma (theorem)
- has sorry:                 no
- qualified name:            `complEDS_eq_aeval` — **root namespace**. Verified: line 1196 sits in `section Map` (1116–1201) at the file's outer scope; the `namespace EllSequence` blocks at 1079–1112 and 1356+ do not enclose it (namespace/end scan confirms 1112 closes before 1116 opens `section Map`).
- module docstring summary:  EDS file (forked from mathlib) — defines `IsEllSequence`/`normEDS`/`complEDS₂`/`complEDS'`/`complEDS` and constructs normalised EDSs from initial terms.

### Statement (Phase 1)

`complEDS_eq_aeval` states: for a commutative ring `R` and `b c d : R`, the
complement sequence `complEDS b c d : ℤ → ℤ → R` equals the termwise
specialization, via the algebra evaluation `aeval (Param.rec b c d)`, of the
**universal** complement sequence `complEDS (X B) (X C) (X D)` taken over the
polynomial ring `MvPolynomial Param ℤ` (with `Param = {B, C, D}` and `X·` the
three indeterminates):

  `complEDS b c d = fun m n ↦ aeval (Param.rec b c d) (complEDS (X B) (X C) (X D) m n)`.

In words: every concrete `complEDS` is obtained from the single universal one by
substituting `B ↦ b, C ↦ c, D ↦ d`. This is the EDS-specific instance of the
universal-polynomial-ring substitution principle.

Variables / typeclasses (Lean side):
- `R : Type*` `[CommRing R]`, `b c d : R` — the three EDS parameters.
- `Param` — the project's 3-element index inductive; `Param.rec b c d : Param → R`
  is the assignment realising the substitution.
- `aeval (Param.rec b c d) : MvPolynomial Param ℤ →ₐ[ℤ] R` — the universal map.

Hypotheses (Lean side): none beyond the typeclass `[CommRing R]`.

Conclusion (math): the concrete complement sequence is the pullback/specialization
of the universal one along the ring map `B,C,D ↦ b,c,d`.

Conclusion (Lean): `complEDS b c d = (aeval (Param.rec b c d) <| complEDS (X (R := ℤ) B) (X C) (X D) · ·)`.

### Size classification (Phase 2a)

Verdict: SMALL.
Reason: a one-line glue lemma (`simp_rw [map_complEDS, aeval_X]`) packaging an
immediate corollary of the naturality lemma `map_complEDS`; not a named theorem,
not a new structure, not a `## Main statements` entry.

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` — one-liner check is **n/a**.
(Context: it IS a one-line proof, and one of a 3-member family —
`normEDS_eq_aeval`, `compl₂EDS_eq_aeval`, `complEDS_eq_aeval` — that all just
push `aeval` through the corresponding `map_*` naturality lemma.)

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                    | Query                                                                                          | Hit? | Standard form found | Notes |
|----|----------------------------|------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)  | "EDS universal ring MvPolynomial specialization division-free Stange elliptic net"             | partial | universal-ring + specialize-to-a-point is standard (Stange formulary; division polys live in `ℤ[A₁..A₆][X,Y]` and specialize) | confirms the *technique* is standard; no named lemma "complEDS = aeval of universal complEDS" |
|  2 | WebSearch (general form)   | "normalised EDS as evaluation of universal polynomial ring homomorphism Lean mathlib"          | yes  | mathlib's own DivisionPolynomial uses universal ring `𝓡[X,Y] := ℤ[A₁..A₆][X,Y]` + universal morphism `𝓡[X,Y] → R[X,Y]` mapping `Aᵢ ↦ aᵢ` | the substitution principle is explicitly mathlib's chosen idiom — but applied to division polys, not phrased as an `eq_aeval` lemma on `complEDS` |
|  3 | WebSearch (mathlib naming) | "mathlib EDS normEDS map_normEDS ring homomorphism naturality lemma universal property"        | yes  | mathlib EDS file has `map_preNormEDS/map_normEDS/map_complEDS₂/map_complEDS` (naturality) but no `eq_aeval` / `universalNormEDS` | naturality building blocks exist upstream; the `aeval`-specialization corollary does not |
|  4 | ChatGPT MCP                | (server down per task brief — fallback to WebSearch #1–3 + direct mathlib source read)          | n/a  | covered by source read | the decisive evidence is the mathlib source, read directly below |
|  5 | Local references           | `ls projects/NagellLutz/.mathlib-quality/references/`                                           | n/a  | directory absent     | only `.mathlib-quality/overview` exists; no source-paper PDFs |
|  6 | nLab                       | "elliptic divisibility sequence" / "universal polynomial ring specialization"                  | n/a  | no nLab EDS/division-polynomial page | EDS is number-theoretic; the substitution principle is the universal property of free comm-rings |
|  7 | nCatLab (categorical)      | —                                                                                              | n/a  | not categorical      | a substitution identity; no categorical content beyond `aeval` being the unique alg map |
|  8 | Stacks Project (alg geom)  | "elliptic divisibility sequence" / "division polynomial"                                        | n/a  | not in Stacks        | Stacks has no EDS material |
|  9 | MathOverflow / MSE         | "elliptic divisibility sequence universal ring specialize parameters"                          | partial | specialize-from-universal is folklore | no statement at this lemma's granularity |
| 10 | arXiv (recent)             | Stange "Division Polynomials for Arbitrary Isogenies" (2503.15428, 2025); edsformulary; 0710.1316 (elliptic nets) | yes  | universal/initial polynomials specialised to a point — the standard framework | the framework, not this Lean glue lemma |

### Literature summary (Phase 3)

Concept identified as: the **universal-polynomial-ring specialization principle**
for the EDS complement sequence — "the concrete `complEDS` is the substitution
`B,C,D ↦ b,c,d` applied to the universal `complEDS` over `ℤ[B,C,D]`".

Sources agree on the standard form: yes, at the level of the *technique*.
Specializing a universal/initial object (division polynomials, elliptic nets) to
a point by a ring homomorphism is textbook (Stange's formulary; mathlib's own
DivisionPolynomial universal ring `ℤ[A₁..A₆][X,Y]`). There is **no named
mathematical theorem** in the literature at the granularity "complEDS = aeval ∘
universal complEDS"; it is formalization plumbing that realises the principle.

Most general standard form: for ANY ring-homomorphism-natural family
`g : R → R → R → (index → R)` (i.e. satisfying `f ∘ g b c d = g (f b) (f c) (f d)`),
one has `g b c d = aeval (Param.rec b c d) ∘ g (X B) (X C) (X D)`. `complEDS` is
one instance; `normEDS`, `compl₂EDS`, division polynomials, `preNormEDS`, … are others.

Disagreement with the literature: none. The lemma is correct and is the expected
specialization identity.

### Generality analysis — `complEDS_eq_aeval` (Phase 4)

Literature-standard form: the generic "natural family = aeval of its universal
instance" identity (above).

| # | Parameter / hypothesis | Current Lean form        | Literature-standard form          | Weaker form exists? | Reason |
|---|------------------------|--------------------------|-----------------------------------|---------------------|--------|
| 1 | `[CommRing R]`         | commutative ring         | commutative ring (needs `aeval`)  | NO                  | `aeval`/`MvPolynomial Param ℤ` substitution needs a comm-ring ℤ-algebra; already maximal |
| 2 | the family `complEDS`  | hard-wired to `complEDS` | any `f`-natural 3-param family    | yes (abstract over the family) | proof is literally `map_complEDS` + `aeval_X`; the SAME two lines prove `normEDS_eq_aeval`/`compl₂EDS_eq_aeval` — content is family-agnostic |
| 3 | index `Param` (3 elts) | 3 EDS parameters         | arbitrary finite parameter set    | yes                 | nothing about `complEDS` needs exactly three indeterminates |

### Generality verdict (Phase 4b)

The current form is: STRICTLY NARROWER THAN the abstract principle, but **the
narrowing is the point** — there is no `complEDS`-with-this-signature in mathlib to
attach a general `eq_aeval` lemma to (mathlib's `complEDS` is a different def, see
Phase 5). The "more general form" is not a better *mathlib* lemma; it is a
meta-pattern (`map_* ⊢ *_eq_aeval`) that mathlib deliberately does not bottle —
it inlines `map_*`/`aeval_X` at use sites instead.
Number of weakening opportunities yielding a shippable standalone lemma: 0.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Notes |
|----|--------------------------------------------------------------------------|----------|-------|
|  1 | bundled-hypotheses → typeclasses/instances?                              | no       | already typeclass-driven (`[CommRing R]`) |
|  2 | sequences/metric → filters/topology?                                     | no       | purely algebraic identity, no analysis |
|  3 | construction → universal-property class?                                  | partial  | the lemma already IS the universal-property specialization; `aeval` is the unique-alg-map characterisation. No further class to introduce. |
|  4 | set-with-closure-predicate → bundled substructure?                        | no       | no substructure |
|  5 | vector-space/field-specific → weaken typeclasses?                         | no       | already over a general comm-ring |
|  6 | 1-categorical → higher-categorical?                                       | no       | none |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group?                          | no       | `m n : ℤ` are the EDS indices, intrinsic to the concept |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: no. The lemma already uses the contemporary
`aeval`/`MvPolynomial` substitution idiom (the same idiom mathlib's
DivisionPolynomial file uses for its `ℤ[A₁..A₆]` universal ring). There is no
cleaner reformulation; the only "more general" move is to NOT have the lemma and
inline `map_complEDS`/`aeval_X` — which is precisely the NO-composable verdict.

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or instances introduced).

### Mathlib search-status: `complEDS_eq_aeval` (Phase 5)

[A] Lean-Finder        "complEDS equals aeval universal", "EDS specialize parameters"   no hits (mathlib index)
[B] Loogle             `complEDS _ _ _ = aeval _ _`, `_ = ⇑(aeval _) (complEDS …)`        no hits — no `eq_aeval` for any EDS object in mathlib
[C] LeanSearch         "complement sequence of normalised EDS equals evaluation of universal polynomial sequence"  no hits
[D] Grep mathlib src   `grep -rnE "aeval|universalNormEDS|Param|_eq_aeval" Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`  **empty** — mathlib's EDS file has NO aeval/universal layer at all
[E] Name pattern       `grep -rn "complEDS_eq_aeval\|universalNormEDS\|normEDS_eq_aeval" .lake/.../Mathlib/`  no hits anywhere in mathlib

Searched for BOTH the user's form and the general form:
- User's form (`complEDS = aeval ∘ universal complEDS`): not in mathlib.
- General/precursor form: mathlib **does** have the naturality building block
  `map_complEDS` (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:544`:
  `f (complEDS b c d k n) = complEDS (f b) (f c) (f d) k n`) and `aeval_X`
  (`Mathlib/Algebra/MvPolynomial/Eval.lean:603`). Note mathlib's `complEDS` has
  signature `complEDS b c d k n` (extra fixed multiplier `k`, `ℤ×ℤ→R`) whereas
  the project's `complEDS b c d m n` is built from a generic `compl`/`compl'` —
  a genuine fork. So the project's lemma is *about the project's def*, but its
  proof pattern is exactly mathlib's `map_*` + `aeval_X`.

Concluded: **not in mathlib** as a standalone lemma; mathlib has the **building
blocks** (`map_complEDS`-style naturality + `aeval_X`) from which this 1-line
corollary composes. Mathlib has deliberately not added `*_eq_aeval` wrappers for
the normEDS family.

### Composition check (Phase 6)

#### Call sites — `complEDS_eq_aeval` (Phase 6.0)

Internal use count (within NagellLutz, excluding the declaring file): **0**.
External-to-file callers (NagellLutz): 0.

| Caller file:line                                              | Usage pattern |
|--------------------------------------------------------------|---------------|
| (none in NagellLutz)                                          | —             |

Inline-derivation / duplication grep across the repo (`grep -rn complEDS_eq_aeval`):
- `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:653`
  — an **independent duplicate** of the same lemma (the HasseWeil EDS fork), and
  it **is used** there at line 805 (`(congr_fun₂ (complEDS_eq_aeval b c d) m n).symm`).

So: K=0 inside NagellLutz, but the identical lemma is load-bearing in the parallel
HasseWeil fork. This is the duplicated-track situation the project is known for:
two copies of the same EDS + `universalNormEDS` machinery. The lemma is real API
for the *technique*, just not consumed inside the file that declares this copy.

#### Composition attempt (Phase 6a)

Can `complEDS_eq_aeval` be derived from mathlib in ≤3 chained calls?

Attempt 1 — the project's own proof IS the composition:
```lean
example : complEDS b c d = (aeval (Param.rec b c d) <| complEDS (X (R := ℤ) B) (X C) (X D) · ·) := by
  simp_rw [map_complEDS, aeval_X]
```
- Building blocks used: `map_complEDS` (naturality; mathlib HAS the analogue at
  `EllipticDivisibilitySequence.lean:544`; project's own at line 1156) + `aeval_X`
  (`MvPolynomial/Eval.lean:603`).
- Result: succeeds — 2 rewrite lemmas, no auxiliary reasoning. `map_complEDS`
  rewrites `aeval f (complEDS (X B) (X C) (X D) m n)` to
  `complEDS (aeval f (X B)) … m n`; then `aeval_X` collapses `aeval (Param.rec b c d) (X B) = b`, etc.

Conclusion: **COMPOSABLE**. Two `simp`-lemma rewrites (`map_complEDS`, `aeval_X`),
≤3 calls, no proof in disguise. Per the Phase-6b table this is the
"single-rewrite/naturality + `aeval_X`" pattern, which is composable.

## Verdict: `complEDS_eq_aeval`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature (Phase 3): the universal-ring-specialize-by-ring-hom principle is
  standard (Stange formulary; mathlib's own `ℤ[A₁..A₆][X,Y]` DivisionPolynomial
  universal ring) — but there is no named theorem at this lemma's granularity.
- Generality (Phase 4): the only "more general" form is the meta-pattern
  `map_* ⊢ *_eq_aeval`, which mathlib intentionally inlines rather than bottles.
- Mathlib search (Phase 5): not present; building blocks `map_complEDS`
  (`…/EllipticDivisibilitySequence.lean:544`) + `aeval_X`
  (`…/MvPolynomial/Eval.lean:603`) are present.
- Composition (Phase 6): COMPOSABLE — `by simp_rw [map_complEDS, aeval_X]`.

**Rationale:**

`complEDS_eq_aeval` is formalization plumbing, not a mathematical result: it says
the concrete complement sequence is the substitution of `B,C,D ↦ b,c,d` into the
universal one over `ℤ[B,C,D]`. Its entire content is "push `aeval` through the
naturality lemma, then evaluate `aeval` at the generators" — exactly the two
mathlib rewrites `map_complEDS` and `aeval_X`, with nothing between them. Mathlib
already ships the naturality half (`map_complEDS`, alongside `map_normEDS`,
`map_complEDS₂`, `map_preNormEDS`) and deliberately does **not** carry any
`*_eq_aeval`/`universalNormEDS` wrappers — the universal-ring substitution idiom is
used inline in the DivisionPolynomial development (`𝓡[X,Y] := ℤ[A₁..A₆][X,Y]`),
not packaged as per-sequence specialization lemmas. Adding `complEDS_eq_aeval` (or
the siblings `normEDS_eq_aeval`/`compl₂EDS_eq_aeval`) upstream would duplicate that
inlined pattern with a single-purpose lemma whose proof is shorter than its
statement. The `universalNormEDS` device is a legitimate *proof technique* this
project (and the HasseWeil fork) adopts to reduce EDS identities to a domain where
nonzero terms are non-zero-divisors — but the technique's helper lemmas belong in
the project, applied where the reduction happens, not in mathlib's public API.

One nuance that does **not** change the verdict: mathlib's `complEDS` is a
*different definition* from the project's (mathlib's carries an extra fixed
multiplier `k`; the project's is built from a generic `compl`/`compl'`). So the
lemma as literally stated is about the fork. That makes the case for NO stronger,
not weaker: the right home for an `eq_aeval` fact, if mathlib ever wanted one, is
against mathlib's own `complEDS` via mathlib's own `map_complEDS` — and even then
it would be a 1-line inline, not a lemma.

**WHY not (refactor-actionable):**
Mathlib has the building blocks; the project's form is a ≤2-rewrite composition
of them. Building blocks:
- `map_complEDS` — `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:544`
  (project analogue: `EllipticDivisibilitySequence.lean:1156`).
- `aeval_X` — `Mathlib/Algebra/MvPolynomial/Eval.lean:603`.

Composition sketch (≤3 lines, the project's actual proof):
```lean
-- wherever `complEDS_eq_aeval` is invoked, inline:
by simp_rw [map_complEDS, aeval_X]
-- or, at a `congr_fun₂` use-site (cf. HasseWeil:805):
fun m n ↦ by simp_rw [map_complEDS, aeval_X]   -- gives the pointwise equation directly
```

Call sites to refactor:
- NagellLutz: **K = 0** inside the file — `complEDS_eq_aeval` is declared but not
  consumed in NagellLutz. (It IS used in the HasseWeil duplicate at
  `…/Auxiliary/EllipticDivisibilitySequence.lean:805`.)

Refactor plan / next action (project-local, NOT a mathlib PR):
1. **Do not propose this for mathlib.** It is a project-internal specialization
   helper; mathlib's policy is to inline `map_*`+`aeval_X`.
2. The real cleanup is **dedup across the NagellLutz and HasseWeil forks**: both
   carry their own `Param` / `universalNormEDS` / `normEDS_eq_aeval` /
   `compl₂EDS_eq_aeval` / `complEDS_eq_aeval` / `universalNormEDS_*`. Factor the
   whole `universalNormEDS` layer into one shared `Common/` module (keep the
   helper lemmas, just share them) rather than upstreaming. That is an AINTLIB
   cross-project dedup ticket, not a mathlib contribution.
3. If NagellLutz genuinely never uses its copy (K=0 and no transitive use), it is
   a deletion candidate from NagellLutz once the shared module exists — verify
   against `normEDS_mul_complEDS` (~line 1338), which uses `map_complEDS`/`aeval_X`
   directly (not this lemma) and so is unaffected.

---

## Next step

Do not open a mathlib PR. Treat as an AINTLIB internal-dedup item: factor the
shared `universalNormEDS` layer (`Param`, `universalNormEDS`, `normEDS_eq_aeval`,
`compl₂EDS_eq_aeval`, `complEDS_eq_aeval`, `universalNormEDS_*`) — currently
duplicated between `projects/NagellLutz` and `projects/HasseWeil` — into one
`Common/` module. Where any of these are *used*, the underlying step is the
2-rewrite `simp_rw [map_*, aeval_X]`, so mathlib needs nothing added.
