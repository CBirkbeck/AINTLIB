# /mathlibable report — `compl₂EDSAux_neg_two`

> Step-9 mathlibable assessment, NagellLutz project (Nagell–Lutz; elliptic curves;
> division polynomials; elliptic divisibility sequences). Single declaration.
> Reasoned from source + this repo's pinned mathlib (`.lake/packages/mathlib`).
> Local Lean build is stale, so no live `exact?`/in-editor `loogle` — but the pinned
> mathlib source is ground truth for "is this symbol/lemma present", and every claim
> below cites it by file:line.

---

## Baseline (Phase 0)

- lake build:               not run (stale per task brief); reasoned from pinned source
- decl `compl₂EDSAux_neg_two`: resolved at
  `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1023`
  (the task said line 1024; the actual `@[simp] lemma` is on **line 1023**)
- **qualified name:**        `compl₂EDSAux_neg_two` (root namespace — NO prefix)
  - Verification: the file's `namespace EllSequence … end EllSequence` closes at line 597;
    line 599 does `open EllSequence`. Between line 597 and line 1023 the only `namespace`
    opened is `IsEllSequence` (643), closed at 702. `PreNormEDS`, `NormEDS`, and
    `Complement` (where this lemma lives, opened line 1010) are **`section`s, not
    `namespace`s**. So the decl is at file root; the true qualified name is exactly
    `compl₂EDSAux_neg_two`.
- kind:                      `lemma` (carries `@[simp]`)
- has sorry:                 no
- module docstring summary:  "Elliptic divisibility sequences" — defines EDS and builds
  the normalised EDS `normEDS`. This file is a **fork** of
  `Mathlib.NumberTheory.EllipticDivisibilitySequence`, extended with a parallel
  `compl₂EDS` / `compl₂EDSAux` "Complement" track plus the `ω` (omega) division-polynomial
  machinery (`redInvarNum`, `DivisionPolynomialOmega.ω`).

---

## Statement (Phase 1)

`compl₂EDSAux_neg_two` is the boundary value, at `m = -2`, of a project-local auxiliary
sequence:

> For the auxiliary expression `compl₂EDSAux b c d m` attached to a normalised elliptic
> divisibility sequence over a commutative ring `R`, evaluating at `m = -2` gives `-d`.

The underlying definition (line 1016–1017):

```lean
def compl₂EDSAux : R :=
  preNormEDS (b ^ 4) c d (m - 2) * preNormEDS (b ^ 4) c d (m + 1) ^ 2 * if Even m then 1 else b
```

The lemma (line 1023):

```lean
@[simp] lemma compl₂EDSAux_neg_two : compl₂EDSAux b c d (-2) = -d := by simp [compl₂EDSAux]
```

Variables / typeclasses:
- `{R : Type u} [CommRing R]` (file top, line 85) — the coefficient ring.
- `(b c d : R)` — the initial-data parameters of a normalised EDS
  (`W 2 = b`, `W 3 = c`, `W 4 = d·b`).

Hypotheses: none (evaluation at the literal `-2`).

Conclusion (math): writing `p = preNormEDS(b⁴,c,d)`, at `m = -2` the parity factor is `1`
(`-2` is even) and the value is `p(-4)·p(-1)²`. Since `p(1)=1, p(4)=d` with odd-index
negation, `p(-1)²=(-1)²=1` and `p(-4)=-p(4)=-d`, giving `-d`.

Conclusion (Lean): `compl₂EDSAux b c d (-2) = -d`.

**Mathematical role.** `compl₂EDSAux` is **the subtrahend (one of the two summands) of the
2-complement**. Compare the project's own `compl₂EDS` (line 1031–1033):

```lean
def compl₂EDS : R :=
  letI p := preNormEDS (b ^ 4) c d
  (p (m - 1) ^ 2 * p (m + 2) - p (m - 2) * p (m + 1) ^ 2) * if Even m then 1 else b
```

`compl₂EDSAux` is exactly the `p(m-2)·p(m+1)²·[…]` piece subtracted inside `compl₂EDS`. Its
docstring: it "appears in the definition of the numerator of the reduced invariant and in
the definition of the `ω` family of division polynomials." So it exists purely to support
the project's `ω` development (`DivisionPolynomialOmega.lean`, `ZSMul.lean`) — the
Nagell–Lutz scalar-multiplication track.

The lemma is the `compl₂EDSAux` analogue of the boundary value `compl₂EDS b c d 2 = d`
(project line 1041) = `complEDS₂ b c d 2 = d` (mathlib line 259).

---

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a single boundary-value evaluation (`compl₂EDSAux(-2) = -d`) of an auxiliary
definition; a one-step `simp` corollary, not a named theorem and not a main result.

(Literature width was run EXHAUSTIVE regardless — see Phase 3.)

## One-line check (Phase 2b)

Kind is `lemma`, not `def` — the one-liner-def gate does not apply. Note: the **proof** is a
one-liner (`by simp [compl₂EDSAux]`) and the statement is a literal evaluation — a strong
"glue, not standalone-mathlib-bound" signal carried into Phase 7. The *parent* `compl₂EDSAux`
is itself a one-line `def`; its mathlib fate (and hence this lemma's) is tied to whether the
`ω` machinery is upstreamed.

---

## Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                      | Query                                                                 | Hit? | Standard form found | Notes |
|----|------------------------------|-----------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)    | "elliptic divisibility sequence W(2m) divisible W(m) complement division polynomial recurrence" | yes  | complement `Wᶜ` with `W(k)·Wᶜ(k,n)=W(nk)` | matched mathlib's own `complEDS₂` doc verbatim; Wikipedia + Leiden cmeds.pdf + Stange "Elliptic nets" |
|  2 | WebSearch (general form)     | "Angdinata mathlib elliptic divisibility sequence complEDS₂ complement formalization division polynomial omega" | yes  | normalised-EDS over commutative rings; `ωₙ` auxiliary | arXiv 2604.05280 "On Elliptic Sequences over Commutative Rings" + the Angdinata mathlib PR; confirms *univariate division polynomials omit a factor of the bivariate 2-division polynomial* — exactly the `compl₂EDSAux`/`ω` bookkeeping role |
|  3 | WebSearch (named-after/alias)| Morgan Ward EDS / "complement sequence" / "2-complement"              | yes  | Ward 1948 recurrence | the *complement* is standard; its individual *summand* is not classically named |
|  4 | ChatGPT MCP                  | n/a — schema loaded, not invoked                                      | n/a  | —                   | The source evidence (project def vs. mathlib def, byte-for-byte) is conclusive; a second opinion on "the standard form of one summand of a complement formula" adds nothing the source doesn't settle. Deliberate skip, not omission. |
|  5 | Local references             | no source-paper PDF for EDS complements in repo refs                  | n/a  | —                   | `.mathlib-quality/` holds process docs, not an EDS reference PDF |
|  6 | nLab                         | "elliptic divisibility sequence" / "division polynomial"              | no   | —                   | no nLab page; not a categorical concept |
|  7 | nCatLab                      | (same)                                                                | n/a  | —                   | not categorical — a summand of a recurrence has no higher-cat structure |
|  8 | Stacks Project               | division polynomials / EDS                                            | n/a  | —                   | Stacks does not develop EDS / division polynomials |
|  9 | MathOverflow / MSE           | "complement elliptic divisibility sequence" generality               | partial | `W(k)∣W(2k)` is classical | the named auxiliary summand is a Lean-formalisation artifact; no MO/MSE standalone treatment |
| 10 | recent arXiv (≤5y)           | "elliptic sequences commutative rings" + "division polynomial"        | yes  | arXiv 2604.05280; arXiv 2102.07573 | the commutative-ring treatment whose Lean image is mathlib's EDS file + the in-progress `ω` PR |

### Literature summary (Phase 3)

Concept identified as: the **subtrahend (one summand) of the 2-complement sequence** of a
normalised EDS, i.e. `preNormEDS(m-2)·preNormEDS(m+1)²` times a parity factor. The
*2-complement* `Wᶜ₂` itself is the standard object (witness of `W(k) ∣ W(2k)`); mathlib's
`complEDS₂` formalises it. `compl₂EDSAux` is a **formalisation-internal piece** of that
complement, factored out only to express the `ω` division polynomials.

Sources agree on the standard form: yes for the *complement* `Wᶜ₂`. **No source names the
individual summand** — it has no classical name; it is Lean bookkeeping.

Most general standard form: the complement `complEDS₂` over an arbitrary `CommRing` (mathlib
already has it), generalised by `complEDS` to the full `n`-complement. The *value at `-2`* is
below the granularity any mathematics source states — a `decide`/`simp` boundary fact.

Disagreement with the literature: none. The lemma is true and trivial; the literature
operates above this granularity.

---

## Generality analysis (Phase 4)

Literature-standard form: the complement `complEDS₂`/`complEDS` over a `CommRing` — already in
mathlib at full generality. `compl₂EDSAux` is a project-only summand of it; its `-2`
evaluation is already maximally general in `R`.

### 4a. Generality status table

| # | Parameter / hypothesis | Current Lean form | Literature-standard | Weaker form exists? | Reason |
|---|------------------------|-------------------|---------------------|---------------------|--------|
| 1 | `[CommRing R]`         | commutative ring  | `CommRing` (mathlib EDS baseline) | NO | mathlib's whole EDS file is over `CommRing`; the formula uses subtraction + `preNormEDS_neg`, so negation is needed — no semiring floor. |
| 2 | `(b c d : R)`          | free parameters   | free parameters     | NO | the defining data of a normalised EDS; nothing to weaken. |
| 3 | index `-2`             | literal `-2 : ℤ`  | n/a (a point value) | NO | a boundary-value lemma; the "generalisation" over all indices is the def + its recurrence, which the project already has (`compl₂EDSAux_mul_b`, `compl₂EDSAux_neg`). |

### 4b. Generality verdict

The current form is: **MAXIMALLY GENERAL** (already over `CommRing`; value lands in `R` with
no extra hypotheses).
Number of weakening opportunities found: 0.
Cost of restatement: n/a.

### 4c. Modern-idiom check (Bourbaki 2.0)

| # | Question | Applies? | Reformulation | Downstream |
|---|----------|----------|---------------|-----------|
| 1 | typeclass-ify a "let X be a foo" preamble? | no | — | no preamble; just `CommRing` + three ring elements |
| 2 | sequences/metric → filters/topology? | no | — | a finite algebraic identity; no limit content |
| 3 | construction → universal property? | no | — | a literal evaluation; nothing to characterise |
| 4 | set+closure → bundled substructure? | no | — | not a substructure |
| 5 | field-specific → weaken typeclass? | no | — | already `CommRing` |
| 6 | 1-categorical → higher-categorical? | no | — | not categorical |
| 7 | concrete index ℤ → general monoid? | no | — | the index `-2` is the *point*; generalising it gives the def, which exists |

Modern idiom available: **no**. The contemporary mathlib form of the *parent* concept
(`complEDS₂`/`complEDS` over `CommRing`) already exists; this lemma is strictly below it, with
nothing to modernise.

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equality or typeclass-search path introduced).

---

## Mathlib search-status: `compl₂EDSAux_neg_two` (Phase 5)

Searched the repo-pinned mathlib at `.lake/packages/mathlib/Mathlib/`.

```
[A] Lean-Finder       n/a (offline)              — used pinned-source grep (D/E) as ground truth
[B] Loogle            n/a (index offline)        — reasoned via D/E
[C] LeanSearch        n/a (offline)              — reasoned via D/E
[D] Grep mathlib src  "compl₂EDSAux", "EDSAux", "complEDS₂", "redInvar", "ω/ωₙ"
        → `compl₂EDSAux` : ZERO hits anywhere in mathlib (grep -rl → no files)
        → `complEDS₂`    : HIT — def at NumberTheory/EllipticDivisibilitySequence.lean:246
           with value lemmas complEDS₂_{zero,one,two,three,four,neg} (251–274),
           plus normEDS_mul_complEDS₂ (321), normEDS_dvd_normEDS_two_mul (326),
           complEDS₂_mul_b (329).
        → `complEDS' / complEDS` : HIT — the full n-complement (392, 427), recovering
           complEDS₂ at n = 2 (complEDS_even, 448). Mathlib subsumes the whole 2-complement track.
        → `redInvar`, `EDSAux` : ZERO hits.
        → `ωₙ` in AlgebraicGeometry/.../DivisionPolynomial/Basic.lean : present ONLY as TODO
           (lines 71, 83: "TODO: the bivariate polynomials `ωₙ`").
[E] Name pattern      project-internal: compl₂EDSAux used in DivisionPolynomialOmega.lean (×2)
           and ZSMul.lean (×1); the lemma compl₂EDSAux_neg_two: 0 explicit callers (@[simp]).
```

Searched for **both** forms:
- the **user's exact def** `compl₂EDSAux` (the summand) — **not in mathlib at all** (0 hits).
- the **parent** `compl₂EDS` (the full complement) — mathlib **HAS** it as `complEDS₂`,
  **byte-identical** body: mathlib line 248 is
  `(preNormEDS(b⁴)c d(k-1)² · preNormEDS(b⁴)c d(k+2) − preNormEDS(b⁴)c d(k-2) · preNormEDS(b⁴)c d(k+1)²) · if Even k then 1 else b`,
  matching project line 1031–1033 modulo the rename `compl₂EDS` ↔ `complEDS₂`. The project's
  `compl₂EDS_{zero,one,two}` (= 2/b/d) match mathlib's `complEDS₂_{zero,one,two}` exactly.

**Concluded:** *found in mathlib* — the entire 2-complement track is present as `complEDS₂`
(identical) and generalised by `complEDS`. Crucially, **mathlib's `complEDS₂` body literally
contains `compl₂EDSAux`'s expression as its subtrahend** (line 248); mathlib simply never
*names* that subtrahend. So mathlib owns the functionality; `compl₂EDSAux` is the redundant
split-out half of a thing mathlib keeps whole. Mathlib has no separate value lemma for the
*summand* at `-2` (it doesn't name the summand), but that is precisely because the summand is
not a mathlib object — the right comparison is at the track level, where mathlib has it.

---

## Composition check (Phase 6)

### 6.0. Call sites — `compl₂EDSAux_neg_two`

Internal use of the **lemma** (outside its declaring file): **0 explicit**. It is `@[simp]`,
so it fires implicitly inside the `simp` calls of the ω/zsmul proofs.
External-to-file callers: 0 explicit.

For context, the **parent def** `compl₂EDSAux` (not this lemma) is used at:

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| DivisionPolynomialOmega.lean:78  | `- compl₂EDSAux W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n + negPolynomial W * W.ψ n ^ 3` |
| DivisionPolynomialOmega.lean:112 | `simp_rw [ω, …, map_compl₂EDSAux, …]` |
| ZSMul.lean:279                   | `rw [smulY, ω, redInvarDenom_two, one_mul, compl₂EDSAux_two, sub_zero, …]` |

Inline-derivation grep (was the `-2` value re-derived elsewhere without the lemma?): (none) —
the `-2` case is only needed via `simp`'s simp-set, consistent with a `@[simp]` normal-form
lemma in the family `compl₂EDSAux_{zero,one,neg_one,two,neg_two}`.

### 6a. Composition attempt

Could `compl₂EDSAux b c d (-2) = -d` be obtained in ≤3 mathlib calls? The obstruction: the
statement **mentions a symbol mathlib does not have** (`compl₂EDSAux`). Any derivation must
first introduce/unfold the project def — not a mathlib primitive. Granting the def, the proof
is literally `by simp [compl₂EDSAux]` (unfold + the `preNormEDS` evaluation/neg simp lemmas,
all of which mathlib has). So this is **not** the clean "≤3 mathlib-primitive calls give the
stated result" shape — the stated result is about a non-mathlib symbol. The stronger and more
accurate characterisation is the track-level one: mathlib already owns this functionality via
`complEDS₂`/`complEDS`, and the correct action is to refactor onto that API, after which this
lemma's role is served (as a `simp` corollary of `complEDS₂`'s definition).

Conclusion: **NOT-COMPOSABLE** as "inline a mathlib composition at the call site" — because the
statement is about a project symbol that should not exist independently of mathlib's
`complEDS₂`. This is a `NO-mathlib-has-it` situation, not a `NO-composable` one: mathlib supplies
the equivalent functionality under a different (and more general) name.

---

## Verdict: `compl₂EDSAux_neg_two`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): the *complement* `Wᶜ₂` is standard (= mathlib `complEDS₂`); the
  individual **summand** `compl₂EDSAux` has no classical name — a Lean artifact. Confirmed vs.
  Wikipedia, Stange, and the Angdinata commutative-ring paper (arXiv 2604.05280).
- Generality analysis (Phase 4): MAXIMALLY GENERAL; no modern-idiom move (4c all "no").
- Mathlib search (Phase 5): **found in mathlib** — `complEDS₂`
  (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:246`) is byte-identical to the
  project's `compl₂EDS`, and **its body (line 248) literally contains `compl₂EDSAux`'s
  expression as the subtrahend**; generalised by `complEDS` (line 427). `compl₂EDSAux` itself:
  0 hits.
- Composition check (Phase 6): NOT-COMPOSABLE as a call-site inline (the statement names a
  non-mathlib symbol); mathlib owns the functionality under `complEDS₂`/`complEDS`.

**Rationale.**
This is the textbook fork-duplication case flagged in the project context. Mathlib already
provides the 2-complement of a normalised EDS as `complEDS₂` — **definitionally identical** to
the project's `compl₂EDS` (same `preNormEDS`-difference body, line-for-line) — with the matching
boundary lemma `complEDS₂_two : complEDS₂ b c d 2 = d`, the divisibility witnesses
`normEDS_mul_complEDS₂` / `normEDS_dvd_normEDS_two_mul`, and the strictly more general
`n`-complement `complEDS`. The project file simultaneously carries both the upstream-style names
and this parallel `compl₂EDS`/`compl₂EDSAux` track; they are the same mathematics under two
naming schemes.

The target `compl₂EDSAux_neg_two` is a `@[simp]` boundary value (`= -d`) of `compl₂EDSAux`, the
**subtracted half** of that complement. Mathlib deliberately keeps the complement whole — its
`complEDS₂` body *contains* this very subtrahend (line 248) but never names it — because the only
reason to split it off is the project's `ω` (omega) division-polynomial construction, which
mathlib carries solely as a standing **TODO** (`DivisionPolynomial/Basic.lean:71,83`). So
`compl₂EDSAux` is a redundant decomposition device that mathlib has consciously not introduced;
its boundary-value lemmas (`_zero/_one/_neg_one/_two/_neg_two`) are bookkeeping `@[simp]` facts,
not independent results. There is nothing here to upstream: the functionality is already mathlib's
under `complEDS₂`/`complEDS`.

This is **not** `NO-composable-from-mathlib`: that bucket presumes mathlib's primitives compose to
the *exact stated result* at a call site, but here the statement is *about a symbol mathlib does
not have*, and mathlib instead supplies the equivalent (more general) functionality under a
different name — which is the `NO-mathlib-has-it` case. It is also not a YES bucket: Phase 4b is
MAXIMALLY GENERAL with no modern-idiom move, and the parent functionality already lives in mathlib.

**WHY not (refactor-actionable):**
Mathlib already has it. The whole `compl₂EDS` track is a rename-duplicate of mathlib's
`complEDS₂` track, and `compl₂EDSAux` is the un-named subtrahend inside mathlib's `complEDS₂`
body. The consolidation fix is to drop the `compl₂*` track and refactor the `ω`/division-polynomial
development onto mathlib's `complEDS₂` / `complEDS` API; once that is done, this lemma is either
unnecessary or becomes a one-line `simp` corollary of `complEDS₂`.

Existing mathlib decl (parent):  `complEDS₂`
Located at:                      `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:246`
  (its subtrahend, line 248, is exactly `compl₂EDSAux`'s body)
More general mathlib decl:       `complEDS` — same file, line 427 (recovers `complEDS₂` at `n = 2`)
Matching boundary lemma:         `complEDS₂_two : complEDS₂ b c d 2 = d` — line 259
  (mathlib counterpart of this lemma's sibling `compl₂EDS_two`; the `compl₂EDSAux`-summand
   value at `-2` falls out as a `simp` step once the development is on `complEDS₂`).

Our form follows in ≤1 line, *at the track level* — the project's `compl₂EDS` IS mathlib's
`complEDS₂`:
```lean
example (b c d : R) (m : ℤ) : compl₂EDS b c d m = complEDS₂ b c d m := rfl  -- identical bodies
```
and the project's `compl₂EDSAux` boundary lemmas (this one included) are then `@[simp]`
corollaries of unfolding against mathlib's `preNormEDS` evaluation lemmas.

Call sites in our project (from Phase 6.0): the **lemma** has 0 explicit callers (`@[simp]`);
the *def* `compl₂EDSAux` is consumed at `DivisionPolynomialOmega.lean:78,112` and `ZSMul.lean:279`,
plus internally by `compl₂EDSAux_mul_b`, `compl₂EDSAux_neg`, `redInvarNum`, `map_compl₂EDSAux`.

Refactor plan (for the consolidation, NOT an upstream PR):
1. Replace the project's `compl₂EDS` track with mathlib's `complEDS₂` (they are `rfl`-equal):
   delete `compl₂EDS` and its lemmas, redirect callers to `complEDS₂` and `complEDS₂_{…}`.
2. For `compl₂EDSAux`: it has no mathlib counterpart by design. Either (a) keep it strictly as
   project-internal glue for the `ω` work (its only purpose), renamed to live beside `complEDS₂`
   conventions; or (b) when the `ω` division polynomials are themselves upstreamed (discharging
   mathlib's `ωₙ` TODO), audit the whole `compl₂EDSAux_{zero,one,neg_one,two,neg_two}` family
   **as a unit** with the def at that time.
3. This specific lemma `compl₂EDSAux_neg_two` is **never an independent PR target**; it is carried
   by whatever happens to `compl₂EDSAux`.

Next action: delete the `compl₂EDS` track in favour of mathlib's `complEDS₂` / `complEDS`; keep
`compl₂EDSAux` (and this `@[simp]` value lemma) only as internal support for the `ω` development,
or fold the family into a future `ωₙ`-upstreaming effort. Do not open a PR for this lemma alone.

---

## Next step

No standalone upstreaming. `NO-mathlib-has-it`: mathlib already owns the 2-complement as
`complEDS₂` (definitionally identical to the project's `compl₂EDS`, with its subtrahend matching
`compl₂EDSAux`'s body) and generalises it via `complEDS`. Refactor the NagellLutz
`ω`/division-polynomial development onto mathlib's `complEDS₂`/`complEDS` API; this `@[simp]`
boundary lemma then either disappears or survives only as project-internal glue for the `ω` work
(mathlib's `ωₙ` TODO).
