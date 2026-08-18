# /mathlibable report — `WeierstrassCurve.two_mul_ω`

**Verdict: YES-add-as-is** (ships with the `WeierstrassCurve.ω` definition, which is an explicit mathlib TODO).

---

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task brief); reasoned from source — file is `sorry`-free, decl elaborates in the integrated build.
- decl `WeierstrassCurve.two_mul_ω`: ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomialOmega.lean:89`
- kind:                      `lemma` (theorem)
- has sorry:                 no (`grep` for `sorry`/`admit` in file → none)
- module docstring summary:  "extends the division polynomial development from mathlib with the `ω` family of division polynomials, the complement `ψc`, and the invariant `invar`, needed for the `ZSMul` proof."

Qualified name verified: namespace block is `namespace WeierstrassCurve` (line 35) → **`WeierstrassCurve.two_mul_ω`**.

---

### Statement (Phase 1)

`WeierstrassCurve.two_mul_ω` is a theorem giving the **defining algebraic characterization of the
ω-division polynomial** `ωₙ` of a Weierstrass curve `W` over a commutative ring `R`:

> `2·ωₙ = (ψ₂ₙ / ψₙ) − ψₙ·(a₁·φₙ + a₃·ψₙ²)`

where `ψ₂ₙ / ψₙ` is realised as the **complement polynomial** `ψc n` (the cofactor of `ψ n` inside
`ψ (2n)`, so that `ψ n · ψc n = ψ (2n)`; see `ψc_spec`). Rearranging mathlib's own stated definition
`ωₙ := (ψ₂ₙ/ψₙ − ψₙ(a₁φₙ + a₃ψₙ²))/2` and clearing the `2` gives exactly this identity. It is the
"times-two" companion of `ω_spec` (line 82), which states
`2·ωₙ + a₁·φₙ·ψₙ + a₃·ψₙ³ = ψc n`.

Variables / typeclasses (Lean side):
- `{R : Type*} [CommRing R]` — base ring (fully general; no characteristic or domain hypothesis).
- `(W : WeierstrassCurve R)` — a Weierstrass curve.
- `(n : ℤ)` — the multiplication index (signed integer).

Hypotheses: none beyond the typeclasses.

Conclusion (math): `2ωₙ = ψ₂ₙ/ψₙ − ψₙ(a₁φₙ + a₃ψₙ²)` in `R[X][Y]`.
Conclusion (Lean): `2 * W.ω n = W.ψc n - CC W.a₁ * W.φ n * W.ψ n - CC W.a₃ * W.ψ n ^ 3`.

Proof body: `rw [← ω_spec]; abel` — a one-line rearrangement of `ω_spec`.

---

### Size classification (Phase 2a)

Verdict: **BIG** (by association).
Reason: it is the principal specification lemma of a new named mathematical object, `WeierstrassCurve.ω`
(the ω-division polynomial), which mathlib lists explicitly as a TODO. A spec lemma for a named
concept is treated as BIG.

(Literature width is EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `lemma`, not a `def`/`abbrev`/`structure` → one-liner check **n/a**. (The proof body is one
line, but the 2b heuristic targets one-line *definitions*; a short proof is not a negative signal.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found                                              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | Silverman AEC ωₙ `ψ₂ₙ/ψₙ` formula, mult-by-n, Jacobian coords                                           | yes  | `[n]P = (φₙ/ψₙ², ωₙ/ψₙ³)`; `ωₙ` = Y-numerator                    | Silverman, *Arithmetic of Elliptic Curves*, "The Division Equation" (Ch. III / Exercise 3.7). |
|  2 | WebSearch (general form)         | `2ωₙ = ψ₂ₙ/ψₙ − ψₙ(a₁φₙ + a₃ψₙ²)` general Weierstrass                                                    | yes  | classical short form `4y·ωₙ = ψₙ₋₁²ψₙ₊₂ − ψₙ₋₂ψₙ₊₁²`; general-`aᵢ` form is the same object | arXiv 1103.4560, 1909.12654 (EDS), 1303.4327 (homogeneous div. polys) — `ωₙ` standard; the `aᵢ` form is the long-Weierstrass generalisation. |
|  3 | WebSearch (aliases)              | "omega division polynomial", second multiplication numerator, elliptic net                              | yes  | `ωₙ` is the canonical name; some authors write `ω_n` or fold into elliptic nets | name is stable across the literature. |
|  4 | ChatGPT MCP                      | (MCP down per task brief — fallback to WebSearch ×3 + mathlib docstring, which states the formula verbatim) | n/a  | mathlib's own `DivisionPolynomial/Basic.lean` docstring states `ωₙ := (ψ₂ₙ/ψₙ − ψₙ(a₁φₙ+a₃ψₙ²))/2` | the authoritative "standard form" is encoded in the mathlib file this project forks. |
|  5 | Local references                 | grep `.mathlib-quality/references/`                                                                     | n/a  | directory absent                                                 | no `references/` dir; `refs/` absent too. |
|  6 | nLab                             | division polynomial / elliptic divisibility sequence                                                    | n/a  | nLab has no dedicated ωₙ page                                     | not a categorical concept; nLab thin here. |
|  7 | nCatLab                          | —                                                                                                       | n/a  | —                                                                | not categorical. |
|  8 | Stacks Project                   | division polynomial                                                                                     | n/a  | Stacks does not treat explicit division polynomials              | computational object, out of Stacks scope. |
|  9 | MathOverflow / MSE               | omega division polynomial general Weierstrass definition                                                | yes  | confirms `[n]P=(φ/ψ², ω/ψ³)` and the `ψ₂ₙ/ψₙ` characterization    | standard exercise-level material. |
| 10 | recent arXiv (≤5 yr)             | division polynomials arbitrary isogenies / EDS recurrence                                               | yes  | 2503.15428, 2102.07573 — `ωₙ` used unchanged                     | no competing modern reformulation. |

### Literature summary (Phase 3)

Concept identified as: the **ω-division polynomial** `ωₙ` of a Weierstrass curve (Silverman AEC; the
second/`Y`-coordinate numerator in `[n]P = (φₙ/ψₙ², ωₙ/ψₙ³)`).
Sources agree on the standard form: **yes**. The classical statement `4y·ωₙ = ψₙ₋₁²ψₙ₊₂ − ψₙ₋₂ψₙ₊₁²`
(short Weierstrass) and the long-Weierstrass form `2ωₙ = ψ₂ₙ/ψₙ − ψₙ(a₁φₙ + a₃ψₙ²)` describe the same
object; the latter is the form mathlib's docstring and this lemma use.
Most general standard form: over an arbitrary commutative ring `R` (the universal-ring construction
makes `ωₙ` an honest element of `R[X][Y]`, with no characteristic/field hypothesis). `two_mul_ω` is
stated at exactly this generality.
Generality dimensions where the literature varies:
  - base ring: short-Weierstrass over a field ↔ **arbitrary `CommRing` via the universal ring** (most general; the project's form).
  - index: `ℕ` ↔ **`ℤ`** (signed; the project's form, the more general).
Disagreement with the literature: none. The lemma is the `R`-and-`ℤ`-general restatement of the
textbook identity.

---

### Generality analysis — `WeierstrassCurve.two_mul_ω`

Literature-standard form (from Phase 3): `2ωₙ = ψ₂ₙ/ψₙ − ψₙ(a₁φₙ + a₃ψₙ²)`, ideally over an arbitrary
base.

| # | Parameter / hypothesis | Current Lean form        | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|--------------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]`         | arbitrary commutative ring | field (textbook) / CommRing (universal) | NO — already maximal | `ω`, `ψc`, `φ`, `ψ` are honest `R[X][Y]` elements over any `CommRing`; no characteristic-≠-2 or domain hypothesis is imposed. This is the maximally general base. |
| 2 | `(n : ℤ)`              | signed integer index     | ℤ (or ℕ in older texts)  | NO — ℤ is already the more general index | identity holds for all `n : ℤ`. |
| 3 | conclusion shape       | `2 * ω = ψc − a₁φψ − a₃ψ³` | `2ωₙ = ψ₂ₙ/ψₙ − …`     | n/a                 | `ψc n` *is* `ψ(2n)/ψ(n)` made polynomial (`ψc_spec`), avoiding ring division — the idiomatic mathlib choice (matches how mathlib's `complEDS₂` already avoids division). |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL**.
Number of weakening opportunities found: 0.
Cost of restatement: n/a (no restatement needed).

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Downstream |
|----|----------|----------|------------------------|------------|
|  1 | bundled-hypotheses → typeclasses? | no | already typeclass-driven (`[CommRing R]`) | — |
|  2 | sequences/metric → filters/topology? | no | purely algebraic identity in `R[X][Y]` | — |
|  3 | construct → universal-property class? | no | `ω` is a concrete polynomial; the universal *ring* is already used internally (`Universal.curve`) exactly to avoid char hypotheses — this is the mathlib idiom, not a thing to re-abstract | — |
|  4 | set+closure → bundled substructure? | no | not a substructure statement | — |
|  5 | field/metric-specific → weaken typeclass? | no | already over `CommRing` | — |
|  6 | 1-categorical → higher-categorical? | no | not categorical | — |
|  7 | concrete index → general monoid? | no | `ωₙ` is intrinsically indexed by `ℤ` (the multiplication-by-n map); generalising the index past `ℤ` is meaningless | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. The statement is already in the contemporary mathlib idiom: arbitrary
`CommRing` base, `ℤ`-indexed, division replaced by the complement polynomial `ψc` (mirroring mathlib's
existing `complEDS₂` "avoid ring division" design). One-line reason: this is a concrete polynomial
identity already at maximal algebraic generality; there is no abstraction move that improves
organisation.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or instances introduced).

*Note for the upstreaming plan:* the **companion `def WeierstrassCurve.ω`** (line 74) WOULD need a
Phase-4.5 pass when it is PR'd — but its risk is LOW (a sealed `noncomputable def` returning a
polynomial; no `@[reducible]`, no instance, no coercion). `two_mul_ω` itself carries no risk.

---

### Mathlib search-status: `WeierstrassCurve.two_mul_ω`

[A] Lean-Finder       "omega division polynomial 2 omega = psi(2n)/psi(n)"     no hits (index unreachable offline; reasoned from source)
[B] Loogle            `2 * WeierstrassCurve.ω _ = _` / `WeierstrassCurve.ω`     no hits — `WeierstrassCurve.ω` is undefined in mathlib
[C] LeanSearch        "characterization of omega division polynomial"          no hits
[D] Grep mathlib src  `WeierstrassCurve.ω`, `two_mul_ω`, `def ψc`, `compl₂EDS`, `redInvarDenom`, `redInvarNum`, `redInvar_normEDS`, `invarDenom`, `compl₂EDSAux` over `.lake/packages/mathlib/Mathlib/` | **no hits in EllipticCurve scope.** `ω`/`two_mul_ω` matches are unrelated (`LucasLehmer.ω`, `LucasLehmer.two_mul_ω_pow`, `OmegaCompletePartialOrder.ωSup`, root systems). |
[E] Name pattern      grep `WeierstrassCurve` + `ω` in `DivisionPolynomial/Basic.lean`, `Degree.lean`, `EllipticDivisibilitySequence.lean` | **no hits** — `ωₙ` appears ONLY in the docstring, twice, as a **TODO**. |

Searched for both:
  - current form `2·W.ω n = W.ψc n − …` — absent.
  - literature-standard `ωₙ := (ψ₂ₙ/ψₙ − …)/2` — absent as a decl; **present only as the prose TODO** in the docstring.

**Decisive mathlib evidence — the TODO is explicit.** In
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`:
  - line 28–30 (Mathematical background): `Furthermore, define the associated sequences φₙ, ωₙ ∈ R[X, Y] by … ωₙ := (ψ₂ₙ / ψₙ − ψₙ ⬝ (a₁φₙ + a₃ψₙ²)) / 2.`
  - line 71 (`## Main definitions`): `* TODO: the bivariate polynomials ωₙ.`
  - line 83 (`## Implementation notes`): `TODO: implementation notes for the definition of ωₙ.`

So `ω` and its specification are a *named, documented gap* in mathlib's own division-polynomial file —
a file this project explicitly forks (`DivisionPolynomial.lean` header: "This is a copy of
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` …").

**Building-block note (re-aim awareness).** Mathlib *already* has the univariate/scalar complement
machinery this lemma's `ψc` is built on: `complEDS₂`, `complEDS'`, `complEDS`, and
`normEDS_mul_complEDS₂` (in `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`, lines 246–420).
The project forked these under the names `compl₂EDS` / `normEDS_mul_compl₂EDS` only to dodge name
clashes while it develops on a frozen mathlib. In a real PR, `ψc n` is the bivariate-polynomial
instance of mathlib's existing `complEDS₂`, and `ψc_spec` (`ψ n · ψc n = ψ (2n)`) is the
`R[X][Y]`-level reflection of mathlib's existing `normEDS_mul_complEDS₂`. The complement *concept* is
in mathlib; the **`ω` def and `two_mul_ω` spec are not.**

Concluded: **not in mathlib** (all methods exhausted, both forms). The `ω` apparatus —
`def WeierstrassCurve.ω`, the complement polynomial `ψc`, and `two_mul_ω` — is net-new and fills the
file's own stated TODO.

---

### Call sites — `WeierstrassCurve.two_mul_ω`

Internal use count (NagellLutz, excluding the declaring file): **1**
External-to-file callers in NagellLutz: **1 file**

| Caller file:line                                   | Usage pattern (one-line excerpt) |
|----------------------------------------------------|----------------------------------|
| `LutzNagell/DivisionPolynomialOmega.lean:120`      | `simp_rw [left_distrib, two_mul_ω, ψc_neg, ψ_neg, φ_neg]; ring` — inside `universal_ω_neg`, the key step proving `ω(-n)` from `ω(n)` (the building block of `ω_neg`). |
| `LutzNagell/ZSMul.lean:127`                         | `have := congr(polyEval cusp 1 1 $(curve.two_mul_ω n))` — used to compute `polyEval_cusp_ω = 1`, feeding the `ZSMul` (scalar-multiplication) proof — the file's reason to exist. |

Cross-project (the project FORKS its own copy; same lemma duplicated in HasseWeil):
- `HasseWeil/Auxiliary/DivisionPolynomial.lean:109` (the lemma itself), `:146` (`ω_neg`-analog use), `:203` (cusp-eval use). Two NT projects independently re-derive this exact lemma — a strong "mathlib should own it" signal.

Inline-derivation grep (re-derived without using `two_mul_ω`?): (none) — every consumer uses the lemma; nobody re-expands `2*ω` by hand.

Call-sites signal: real API. `two_mul_ω` is the *only* bridge from the `ω` definition to its
computational uses (it is how `ω_neg` and every `polyEval … ω` fact are proved). It is load-bearing
in **both** NagellLutz (`ZSMul`) and HasseWeil. Low raw count, but zero inline bypass and
cross-project duplication → YES-bucket signal.

---

### Composition check (Phase 6)

Can `two_mul_ω` be derived from *mathlib* in ≤3 chained calls? **No** — because its very subject,
`WeierstrassCurve.ω`, does not exist in mathlib. There is nothing to compose against: the lemma is the
defining property of an object mathlib has not yet defined.

Attempt 1: `← W.ω_spec` then `abel` — this is the *project's* proof, but `ω_spec` and `ω` are project
decls, not mathlib. Result: fails as a mathlib composition (depends on to-be-upstreamed defs).
Attempt 2: express `ψc`/`ω` via mathlib's `complEDS₂` — gets the complement, but `ω` is still
undefined upstream, so there is no statement to prove. Result: fails.

Conclusion: **NOT-COMPOSABLE** from current mathlib. (It becomes a one-liner *only after* `ω` and
`ω_spec` are themselves upstreamed — i.e. it is part of the same contribution, not a thing mathlib can
already synthesise.)

---

## Verdict: `WeierstrassCurve.two_mul_ω`

**Category:** YES-add-as-is

**Evidence:**
- Literature search (Phase 3): `ωₙ` is the standard ω-division polynomial (Silverman AEC); the
  identity `2ωₙ = ψ₂ₙ/ψₙ − ψₙ(a₁φₙ + a₃ψₙ²)` is its standard long-Weierstrass characterization — and is
  the exact formula mathlib's own docstring writes for the TODO `ωₙ`.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** (arbitrary `CommRing`, `ℤ`-indexed, division-free
  via `ψc`); Phase 4c found no modernisation move.
- Mathlib search (Phase 5): **not in mathlib**; `ωₙ` exists there only as a documented **TODO** (Basic.lean
  lines 71, 83) with the formula spelled out at line 30.
- Composition check (Phase 6): **NOT-COMPOSABLE** (its subject `ω` is itself undefined upstream).

**Rationale.**
This lemma is the principal specification of `WeierstrassCurve.ω`, the ω-division polynomial that
mathlib's `DivisionPolynomial/Basic.lean` *explicitly defers as a TODO in two places* while already
writing its defining formula in the docstring. `two_mul_ω` is precisely that formula, cleared of the
`/2` and made division-free by routing `ψ₂ₙ/ψₙ` through the complement polynomial `ψc` (whose scalar
analogue `complEDS₂` mathlib already ships). It is stated at maximal generality — any commutative ring,
signed index — with no field or characteristic hypothesis, exactly the form mathlib wants. It is not
composable from current mathlib because the object it characterizes does not yet exist upstream; it
*is* the missing piece. That two independent AINTLIB number-theory projects (NagellLutz and HasseWeil)
each re-derive it verbatim, and that it is the sole bridge from the `ω` definition to every downstream
`ω` computation (`ω_neg`, the `ZSMul` multiplication-by-n proof), confirms it is genuine reusable API
rather than a private helper.

The honest scope caveat: `two_mul_ω` cannot land *alone* — it presupposes `def WeierstrassCurve.ω` and
`ω_spec`, which are the actual TODO. It should be PR'd **together with** `ω`, `ω_spec`, `ψc`, and the
`ω_zero`/`ω_one`/`ω_neg`/`map_ω` API in this file. As the spec lemma of that bundle, its own verdict is
unambiguously add-as-is.

**WHY add it (refactor-actionable).**
- *New content / named gap.* `WeierstrassCurve.ω` is listed as a TODO at
  `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:71` ("TODO: the bivariate
  polynomials ωₙ.") and `:83`, with the defining formula already at `:30`. `two_mul_ω` discharges the
  "what equation does ωₙ satisfy" half of that TODO. This is the textbook example of *naming the gap*:
  the gap is a literal `TODO` comment in the target file.
- *Composition with existing API.* Once `ω` + `two_mul_ω` land, mathlib's multiplication-by-`n` map on
  affine points gets its `Y`-coordinate numerator: `[n]P = (φₙ/ψₙ², ωₙ/ψₙ³)`. The lemma plugs `ω`
  directly into the existing `ψ`/`φ` division-polynomial API (`WeierstrassCurve.ψ`,
  `WeierstrassCurve.φ` in the same file) and into the EDS complement API
  (`complEDS₂`, `normEDS_mul_complEDS₂`) that already lives in
  `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`.

Proposed mathlib location:    `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`
                              (the file whose TODO this fills), or a sibling
                              `DivisionPolynomial/Omega.lean` if size warrants a split.
Proposed PR title:            `feat(AlgebraicGeometry/EllipticCurve): add the ω division polynomials`
PR grouping (REQUIRED):       ship `two_mul_ω` **as one PR** with the rest of `DivisionPolynomialOmega.lean`:
                              `WeierstrassCurve.ω` (the def), `ω_spec`, `ψc` (re-expressed via mathlib
                              `complEDS₂`), `ψc_spec`, `ω_zero`, `ω_one`, `ψc_neg`, `ω_neg`, `map_ω`, plus the
                              supporting `compl₂EDS`/`redInvar*` lemmas from
                              `EllipticDivisibilitySequence(.lean)` that have no upstream equivalent. The
                              `invar`/`Ψ₃`/`preΨ₄` helpers (lines 45–67) ride along as needed. Because the
                              project forked the EDS + DivisionPolynomial files wholesale, the PR's real
                              work is *diffing the fork against upstream* and contributing only the `ω`/`ψc`
                              delta on top of mathlib's existing `complEDS`/`ψ`/`φ`.
Pre-PR checklist before opening:
  - [ ] `/generalise WeierstrassCurve.two_mul_ω` — confirm no further weakening (expected: none; already maximal).
  - [ ] `/cleanup DivisionPolynomialOmega.lean` — full audit + diff gates; re-base the fork onto live mathlib so `ψc`/`compl₂EDS` collapse onto upstream `complEDS₂`.
  - [ ] First land the `ω` **def** + `ω_spec` (this lemma's prerequisites); `two_mul_ω` is a 2-line corollary in the same PR.
  - [ ] Pick a reviewer from recent `Mathlib/AlgebraicGeometry/EllipticCurve/` commits (the division-polynomial author, per the file copyright: David Kurniadi Angdinata).

---

## Next step

Run `/generalise WeierstrassCurve.two_mul_ω` (expected: already maximally general), then `/cleanup` the
file to re-base the `ψc`/`compl₂EDS` fork onto mathlib's existing `complEDS₂`. Open a single
`feat(AlgebraicGeometry/EllipticCurve)` PR that adds the whole `ω` family — `ω`, `ω_spec`, `two_mul_ω`,
`ψc`, `ψc_spec`, `ω_zero/one/neg`, `map_ω` — discharging the `ωₙ` TODO at
`DivisionPolynomial/Basic.lean:71,83`. `two_mul_ω` is the spec lemma of that bundle.
