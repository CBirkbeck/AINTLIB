# /mathlibable report — `compl₂EDSAux_two`

> Step-9 single-declaration mathlibable assessment (NagellLutz / Nagell–Lutz theorem; elliptic
> curves; division polynomials; elliptic divisibility sequences). Read-only on `.lean`. Local
> build is stale; reasoning is from the source statement + the pinned mathlib source +
> literature/index search. Re-run 2026-06-21.

---

## Baseline (Phase 0)

- lake build:               ⚠ not run (project build stale per task brief; reasoned from source)
- decl `compl₂EDSAux_two`:  ✓ resolved at
  `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1022`
- **qualified name:**       `compl₂EDSAux_two` (ROOT namespace — verified below)
- kind:                     `lemma` (carries `@[simp]`)
- has sorry:                no
- module:                   a fork/extension of `Mathlib.NumberTheory.EllipticDivisibilitySequence`
  (same copyright header: David Kurniadi Angdinata, 2024).

**Namespace verification.** The decl at line 1022 sits in `section Complement` (opens line 1010)
⊂ `section NormEDS` (line 881). The nearest `namespace EllSequence` was *closed* at line 597
(`end EllSequence`); the next `namespace EllSequence` only opens at line 1079 — **after** line 1022.
No `namespace` wraps line 1022. Hence the fully-qualified name is the bare **`compl₂EDSAux_two`**.

---

## Statement (Phase 1)

```lean
@[simp] lemma compl₂EDSAux_two : compl₂EDSAux b c d 2 = 0 := by simp [compl₂EDSAux]
```

with parent definition (line 1016):

```lean
/-- An auxiliary expression that appears in the definition of the numerator of
the reduced invariant and in the definition of the `ω` family of division polynomials. -/
def compl₂EDSAux : R :=
  preNormEDS (b ^ 4) c d (m - 2) * preNormEDS (b ^ 4) c d (m + 1) ^ 2 * if Even m then 1 else b
```

Variables / typeclasses (Lean side): `{R : Type u} [CommRing R]`, `(b c d : R)`, index `(m : ℤ)`
(here specialised to the literal `2`). Hypotheses: none.

`compl₂EDSAux_two` is a **special-value (evaluation) `@[simp]` lemma**: the auxiliary quantity
`compl₂EDSAux b c d m`, evaluated at `m = 2`, is `0`. With `p := preNormEDS (b^4) c d`, the value is
`p (2-2) · p (2+1)² · 1 = p 0 · p 3² · 1 = 0 · c² · 1 = 0`, because `p 0 = 0` (`preNormEDS_zero`).
It is one of a family of five such `@[simp]` evaluation lemmas: `_zero = -1`, `_one = -b`,
`_neg_one = 0`, `_two = 0`, `_neg_two = -d`.

**What `compl₂EDSAux` actually is.** It is *one summand* of the "2-complement"
`compl₂EDS b c d m · b = W(m-1)²·W(m+2) − W(m-2)·W(m+1)²` (line 1063) — specifically the
`W(m-2)·W(m+1)²` term, written in division-free `preNormEDS` form (`compl₂EDSAux b c d m · b =
normEDS(m-2)·normEDS(m+1)²`, line 1026). It exists so the project can define the `ω` family of
division polynomials (second / `Y`-coordinate) over a general `CommRing` **without division**.

---

## Size classification (Phase 2a)

Verdict: **SMALL** — a one-line `@[simp]` evaluation lemma for a bespoke auxiliary `def`; not a named
theorem, not a `## Main results` entry, not a new structure. (Literature width run EXHAUSTIVE anyway.)

## One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → the def-oriented one-liner gate is **n/a**. The
relevant one-liner question attaches to the *parent* `def compl₂EDSAux` (a one-line `def`), not to
this lemma. Carried into Phase 7: this lemma's fate is governed by its parent def's fate
(verdict-inheritance pattern).

---

## Literature search table — EXHAUSTIVE protocol

| #  | Channel                        | Query                                                                                  | Hit? | Standard form found                                  | Notes |
|----|--------------------------------|----------------------------------------------------------------------------------------|------|------------------------------------------------------|-------|
|  1 | WebSearch (specific form)      | EDS ω division-polynomial numerator `psi_{m-2} psi_{m+1}^2` summand named               | partial | only the *whole* `ω`-numerator surfaces             | no named object for the single summand |
|  2 | WebSearch (general/named form) | `ω_m = ψ_{m+2}ψ_{m-1}² − ψ_{m-2}ψ_{m+1}²` Silverman/Stange/Washington                   | yes  | `ω_m = (ψ_{m+2}ψ_{m-1}² − ψ_{m-2}ψ_{m+1}²)/(4v)`     | the *difference* (both summands) is standard; `compl₂EDSAux` is just the `ψ_{m-2}ψ_{m+1}²` half |
|  3 | WebSearch (aliases)            | "2-complement" / witness `W(m) ∣ W(2m)`, `W·Wᶜ₂ = W(2m)`                                | yes  | the witness `Wᶜ₂`                                    | = mathlib `complEDS₂` / project `compl₂EDS`; NOT the same as the `Aux` summand |
|  4 | ChatGPT MCP                    | is `W(m-2)·W(m+1)²` a standard named EDS object?                                        | n/a  | backend down (env)                                   | mitigated by #1–#3 + Phase-5 source reading, which are conclusive |
|  5 | Local references               | `.mathlib-quality/references/` for "complement"/"omega"                                 | n/a  | no references dir for this project                   | recorded n/a |
|  6 | nLab / nCatLab                 | elliptic divisibility sequence / division polynomial                                   | n/a  | not a categorical concept at this granularity        | — |
|  7 | Stacks Project                 | division polynomial / EDS                                                              | n/a  | Stacks does not cover EDS division polynomials       | out of scope |
|  8 | MathOverflow / MSE             | naming of a single `ω`-numerator summand                                                | n/a  | community names `ψ`, `φ`, `θ`, `ω` — not the summand  | — |
|  9 | arXiv (recent)                 | Stange isogenies (eprint 2025); EDS recurrences (2102.07573); EDLP (eprint 2008/444)    | yes  | confirms `ψ/φ/ω/θ` are the named families            | none names the bare `ψ_{m-2}ψ_{m+1}²` factor |

Sources consulted (this run): Wikipedia "Elliptic divisibility sequence"; MIT 18.783 Lecture 5
(division polynomials); arXiv 0910.5370 (isogenies, computational); eprint 2008/444 (EDS & ECDLP);
arXiv 2102.07573 (EDS recurrence). All give `ω_m = ψ_{m+2}ψ_{m-1}² − ψ_{m-2}ψ_{m+1}²` (over `2`/`4v`);
**none names the individual `ψ_{m-2}ψ_{m+1}²` summand.**

### Literature summary (Phase 3)

Concept identified as: **a single summand of the `ω`-numerator / 2-complement of an EDS**, in
division-free (`preNormEDS`) coordinates. The *named* objects are the division-polynomial families
`ψ_m` (= `normEDS`), `φ_m`, `θ_m`, `ω_m`, and the second-coordinate identity
`ω_m = ψ_{m+2}ψ_{m-1}² − ψ_{m-2}ψ_{m+1}²`. The *whole* difference `ψ_{m-1}²ψ_{m+2} − ψ_{m-2}ψ_{m+1}²`
is the recognised complement (mathlib `complEDS₂`, project `compl₂EDS`). **Gap:** the literature names
the families and the complement, but gives **no independent name** to the single `ψ_{m-2}ψ_{m+1}²`
summand — `compl₂EDSAux` is an implementation device for writing `ω` without the textbook's `/2`,
`/ψ_m` divisions. The `_two = 0` value is an immediate consequence of `ψ_0 = 0`.

---

## Generality analysis (Phase 4)

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]`         | commutative ring  | commutative ring (division-free EDS theory lives here) | NO | `preNormEDS`/`normEDS` are defined over `CommRing`; mathlib's EDS baseline. Cannot go below `CommRing` (needs `−`, `·`, `1`). |
| 2 | `(b c d : R)`          | three ring params | same                     | NO | intrinsic to the EDS construction |
| 3 | index `2 : ℤ`          | the literal `2`   | a specific evaluation point | n/a | this *is* a special-value lemma; specialising to `2` is the point |

**Generality verdict (4b):** **MAXIMALLY GENERAL** for what it is (a `CommRing`-level special-value
lemma of a division-free auxiliary). K = 0 weakening opportunities.

**Modern-idiom check (4c):** none apply — it is a finite algebraic evaluation identity already at
mathlib's standard `CommRing` generality. Nothing to filter-ise, bundle, typeclass-ify, or weaken.

**Diamond / defeq risk (4.5):** n/a — kind is `lemma` (introduces no new definitional equality or
instance-search path). The risk question would attach to the parent `def compl₂EDSAux`, not the lemma.

---

## Mathlib search-status (Phase 5)

```
[A] Lean-Finder      "compl2EDSAux two value", "EDS complement aux eval"      no hits (decl is project-local)
[B] Loogle           (special-value of a preNormEDS product)                  no exact hit; nearest = mathlib complEDS₂_* family
[C] LeanSearch       "two-complement auxiliary of EDS equals 0 at 2"          no hit for the Aux summand
[D] Grep mathlib src grep -rn "EDSAux" .lake/packages/mathlib/Mathlib/        ZERO matches across the ENTIRE tree
[E] Name pattern     grep "compl₂EDSAux" repo-wide                            only NagellLutz (target file + ZSMul.lean consumer + dead Original.lean backup)
```

Searched for **both** forms:

- **user's form** (`compl₂EDSAux ... 2 = 0`) — **not in mathlib**. A grep for any `*EDSAux*` over all
  of `Mathlib/` returns nothing (verified this run).
- **literature-standard / nearest mathlib form** — mathlib DOES have the *sibling* "2-complement"
  track, under DIFFERENT names:
  - `complEDS₂` (def, `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:246`) ≙ project `compl₂EDS`
    — bodies match: `p(k-1)²·p(k+2) − p(k-2)·p(k+1)²) · (if Even k then 1 else b)`;
  - `complEDS₂_two : complEDS₂ b c d 2 = d` (line 259) ≙ project `compl₂EDS_two = d` (line 1041);
  - `normEDS_mul_complEDS₂` (line 321) ≙ project `normEDS_mul_compl₂EDS` (line 1046);
  - `complEDS₂_mul_b`, `normEDS_dvd_normEDS_two_mul`, etc.
  **But `compl₂EDSAux` — the single `ψ_{m-2}ψ_{m+1}²` summand — has no counterpart in mathlib.**
  Mathlib's `complEDS₂` is the *whole* difference, never split into this `Aux` piece. Notably, the
  matching mathlib `@[simp]` value lemma here is `complEDS₂_two = d` — there is **no** mathlib lemma
  asserting any summand `= 0`, because mathlib never names the summand.

**Crucial mathlib gap.** `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`
explicitly lists, as open TODOs (verified this run):
- line 71: `* TODO: the bivariate polynomials ωₙ.`
- line 83: `TODO: implementation notes for the definition of ωₙ.`

So mathlib has **not** yet built the `ω` family. The NagellLutz project's `DivisionPolynomialOmega.lean`
(`protected def ω`) is exactly the development that fills this gap, and `compl₂EDSAux` is the
division-free helper introduced to write that `ω` over a general `CommRing`.

Concluded: **the lemma is not in mathlib; its parent def `compl₂EDSAux` is not in mathlib; mathlib's
nearest object `complEDS₂` is the (whole) complement, not this summand; and the `ω` consumer is an
acknowledged mathlib TODO.**

---

## Call sites (Phase 5b)

Live internal use (excluding the declaring file and the non-imported `...Original.lean` backup): **1**.

| Caller file:line   | Usage pattern (one-line excerpt)                                                       |
|--------------------|----------------------------------------------------------------------------------------|
| `LutzNagell/ZSMul.lean:279` | `rw [smulY, ω, redInvarDenom_two, one_mul, compl₂EDSAux_two, sub_zero, Affine.addY, …]` |

Used to prove the `n = 2` case of the scalar-multiplication `addY` / `smulY` formula (the affine
group-law `Y`-coordinate of `[2]P`). No inline re-derivation elsewhere. (`compl₂EDSAux_two` also
appears at `EllipticDivisibilitySequenceOriginal.lean:972`, but that file is a **dead backup** — not
imported by any `.lean` — so it is not a live call site.)

The parent `def compl₂EDSAux` is used more broadly (`compl₂EDSAux_mul_b`, `compl₂EDSAux_neg`,
`map_compl₂EDSAux`, `redInvarNum`, and the `ω` definition at `DivisionPolynomialOmega.lean`). The
parent def is real, load-bearing API; this `_two` lemma is one `@[simp]` fact about it, consumed once.

**Signal read:** K = 1 live use, no inline re-derivation. By itself K=1 leans "could be inlined", but
the lemma is a `@[simp]` evaluation fact of a genuinely-new auxiliary `def`; its mathlib fate is
governed by the fate of `compl₂EDSAux` (verdict inheritance), not by its own call count.

---

## Composition check (Phase 6)

Can `compl₂EDSAux_two` be derived from mathlib in ≤3 chained calls?

- It is a fact **about a definition (`compl₂EDSAux`) that does not exist in mathlib.** The statement
  does not even typecheck without the project's `compl₂EDSAux`. There is no mathlib decl to compose
  against.
- Within the *project*, the proof is `by simp [compl₂EDSAux]` (unfold + `preNormEDS_zero` + `mul_zero`),
  a trivial 1-step `simp`. But that is composition *from the project's own def*, not from mathlib
  primitives.
- Mathlib decls usable: none (the subject is project-local).

**Result:** NOT-COMPOSABLE from mathlib (mathlib lacks the underlying `def`). It IS a trivial `simp`
once `compl₂EDSAux` exists — i.e. it is glue around a new def.

---

## Verdict: `compl₂EDSAux_two`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature (Phase 3): the `ω`/complement identities are standard, but the single `ψ_{m-2}ψ_{m+1}²`
  summand `compl₂EDSAux` is **not a named object** — it is division-free plumbing for `ω`.
- Generality (Phase 4): MAXIMALLY GENERAL; no modern-idiom move — so `YES-but-generalise-first` is
  not in play.
- Mathlib search (Phase 5): **not in mathlib** (zero `*EDSAux*` anywhere); the sibling `complEDS₂`
  (whole complement) IS in mathlib under a different name, but the `Aux` summand and the `ω` consumer
  are **not** (mathlib `ω` is an explicit TODO at `DivisionPolynomial/Basic.lean:71,83`).
- Composition (Phase 6): NOT-COMPOSABLE from mathlib (the parent `def` is absent); trivial `simp`
  once the def exists.

**Why not the other buckets.**
- `NO-mathlib-has-it` — **wrong as stated**: mathlib has neither this lemma nor the def. Mathlib's
  `complEDS₂` is the *whole* complement (its analogous value lemma is `complEDS₂_two = d`); there is
  no mathlib lemma naming any summand, let alone one `= 0`.
- `NO-composable-from-mathlib` — **misleading**: you cannot inline / compose from mathlib a fact whose
  very subject `compl₂EDSAux` is absent from mathlib; the only "composition" is `simp [compl₂EDSAux]`,
  which presupposes the project's def.
- `YES-add-as-is` — **premature**: it can't be added without its parent def, and that def is a
  deliberately non-standard, division-free *split* of the complement (naming one of two summands).

**Rationale.** This lemma cannot be assessed in isolation: it is a `@[simp]` evaluation fact
(`compl₂EDSAux b c d 2 = 0`) about a **project-introduced auxiliary `def compl₂EDSAux`** with no
mathlib counterpart. Its true status is **inherited from that parent def**, and *that* def is the
genuine judgment call: it is real, load-bearing API (used by `ω`, `redInvarNum`, the map lemmas) that
fills an **acknowledged mathlib gap** (the `ωₙ` TODO) — yet it is also a deliberately non-standard,
division-free *splitting* of the literature's complement, i.e. an implementation-detail name (one of
two summands) rather than a textbook object. Whether mathlib wants this *particular* auxiliary split —
versus building `ω` directly from the existing `complEDS₂` plus its own `ψ/φ` machinery when the `ωₙ`
TODO is finally tackled — is a mathlib-maintainer design choice, not something this skill should decide
unilaterally. Hence BORDERLINE, with the decision deferred to the parent-def design question.

**Numbered questions (≤5):**

1. The real subject is `def compl₂EDSAux` (this `_two` lemma just inherits its fate). When mathlib
   discharges its `ωₙ` TODO (`DivisionPolynomial/Basic.lean:71,83`), do maintainers want `ω` built via
   this **division-free auxiliary split** (`compl₂EDSAux` = the `ψ_{m-2}ψ_{m+1}²` summand), or directly
   from the existing `complEDS₂` + `ψ/φ` API? If the latter, `compl₂EDSAux` (and this lemma) stay
   project-local.
2. If `compl₂EDSAux` *is* upstreamed, should it be **renamed to mathlib convention**
   (`complEDS₂Aux` / `preComplEDS₂…`, matching `complEDS₂`) and shipped *together with* the whole
   `ω`/`redInvar` development as one PR — not as an orphan auxiliary?
3. Is naming a *single summand* of the complement (rather than only the complement `complEDS₂` itself)
   acceptable mathlib style, or should it remain a `private`/local `let` inside the `ω` definition (in
   which case the five `@[simp]` value lemmas, including `_two`, do not surface as public API)?

**Next action (verbatim).** Run `/mathlibable` on the parent `def compl₂EDSAux` first and answer the
three design questions; this lemma's verdict should then inherit from that decision. The natural
upstreaming unit is the whole `ω`/`redInvar`/`compl₂EDSAux` block landing against mathlib's `ωₙ` TODO,
not this `@[simp]` lemma alone. Do not delete the lemma — its sole live consumer `ZSMul.lean:279`
needs it as a `@[simp]` rewrite.
