# /mathlibable report — `compl₂EDSAux`

**TL;DR — `BORDERLINE-needs-human`.** `compl₂EDSAux` is genuinely **not** in
mathlib (definitive grep over the pinned tree: zero hits anywhere), and it is a
real, multiply-reused building block of the project's **`WeierstrassCurve.ω`**
family of division polynomials — and `ωₙ` is an **explicit mathlib TODO**
(`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:71,83`).
That pulls toward "ships upstream with the `ω` PR" (the same disposition as the
sibling decls `two_mul_ω` / `map_ω`). **But** two facts pull the other way and
the skill cannot adjudicate between them: (1) `compl₂EDSAux` is a **one-line,
literature-unnamed convenience** — the literature names the *full* ω-bracket
`ψₙ₋₁²ψₙ₊₂ − ψₙ₋₂ψₙ₊₁²` and the EDS complement, **not** the single subtrahend
product `ψₙ₋₂ψₙ₊₁²`; and (2) mathlib **already has the parent complement**
`complEDS₂` (with `complEDS₂_mul_b`), so whether the upstream `ω` keeps this
exact auxiliary or is restructured to go through `complEDS₂` / the
`ψ₂ₙ/ψₙ` route the mathlib docstring itself prescribes is a **formalisation-
design decision for the `ω`-PR author**, not something the evidence forces.
The verdict therefore hinges on a human judgment about how `ω` will be
upstreamed. Questions for the user are in Phase 7.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task note; verdict reasoned from source — it does not depend on elaboration)
- decl `compl₂EDSAux`:      ✓ resolved — `def` head at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1016`, body at 1017 (task cited line 1017)
- qualified name:           **`compl₂EDSAux`** (root namespace — VERIFIED). At the def the only open scope is the file's `@[expose] public section` (line 81, not a namespace) inside `section Complement` (line 1010, unnamed) ⊂ `section NormEDS` (line 881, unnamed); every `namespace EllSequence`/`IsEllSequence` block closes before it (`end EllSequence` at 597, `end IsEllSequence` at 702; the next `namespace EllSequence` only opens at 1079). So there is **no** namespace prefix — the parsed/qualified name is exactly `compl₂EDSAux`.
- kind:                     `def`
- has sorry:                no
- module docstring summary: "Elliptic divisibility sequences" — defines EDS and constructs normalised EDSs from initial terms. This file is an **extended fork** of `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (same author header, David Kurniadi Angdinata): a verbatim copy of the mathlib content **plus** ~1100 extra lines (1667 vs mathlib's 547) adding the `invarNum`/`redInvarNum`/`compl₂EDS`/`compl₂EDSAux` + `ω`-division-polynomial layer.

---

### Statement (Phase 1)

`compl₂EDSAux b c d : ℤ → R` is the auxiliary algebraic expression

  `compl₂EDSAux b c d m = P(m−2) · P(m+1)² · (if Even m then 1 else b)`,   where `P = preNormEDS (b⁴) c d`.

Equivalently `compl₂EDSAux b c d m · b = W(m−2) · W(m+1)²` where `W = normEDS b c d`
(this is the project lemma `compl₂EDSAux_mul_b`, line 1026). So it is the
**`b`-reduced single product term** `W(m−2)·W(m+1)²`.

Its mathematical role — it is **one of the two product terms** of the standard
EDS 2-complement / duplication bracket. The 2-complement `Cᶜ₂ = compl₂EDS`
(witness of `W(m) ∣ W(2m)`) satisfies (project `compl₂EDS_mul_b`, line 1063;
mathlib `complEDS₂_mul_b`, line 329):

  `compl₂EDS b c d m · b = W(m−1)²·W(m+2) − W(m−2)·W(m+1)²`,

so `compl₂EDSAux·b` is the **subtrahend half** of that bracket. It then serves two
consumers (exactly as its docstring states — "appears in the definition of the
numerator of the reduced invariant and in the definition of the `ω` family of
division polynomials"):
  (i) `redInvarNum b c d m = compl₂EDS m + W(m)³·b + 2·compl₂EDSAux m`
      (EllipticDivisibilitySequence.lean:1359), the numerator of the reduced
      EDS invariant `invarNum/W₂`; and
  (ii) `WeierstrassCurve.ω n = redInvarDenom … n · (…) − compl₂EDSAux ψ₂ (C Ψ₃) (C preΨ₄) n + negPolynomial · ψ n³`
      (DivisionPolynomialOmega.lean:74) — the **division-free** closed form of the
      ωₙ division polynomial, satisfying `2·ω n + a₁·φ·ψ + a₃·ψ³ = ψc n`
      (`ω_spec`, line 82), i.e. the classical `ωₙ = (ψ₂ₙ/ψₙ − ψₙ(a₁φₙ + a₃ψₙ²))/2`.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — coefficient ring.
- `(b c d : R)` — the four initial data of the normalised EDS (`W(2)=b, W(3)=c, W(4)=d·b`).
- `(m : ℤ)` — the index.

Hypotheses: none (it is a plain `def`).

Conclusion (math): n/a — definition.
Conclusion (Lean): `compl₂EDSAux b c d m : R`.

---

### Size classification (Phase 2a)

Verdict: **SMALL** (with a BIG association).
Reason: it is a helper `def` — not a named mathematical structure, not a "Main
result", not named after a person. *However* it is a constituent of a BIG object
(`WeierstrassCurve.ω`, the explicitly-TODO'd ω-division-polynomial family), so
its fate is coupled to that BIG decl. (Literature width is EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: **1 substantive line**
(`preNormEDS (b^4) c d (m - 2) * preNormEDS (b^4) c d (m + 1) ^ 2 * if Even m then 1 else b`).
One-liner verdict: **ONE-LINER**.

Exemption check:
| Exemption                         | Applies? | Evidence                                                                                                     |
|-----------------------------------|----------|--------------------------------------------------------------------------------------------------------------|
| Avoid defeq abuse                | no       | No downstream proof relies on a *sealed* RHS; on the contrary, `compl₂EDSAux_mul_b`, `compl₂EDSAux_neg`, `compl₂EDS_eq_redInvarNum_sub` all freely `simp_rw [compl₂EDSAux, …]` to unfold it. No barrier role. |
| Avoid typeclass diamonds         | no       | No instances involved; plain ring expression over a fixed `[CommRing R]`. |
| Mark semantic intent / API name  | **yes**  | It has a name + docstring and is the **shared subterm** of `redInvarNum` (line 1359) and `WeierstrassCurve.ω` (DivisionPolynomialOmega.lean:74); its `@[simp]` value lemmas (`compl₂EDSAux_zero/one/neg_one/two/neg_two`) and `map_compl₂EDSAux` form a small API used by `ω_zero/ω_one` and `map_ω`. The stable name lets `ω`'s definition and naturality proof name the term once. |

Conclusion: **ONE-LINER WITH-EXEMPTION** (the "semantic intent / shared-API-name" exemption applies — but note it is the *weakest* of the three, and the term it names is not a literature object).

---

## PHASE 3 — Literature search (EXHAUSTIVE)

### Literature search table

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found                                   | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|--------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | EDS omega division polynomial duplication W(m-2)·W(m+1)² complement                                     | partial | the **bracket** `ω_n = (ψ_{n+2}ψ_{n-1}² − ψ_{n-2}ψ_{n+1}²)/(4v)` | Wikipedia "Division polynomials"; arXiv 2102.07573, 1909.12654. The bracket is named (`ω_n`); the single term `ψ_{n-2}ψ_{n+1}²` is **not**. |
|  2 | WebSearch (general / def form)   | division polynomial ω_n definition ψ_{2n}/ψ_n doubling formula                                          | yes  | `ψ_{2n} = ψ_n(ψ_{n+2}ψ_{n-1}² − ψ_{n-2}ψ_{n+1}²)/2y`; `ω_n=(ψ_{n-1}²ψ_{n+2} − ψ_{n-2}ψ_{n+1}²)/4y` | Wikipedia confirms: the *full bracket* (= `complEDS₂·b` up to `4y`/parity) is the named object; the subtrahend alone is incidental. |
|  3 | WebSearch (named-after / aliases)| Stange elliptic nets / Ward EDS auxiliary intermediate-term naming                                      | no   | named objects = ψ, φ, **ω**, net polynomials, the *complement*; no name for `ψ_{n-2}ψ_{n+1}²` | Stange "Elliptic nets and elliptic curves" (arXiv 0710.1316), eprint 2025/521. Intermediate single products are never separately named. |
|  4 | ChatGPT MCP                      | "Is `P(m-2)·P(m+1)²·(parity-b)` a named object in EDS/division-polynomial literature, or an implementation sub-expression?" | n/a  | —                                                      | **MCP down** (Codex exec error, as the task warned). Compensated by extra WebSearch rows #1–#3 + #5–#10 and by reading the mathlib docstring's own ω formula. |
|  5 | Local references                 | grep `.mathlib-quality/references/`                                                                     | n/a  | directory absent for NagellLutz                        | `projects/NagellLutz/.mathlib-quality/` has only `overview/`; no `references/`. Recorded n/a. |
|  6 | nLab                             | "division polynomial" / "elliptic divisibility sequence"                                                | no   | nLab has no dedicated division-polynomial entry isolating this term | not a categorical concept; the EDS/division-polynomial atom there is ψ_n / the recurrence. |
|  7 | nCatLab (categorical)            | —                                                                                                      | n/a  | not a categorical concept                              | ω is a concrete polynomial coordinate, no universal-property phrasing. |
|  8 | Stacks Project (alg geom)        | division polynomial / Weierstrass ω                                                                     | n/a  | Stacks does not develop explicit division polynomials  | recorded n/a — out of Stacks' scope. |
|  9 | MathOverflow / MathSE            | division polynomial ω_n formula ψ_{n-2}ψ_{n+1}² intermediate                                            | no   | answers cite the *full* `ω_n` bracket; no name for the half-term | consistent with #1–#3. |
| 10 | recent arXiv (≤5 yr)             | EDS recurrence / elliptic sequences over commutative rings                                              | partial | arXiv 2102.07573, 2604.05280 use the full recurrence/bracket | the b-reduced `preNormEDS` machinery is essentially Angdinata's mathlib formalisation; no paper names this sub-term. |

### Literature summary (Phase 3)

Concept identified as: the **subtrahend product term** `ψ_{n-2}·ψ_{n+1}²` (b-reduced) of the EDS 2-complement / ω-division-polynomial bracket.
Sources agree on the standard form: **yes, on what the NAMED objects are** — ψ_n, φ_n, **ω_n**, the *full* bracket `ψ_{n-1}²ψ_{n+2} − ψ_{n-2}ψ_{n+1}²`, and the EDS complement `W(2m)/W(m)`. They **uniformly do NOT name** the single product `ψ_{n-2}ψ_{n+1}²`.
Most general standard form: the named atom is `ω_n` (and the complement); `compl₂EDSAux` is a strict sub-expression of `complEDS₂·b` (= the bracket).
Generality dimensions where the literature varies:
  - base field vs commutative ring: classical sources use a field with `2y` denominators; mathlib/Angdinata use a general `[CommRing R]` with the `b`-reduced division-free `preNormEDS` (this is the *modern* form — see Phase 4c). `compl₂EDSAux` is already in the modern, general, division-free form.
Disagreement with the literature: **the very existence of a name for this term is non-standard.** Literature inlines it inside the ω/complement bracket.

---

## PHASE 4 — Generality analysis

Literature-standard form (from Phase 3): the named object is `ω_n` / the full
complement bracket; `compl₂EDSAux` is an *unnamed* sub-term. There is no
"literature-standard form of `compl₂EDSAux`" to weaken toward — only the
question of whether to name it at all.

### Generality analysis — `compl₂EDSAux`

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|---------------------------|---------------------|--------|
| 1 | `[CommRing R]`         | commutative ring  | classical: field with `2y`; modern: commutative ring | NO | already maximally general — `preNormEDS` is defined over any `CommRing`; this *is* the Bourbaki-2.0 form (division-free, ring-general). |
| 2 | `(b c d : R)`          | free EDS initial data | EDS initial data | NO | the natural parameters of `normEDS`; cannot be weakened. |
| 3 | `(m : ℤ)`              | integer index     | integer index             | NO | ℤ-indexing is the correct EDS index set (already general; `preNormEDS` handles negatives). |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (as a ring-level, division-free expression — it is exactly the modern mathlib idiom already; nothing to weaken).
Number of weakening opportunities found: **0**.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Downstream |
|----|----------|----------|------------------------|------------|
|  1 | bundled hyps → typeclasses? | no | — | already a bare ring expression. |
|  2 | sequences → filters? | no | — | no limiting/topology; purely algebraic. |
|  3 | construction → universal property? | no | — | it is a polynomial value, not a UP-characterisable object. |
|  4 | set+closure → bundled substructure? | no | — | n/a. |
|  5 | field/metric-specific → weaken typeclass? | **already done** | — | the `preNormEDS` `b⁴`-reduction is *precisely* the modern division-free, `CommRing`-general reformulation of the classical `/2y` division polynomials. The decl is already on the modern side. |
|  6 | 1-categorical → higher-categorical? | no | — | n/a. |
|  7 | concrete index → general additive structure? | no | ℤ is the right index for EDS. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (the decl is *already* the modern form — division-free, ring-general; the modernisation here is `complEDS₂`/`preNormEDS` itself, which mathlib already adopted).
One-line reason: there is no cleaner contemporary phrasing of a single ring monomial; the only design question is **whether to name it**, which is Phase 6/7 territory, not a generalisation.

---

## PHASE 4.5 — Diamond / defeq risk (`def`)

### Diamond / defeq risk — `compl₂EDSAux`

| # | Risk | Verdict | Evidence |
|---|------|---------|----------|
| 1 | Typeclass diamond | none | no instances declared/derived; just an `R`-valued expression. |
| 2 | Reducibility leak | none | not `@[reducible]`; semireducible `def`. Downstream proofs unfold it *explicitly* via `simp_rw [compl₂EDSAux, …]`, never relying on automatic defeq. |
| 3 | Non-canonical unfolding | low | `simp` will not unfold it unless `compl₂EDSAux` is named in the simp set; its `@[simp]` *value* lemmas (`compl₂EDSAux_zero` etc.) fire only at literal indices 0, ±1, ±2 — controlled. |
| 4 | Instance priority collision | none | not an instance. |
| 5 | Universe-polymorphism | none | lives in `R : Type u`; no forced annotation. |
| 6 | Coercion ambiguity | none | no `CoeFun`/`CoeSort`. |

### Risk verdict (Phase 4.5)

Overall risk: **NONE**.
Top risks: none. (Risk does not gate this verdict.)

---

## PHASE 5 — Mathlib search

### Mathlib search-status: `compl₂EDSAux`

[A] Lean-Finder       (no dedicated MCP in this env)          n/a — covered by [D] grep over the pinned tree + [C] web docs search
[B] Loogle            type-pattern `preNormEDS _ _ _ (_ - 2) * preNormEDS _ _ _ (_ + 1) ^ 2 * _` (no MCP; grepped the source as proxy)   no hits — the pattern occurs **only inside `complEDS₂`'s body** (line 248), never as a standalone named decl
[C] LeanSearch        web search over `leanprover-community.github.io` mathlib4 docs: "EllipticDivisibilitySequence complEDS₂ … ωₙ TODO"   confirms mathlib has `preNormEDS`/`complEDS₂`/`ψ`/`φ`; **`ωₙ` is TODO**; no `compl₂EDSAux`
[D] Grep mathlib src  `compl₂EDSAux` / `complEDSAux` / `EDSAux` / `def ω|Ω|omega` over `.lake/packages/mathlib/Mathlib/`   **no hits** for `compl₂EDSAux` anywhere; the only `ω`/`Ω`/`omega` defs are unrelated (`LucasLehmer.ω`, `Hyperreal.omega`, Topos `Ω`, Triangulated `ω₁/ω₂`, RootSystem `ω`, ZFC `omega`)
[E] Name pattern      `def .*EDSAux`, `ωEDS`, `omegaEDS` in `Mathlib/AlgebraicGeometry/` + `Mathlib/NumberTheory/`   no hits

Searched for both:
  - the user's current form (`compl₂EDSAux`, `ψ_{n-2}ψ_{n+1}²`-shape) → not in mathlib;
  - the literature-standard atom (the *full* ω-bracket / complement) → **mathlib HAS the complement** as `complEDS₂` (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:246`, with `complEDS₂_mul_b` at line 329), and `ωₙ` is a **named TODO** (DivisionPolynomial/Basic.lean:71,83).

Concluded: **not in mathlib** (all methods exhausted) for `compl₂EDSAux` itself; **but** its parent bracket `complEDS₂` and the value relation `complEDS₂_mul_b` ARE in mathlib, and the ω-object it feeds is an explicit mathlib TODO. So `compl₂EDSAux` is a genuinely-new *sub-expression* whose parent and target are already-/about-to-be upstream.

---

## PHASE 6 — Composition check (+ call-sites)

### Call sites — `compl₂EDSAux`

Internal use count (excluding the declaring file): **3 `.lean` sites in 2 files**, plus a substantial **same-file** API.

| Caller file:line | Usage pattern |
|------------------|---------------|
| `LutzNagell/DivisionPolynomialOmega.lean:78` | inside `WeierstrassCurve.ω`'s definition: `… − compl₂EDSAux W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n + …` |
| `LutzNagell/DivisionPolynomialOmega.lean:112` | inside `map_ω`'s proof: `simp_rw [ω, …, map_compl₂EDSAux, …]` |
| `LutzNagell/ZSMul.lean:279` | `rw [smulY, ω, redInvarDenom_two, one_mul, compl₂EDSAux_two, sub_zero, …]` (the `z·Y` addition formula) |

Same-file API built on it (EllipticDivisibilitySequence.lean): `compl₂EDSAux_zero/one/neg_one/two/neg_two` (5 `@[simp]` value lemmas), `compl₂EDSAux_mul_b` (1026), `compl₂EDSAux_neg` (1036), `redInvarNum` (1359), `compl₂EDS_eq_redInvarNum_sub` (1362), `invarNum_eq_redInvarNum_mul` (1367), `map_compl₂EDSAux` (1416), `map_redInvarNum` (1419). (Also duplicated in the `…Original.lean` snapshot and the HasseWeil fork.)

Inline-derivation grep (re-derived elsewhere without using `compl₂EDSAux`?): **none** — every use goes through the name.

Call-sites signal: this is a **real, reused internal API** (K ≥ 3 across files + a value/naturality lemma cluster), with **no inline bypass** → composability signal leans YES/keep. But every consumer is *inside the very `ω`/`redInvarNum` layer this fork is building to upstream* — there are **no consumers independent of `ω`/`redInvarNum`**. So the "real API" signal is entirely *internal to the ω-upstreaming effort*, which is exactly why the verdict is coupled to how `ω` lands (Phase 7).

### Composition check (Phase 6)

Can `compl₂EDSAux b c d m` be obtained from mathlib in ≤3 calls? It is a single
product `preNormEDS (b^4) c d (m-2) * preNormEDS (b^4) c d (m+1)^2 * (parity)` —
each factor is a mathlib `preNormEDS` call, so the *value* is a ≤3-call mathlib
expression and could be **inlined**:

Attempt 1 (inline the body):
```lean
-- at each ω/redInvarNum site, write directly:
preNormEDS (b ^ 4) c d (m - 2) * preNormEDS (b ^ 4) c d (m + 1) ^ 2 * (if Even m then 1 else b)
```
  - Mathlib decls used: `preNormEDS` (×2), `Even`, `ite`. Result: **succeeds** as a value (it is literally the body). Notes: this is "inline the one-liner", not "compose a different mathlib primitive".

Attempt 2 (route through the parent `complEDS₂`): the named literature atom
`complEDS₂` is in mathlib; `compl₂EDSAux·b` is its subtrahend half
(`complEDS₂_mul_b` gives `complEDS₂·b = W(m-1)²W(m+2) − W(m-2)W(m+1)²`). If the
upstream `ω` were phrased via `ψ_{2n}/ψ_n` (the route mathlib's own docstring
prescribes), `compl₂EDSAux` would be subsumed by `complEDS₂` and **need not
exist**. But re-expressing the *current* division-free `ω` definition this way is
a non-trivial restructuring of `ω` + `ω_spec`, not a ≤3-call swap.

Conclusion: **COMPOSABLE-AS-INLINE but NOT cleanly-NO**. The body is a ≤3-call
mathlib expression (so a pure NO-composable is defensible if one is willing to
inline at the 3 sites + drop the value/naturality lemmas), yet the decl is a
deliberately-named shared subterm of an explicit-TODO mathlib object, and the
"better" composition (via `complEDS₂`) requires redesigning `ω`. The choice
between "inline it / route via `complEDS₂`" and "keep it as `ω`'s private
helper" is a formalisation-design judgment — hence BORDERLINE.

---

## Verdict: `compl₂EDSAux`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature search (Phase 3): the NAMED literature objects are `ω_n`, the *full* bracket `ψ_{n-1}²ψ_{n+2} − ψ_{n-2}ψ_{n+1}²`, and the EDS complement; the single product `ψ_{n-2}ψ_{n+1}²` (= `compl₂EDSAux·b`) is **never separately named**.
- Generality analysis (Phase 4): MAXIMALLY GENERAL / already the modern division-free `CommRing` idiom; nothing to weaken (4b), no further modernisation (4c).
- Mathlib search (Phase 5): `compl₂EDSAux` is **not in mathlib** (definitive); but its parent `complEDS₂` IS (line 246, with `complEDS₂_mul_b`), and the `ωₙ` it feeds is an **explicit mathlib TODO** (DivisionPolynomial/Basic.lean:71,83).
- Composition check (Phase 6): the body is a ≤3-call mathlib expression (inline-able); K≥3 real internal uses but **all internal to the `ω`/`redInvarNum` upstreaming layer**, no inline bypass; the clean `complEDS₂` route requires restructuring `ω`.

**Rationale.**
`compl₂EDSAux` sits exactly on the fence. On the YES side: it is genuinely absent
from mathlib, it is a *reused* named building block (3 cross-file `.lean`
consumers + a value/naturality lemma cluster + `map_compl₂EDSAux`), and the object
it builds — `WeierstrassCurve.ω` — is one of the few **explicitly TODO'd** items
in mathlib's division-polynomial file. The natural way that TODO gets discharged
is a PR that adds `WeierstrassCurve.ω` together with its EDS-level scaffolding,
and `compl₂EDSAux` (alongside `redInvarDenom`, `compl₂EDS`/`complEDS₂`,
`redInvarNum`) is part of that scaffolding — the same disposition the sibling
reports reached for `two_mul_ω` (`YES-add-as-is`, "ships with the `ω` definition")
and `map_ω`.

On the NO side: (1) it is a **one-line, literature-unnamed** convenience — the
literature consistently names the *whole* bracket and the complement, not the
subtrahend monomial; (2) mathlib **already** has the parent complement
`complEDS₂` and the relation `complEDS₂_mul_b`, and mathlib's own ω docstring
defines `ωₙ = (ψ₂ₙ/ψₙ − …)/2`, i.e. *through* the `ψ₂ₙ/ψₙ` complement — under
that phrasing `compl₂EDSAux` would be subsumed and need not exist as a separate
def; (3) the body is itself a ≤3-`preNormEDS`-call expression, so a pure
"inline it" NO-composable is defensible. Whether the upstream `ω` keeps this
exact division-free auxiliary (as the project's `WeierstrassCurve.ω` does, by
construction, to stay division-free) or is restructured to ride on the
already-upstream `complEDS₂` is a **formalisation-design decision for the `ω`-PR
author** that the literature/mathlib evidence does not force. The decl is also
*not* in the verbatim-fork bucket — unlike its neighbour `complEDS₂` (which is
byte-identical to mathlib and is a clean `NO-mathlib-has-it`), `compl₂EDSAux`
has **no upstream counterpart at all**; so "delete the fork" is the wrong action
for it. That is precisely a human judgment call, so the verdict is BORDERLINE.

**Numbered questions (≤5):**
  1. Will `WeierstrassCurve.ω` be upstreamed with the project's **current
     division-free definition** (which names `compl₂EDSAux` as a subterm)? If
     yes → `compl₂EDSAux` ships **with that `ω` PR** as a supporting `def`
     (effectively `YES-add-as-is`, grouped with `redInvarDenom` / `compl₂EDS` /
     `redInvarNum` / `two_mul_ω` / `map_ω`).
  2. Or will the upstream `ω` be defined via mathlib's docstring formula
     `ωₙ = (ψ₂ₙ/ψₙ − ψₙ(a₁φₙ + a₃ψₙ²))/2`, routed through the already-upstream
     `complEDS₂`/`complEDS₂_mul_b`? If yes → `compl₂EDSAux` is **subsumed**;
     inline it (or drop it) → `NO-composable-from-mathlib`.
  3. Independent of `ω`, do you want the *reduced-invariant* layer
     (`redInvarNum`/`invarNum`) upstreamed at all? `compl₂EDSAux`'s second
     consumer is `redInvarNum`; if that layer stays project-local, that consumer
     does not argue for upstreaming `compl₂EDSAux`.
  4. If it does ship: keep the name `compl₂EDSAux` (Angdinata's
     `complEDS₂`/`preNormEDS` naming family suggests `complEDS₂Aux` or
     `preComplEDS₂` for consistency — note the project name puts `₂` mid-word),
     and should it be a `private`/`protected` helper rather than public API,
     given it is not a literature object?

**Next action.** User answers Q1–Q3 (the disposition is fully determined by how
`WeierstrassCurve.ω` is upstreamed). If Q1=yes → re-run resolves to
**YES-add-as-is**, grouped into a single `feat(AlgebraicGeometry): add
WeierstrassCurve.ω` PR with `redInvarDenom`, `compl₂EDS`, `redInvarNum`,
`two_mul_ω`, `map_ω` (and discharging the
`DivisionPolynomial/Basic.lean:71,83` TODO). If Q2=yes → **NO-composable-from-
mathlib**: inline the body at DivisionPolynomialOmega.lean:78 / ZSMul.lean:279
(routing the bracket through `complEDS₂_mul_b`) and drop the standalone def.
This is the **same coupled decision** that governs the whole `ω`-family of this
fork; resolve it once for all of them together.

---

## Next step

Ask the user how `WeierstrassCurve.ω` will be upstreamed (Q1 vs Q2 above) — that
single choice determines whether `compl₂EDSAux` is `YES-add-as-is` (ships as a
helper inside the `ω` PR that discharges mathlib's ωₙ TODO) or
`NO-composable-from-mathlib` (inlined / subsumed by the already-upstream
`complEDS₂`). Decide it jointly with the sibling `ω`-family decls
(`redInvarDenom`, `compl₂EDS`/`complEDS₂`, `redInvarNum`, `two_mul_ω`, `map_ω`),
not in isolation.
