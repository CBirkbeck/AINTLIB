# /mathlibable report — `compl₂EDSAux_zero`

## Verdict: **BORDERLINE-needs-human** (a `@[simp]` boundary value of the project-local half-complement helper `compl₂EDSAux`; its fate is inherited from that def, which is itself BORDERLINE — it discharges mathlib's open `ωₙ` TODO but is a literature-unnamed division-free split that mathlib may or may not want)

One-line rationale: `@[simp]` boundary value of the fork-local helper `compl₂EDSAux`; inherits the parent def's BORDERLINE verdict (mathlib lacks the half-complement; whether `ω` upstreams via it is a human call).

> Re-assessed 2026-06-21 (reasoned from source; local build stale). Supersedes an earlier
> NO-mathlib-has-it draft: the two key mathlib facts below were **re-verified live against the
> mathlib4 docs**, and the verdict is realigned to *inherit from the parent `def compl₂EDSAux`*
> (assessed BORDERLINE-needs-human in `compl₂EDSAux.md`), matching the directly-analogous sibling
> `compl₂EDSAux_two`. See "Reconciliation with siblings" at the end.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task brief); reasoned from source + live mathlib4 docs verification.
- decl `compl₂EDSAux_zero`:  ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1019` (the line the task cited, 1020, is within the same simp-lemma cluster; the decl itself is L1019).
- kind:                      `lemma` (`@[simp]`)
- has sorry:                 no
- qualified name:            **`compl₂EDSAux_zero`** — top-level, **no namespace**. VERIFIED: the decl sits in `section Complement` (L1010) ⊂ `section NormEDS` (L881); the file's `@[expose] public section` (L81) is *not* a namespace. The nearest `namespace EllSequence` closed at `end EllSequence` (L597); the next one only opens at L1079 — *after* L1019. `IsEllSequence` (L643) closed at L702. So no namespace prefix applies.
- module docstring summary:  "Elliptic divisibility sequences" — defines `preNormEDS`/`normEDS` and the normalised-EDS API. **This file is an extended fork of `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`** (same author header, David Kurniadi Angdinata): a near-verbatim copy of the upstream content *plus* ~1100 extra lines adding the `invarNum`/`redInvarNum`/`compl₂EDS`/`compl₂EDSAux` + `ω`-division-polynomial layer for the Nagell–Lutz development.

### Statement (Phase 1)

```lean
@[simp] lemma compl₂EDSAux_zero : compl₂EDSAux b c d 0 = -1 := by simp [compl₂EDSAux]
```

where (L1016–1017):
```lean
/-- An auxiliary expression that appears in the definition of the numerator of
the reduced invariant and in the definition of the `ω` family of division polynomials. -/
def compl₂EDSAux : R :=
  preNormEDS (b ^ 4) c d (m - 2) * preNormEDS (b ^ 4) c d (m + 1) ^ 2 * if Even m then 1 else b
```

`compl₂EDSAux_zero` is a **boundary-value (`@[simp]` evaluation) lemma**: with `p := preNormEDS (b^4) c d`, at `m = 0` the parity factor is `1` (since `0` is even) and the value is `p(−2) · p(1)² · 1 = (−1)·1²·1 = −1` (using `preNormEDS_one = 1`, and `p(−2) = −p(2) = −1`). It is one of a family of five such `@[simp]` lemmas: `_zero = -1`, `_one = -b`, `_neg_one = 0`, `_two = 0`, `_neg_two = -d`.

**What `compl₂EDSAux` actually is (crucial for the verdict).** It is **one summand** — the subtrahend product `p(m−2)·p(m+1)²` (times a parity factor) — of the EDS **2-complement / duplication bracket**, *not* the complement itself. Equivalently `compl₂EDSAux b c d m · b = W(m−2)·W(m+1)²` where `W = normEDS b c d` (project `compl₂EDSAux_mul_b`, L1026). The *full* 2-complement is the **difference of two** such products: `compl₂EDS b c d m · b = W(m−1)²·W(m+2) − W(m−2)·W(m+1)²` (project `compl₂EDS_mul_b`, L1063). The project carved out this half so the identical product can be reused verbatim in `WeierstrassCurve.ω` (the Y / Jacobian-second-coordinate division polynomial, `DivisionPolynomialOmega.lean:74–78`) and in `redInvarNum` — i.e. it exists to write `ω` **without division**.

- Variables (Lean side): `{R : Type u} [CommRing R]` (file-level); `b c d : R` (the three normalised-EDS seeds `W(2)=b, W(3)=c, W(4)=d·b`); index specialised to `0 : ℤ`.
- Hypotheses: none.
- Conclusion (math): the auxiliary half-complement product, at index `0`, equals `−1`.
- Conclusion (Lean): `compl₂EDSAux b c d 0 = -1`.

### Size classification (Phase 2a)

Verdict: **SMALL** (with a BIG association).
Reason: a one-line `@[simp]` boundary-value evaluation lemma of a helper `def`; not a structure, not a named theorem, not a `## Main results` entry. *However* it is part of the API of a BIG object — `WeierstrassCurve.ω`, an explicitly-TODO'd mathlib family — so its fate is coupled to that def. (Literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → the def one-liner gate is **n/a**. For the record: the *proof* is a single `by simp [compl₂EDSAux]` (pure unfold + `preNormEDS` boundary simp-lemmas), and the *parent* `compl₂EDSAux` is itself a one-line `def`. **Glue-lemma inheritance applies**: this lemma's mathlib fate is governed entirely by the fate of `def compl₂EDSAux` (carried to Phase 7).

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | mathlib `complEDS₂` EllipticDivisibilitySequence complement normEDS W(2k) divides                       | yes  | mathlib `complEDS₂` — the **2-complement** `W(k)·Wᶜ₂(k)=W(2k)` | docs return `complEDS₂`'s exact body (see Phase 5); confirms the *full* complement is upstream. No "auxiliary half-complement" named anywhere. |
|  2 | WebSearch (general form)         | "division polynomial" ω elliptic curve ψ scalar mult Jacobian coords; `ωₙ = (ψ_{n+2}ψ_{n-1}² − ψ_{n-2}ψ_{n+1}²)/…` | yes  | `[n]P = (φ/ψ², ω/ψ³)`; ψ,φ,ω the three division polys; the **full bracket** is the named object | the single summand `ψ_{n-2}ψ_{n+1}²` is **not** a named object — implementation device. |
|  3 | WebSearch (named-after / aliases)| "2-complement" / "complement sequence" elliptic; Ward / Stange / Shipsey                                | yes  | the only "complement" object is the **full** complement (`complEDS₂`) | no literature name for a *half*. |
|  4 | ChatGPT MCP                      | standard form + generality of the EDS "complement" and its constituent products                         | n/a  | —                                | MCP down per task brief (fallbacks used: live WebSearch ×3 + WebFetch of mathlib docs + by-hand value re-derivation). |
|  5 | Local references                 | `.mathlib-quality/references/` for "complement / EDSAux / division polynomial / omega"                  | n/a  | —                                | directory absent for NagellLutz (`ls` → not found). Recorded n/a. |
|  6 | nLab                             | elliptic divisibility sequence / division polynomial                                                    | n/a  | —                                | not a category-theoretic concept; no EDS half-complement page. |
|  7 | nCatLab                          | —                                                                                                       | n/a  | —                                | not categorical. |
|  8 | Stacks Project                   | division polynomial / EDS                                                                                | n/a  | —                                | Stacks does not develop explicit division polynomials; out of scope. |
|  9 | MathOverflow / Math.SE           | elliptic divisibility sequence complement summand naming                                                | n/a  | —                                | community names ψ/φ/ω + the complement, never the single summand. |
| 10 | arXiv (recent ≤5 yr)             | EDS recurrence over commutative rings (2102.07573, 2604.05280); Stange elliptic nets                    | yes (context) | ψ/φ/ω + EDS recursion; full bracket | confirms ω is standard and the *split* is not a named object. |

### Literature summary (Phase 3)

Concept identified as: the **subtrahend product term** `ψ_{m−2}·ψ_{m+1}²` (b-reduced) of the EDS **2-complement / ω-division-polynomial bracket**. The target lemma is its **boundary value at 0** (`= −1`).
Sources agree on the standard form: **yes for the NAMED objects** — ψ_m (= `normEDS`), φ_m, **ω_m**, the *full* bracket `ψ_{m−1}²ψ_{m+2} − ψ_{m−2}ψ_{m+1}²`, and the EDS complement `W(2m)/W(m)`. They **uniformly do NOT name** the single summand `ψ_{m−2}ψ_{m+1}²` — `compl₂EDSAux` is an implementation device for writing `ω` without the classical `/2`, `/ψₘ`, `/y` divisions.
Most general standard form: the named atoms are `ω_m` and the *full* complement `complEDS₂` (already in mathlib, see Phase 5); `compl₂EDSAux` is a strict sub-expression of `complEDS₂·b`.
Disagreement with the literature: the very *existence of a name* for this half-term is non-standard; the literature inlines it inside the ω/complement bracket.

### Generality analysis — `compl₂EDSAux_zero`

Literature-standard form (from Phase 3): the *full* complement and its boundary values (`complEDS₂_zero = 2`, …) — already mathlib's; and `ω_m`. There is no literature object "value of the EDS half-complement at 0" to weaken toward.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]` (file-level) | commutative ring | classical: field with `2y`; modern: commutative ring | NO | mathlib's entire EDS API (`preNormEDS`/`normEDS`/`complEDS₂`) lives over `CommRing`; this is already the modern division-free form. Cannot drop below `CommRing` (needs `−`,`·`,`1`). |
| 2 | `b c d : R` | three ring seeds | three ring seeds | NO | identical to mathlib's `normEDS`/`complEDS₂` signature. |
| 3 | index `0 : ℤ` | a fixed integer boundary | a fixed integer boundary | n/a | this *is* the value-at-0 lemma; generalising the index gives a different lemma (`compl₂EDSAux_mul_b`, already present). |

### Generality verdict (Phase 4b)

The current form is **MAXIMALLY GENERAL** (it inherits mathlib's exact EDS typeclass setting; nothing to weaken). K = 0 weakening opportunities. Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Reformulation | Downstream |
|----|----------|----------|---------------|------------|
| 1 | typeclasses instead of bundled hypotheses? | no | already `[CommRing R]` | — |
| 2 | filters/topology instead of sequences/metric? | no | purely algebraic finite identity | — |
| 3 | universal-property class instead of construction? | no | a boundary value, not a construction | — |
| 4 | bundled substructure instead of set+closure? | no | n/a | — |
| 5 | weaken vector-space/field to module/ring? | no | already `CommRing` | — |
| 6 | higher-categorical generalisation? | no | n/a | — |
| 7 | concrete index → arbitrary monoid/group? | no | EDS is intrinsically `ℤ`-indexed; the index is fixed to `0` by design | — |

Modern idiom available: **no** — a finite ring computation at a fixed boundary of an already-idiomatic `CommRing`/`ℤ`-indexed EDS definition. The only "modernisation" in this corner is the one mathlib already performed (`preNormEDS`/`complEDS₂`, the division-free `b⁴`-reduction).

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no new definitional equalities or typeclass-search paths). (The risk question attaches to the *parent* `def compl₂EDSAux`, assessed NONE in `compl₂EDSAux.md` — semireducible, no instances, unfolded explicitly via `simp_rw [compl₂EDSAux, …]`.)

### Mathlib search-status: `compl₂EDSAux_zero`

```
[A] Lean-Finder       (index unavailable in-env)                          n/a — covered by [D]/[E] + live docs
[B] Loogle            `compl₂EDSAux`, `?a * ?b ^ 2 * ite _ 1 _ = -1`       no hit for the aux; the shape is too generic to match usefully; nearest = `complEDS₂_*` family
[C] LeanSearch        "elliptic divisibility sequence complement value at zero"   no hit for the *half*; surfaces mathlib `complEDS₂_zero` (the FULL complement at 0)
[D] Grep mathlib src  `grep -rn "compl₂EDSAux|complEDSAux|EDSAux" Mathlib/`        ZERO hits anywhere in mathlib — the helper does not exist upstream
[E] Name pattern      `complEDS₂` / `complEDS₂_zero` in mathlib EDS file           HIT (verified live, see below)
```

**Live verification (2026-06-21), via WebSearch + WebFetch of the mathlib4 docs:**

1. **Mathlib HAS the full complement `complEDS₂`**, and its body is *character-for-character* this fork's `compl₂EDS` (L1032–1033). The docs return:
   ```
   complEDS₂ b c d k =
     (preNormEDS (b^4) c d (k-1) ^ 2 * preNormEDS (b^4) c d (k+2)
        - preNormEDS (b^4) c d (k-2) * preNormEDS (b^4) c d (k+1) ^ 2) * if Even k then 1 else b
   ```
   with `preNormEDS (b^4) c d k * complEDS₂ b c d k = preNormEDS (b^4) c d (2k) * if Even k then 1 else b`, and boundary lemmas `complEDS₂_zero = 2`, `complEDS₂_one = b`, `complEDS₂_two = d`, `complEDS₂_neg`, plus `normEDS_mul_complEDS₂` / `complEDS₂_mul_b`. *(Source: `Mathlib/NumberTheory/EllipticDivisibilitySequence.html`.)*
2. **Mathlib does NOT have `compl₂EDSAux`** (the half-complement subtrahend) — zero `*EDSAux*` hits — because mathlib keeps the complement as one subtraction and never splits off the subtrahend.
3. **`ωₙ` is an explicit, open mathlib TODO.** WebFetch of `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.html` confirms verbatim in *Main definitions*: **"TODO: the bivariate polynomials ωₙ."** Mathlib currently defines ψₙ, ψ₂, Ψₙ, preΨₙ, ΨSqₙ, Φₙ, φₙ, Ψ₂Sq — **but not ωₙ**. The NagellLutz project's `DivisionPolynomialOmega.lean:74` (`protected def ω`) is exactly the development that would discharge that TODO, and `compl₂EDSAux` is the division-free helper introduced to write that `ω` over a general `CommRing`.

Searched for both forms:
- the user's current form (`compl₂EDSAux_zero` / `compl₂EDSAux`) → **not in mathlib at all**;
- the literature-standard / parent form (the *full* complement and its boundary value) → **in mathlib**: `complEDS₂` *is* this fork's `compl₂EDS` verbatim, and `complEDS₂_zero : complEDS₂ b c d 0 = 2` exists.

Concluded: the **full** complement (`compl₂EDS`) is a verbatim fork of mathlib's `complEDS₂`; but the **half** complement `compl₂EDSAux` — the subject of *this* lemma — has **no mathlib counterpart**, and the object it builds (`ωₙ`) is an explicit upstream TODO.

### Call sites — `compl₂EDSAux_zero`

Internal use count of the **lemma** `compl₂EDSAux_zero`: **0 explicit named uses** — it is `@[simp]`, consumed implicitly wherever `compl₂EDSAux _ _ _ 0` is normalised (e.g. in proving `ω_zero : W.ω 0 = 1`, `DivisionPolynomialOmega.lean:95`, `by simp [ω]`).

For context, the **parent def** `compl₂EDSAux` is real, reused API (this matters for inheritance):

| Caller file:line | Usage pattern |
|------------------|---------------|
| `LutzNagell/DivisionPolynomialOmega.lean:78` | `… − compl₂EDSAux W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n + …` — inside `def WeierstrassCurve.ω` (the Y-coordinate division polynomial; the ωₙ TODO) |
| `LutzNagell/DivisionPolynomialOmega.lean:112` | `simp_rw [ω, …, map_compl₂EDSAux, …]` in the `map_ω` naturality proof |
| `LutzNagell/ZSMul.lean:279` | `rw [smulY, ω, redInvarDenom_two, one_mul, compl₂EDSAux_two, sub_zero, …]` — point-doubling Y-coord |
| `LutzNagell/EllipticDivisibilitySequence.lean:1026,1035,1359,1362,1416` | `compl₂EDSAux_mul_b`, `compl₂EDSAux_neg`, `redInvarNum`, `compl₂EDS_eq_redInvarNum_sub`, `map_compl₂EDSAux` |

Inline-derivation grep (was `compl₂EDSAux b c d 0` re-derived elsewhere without the lemma?): **none** — the value `−1` at `0` flows only through this `@[simp]` lemma. (`compl₂EDSAux_zero` also appears in `EllipticDivisibilitySequenceOriginal.lean`, but that is a **dead, non-imported backup** — not a live call site.)

Call-sites signal: the *def* is real, load-bearing, project-only API (the `ω`/Nagell–Lutz machinery genuinely needs it). The *lemma* under assessment is a boundary-value `@[simp]` fact whose worthiness is entirely **parasitic on the def** — it travels with the def or not at all.

### Composition check (Phase 6)

Can `compl₂EDSAux_zero` be derived from mathlib in ≤3 chained calls?

- **Attempt 1 (the actual proof):** `by simp [compl₂EDSAux]` — but `compl₂EDSAux` is **fork-local**; mathlib cannot even *state* this lemma without importing the helper def. Mathlib decls used: none applicable to the half. Result: **not a mathlib composition** — the subject term isn't in mathlib.
- **Attempt 2 (route via mathlib's `complEDS₂`):** mathlib has `complEDS₂_zero : complEDS₂ b c d 0 = 2` (the *full* complement). There is **no** mathlib lemma giving the *half*-complement value `−1`, because mathlib never splits the complement. Result: partial — mathlib has the boundary lemma for the *full* object, not for the half.

Conclusion: **NOT-COMPOSABLE from mathlib** in the strict sense — the subject `compl₂EDSAux` is not a mathlib object, so there is nothing to compose *to*. Within the project it is a trivial 1-step `simp`-unfold of a def mathlib lacks. (Contrast the *full*-complement boundary lemma, which mathlib does own as `complEDS₂_zero`.)

---

## Verdict: `compl₂EDSAux_zero`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature search (Phase 3): the `ω`/complement and ψ/φ are standard and (mostly) upstream, but the **half-complement `compl₂EDSAux` is not a named literature object** — it is a division-free implementation device for `ω`.
- Generality analysis (Phase 4): MAXIMALLY GENERAL (`CommRing`, `ℤ`-indexed); nothing to weaken (4b); no modern-idiom move (4c all "no").
- Mathlib search (Phase 5, **live-verified**): `compl₂EDSAux` has **zero hits** in mathlib; the *full* complement `compl₂EDS` IS mathlib's `complEDS₂` verbatim (with `complEDS₂_zero = 2`); but the **half** and its consumer `ωₙ` are **not** — `ωₙ` is an **explicit open TODO** (`DivisionPolynomial/Basic.lean`, "TODO: the bivariate polynomials ωₙ").
- Composition check (Phase 6): NOT-COMPOSABLE from mathlib (the parent `def` is absent); a trivial `simp`-unfold once the project's def exists.

**Rationale.**
This lemma **cannot be assessed in isolation**: it is a `@[simp]` boundary-value fact (`compl₂EDSAux b c d 0 = -1`, proof `by simp [compl₂EDSAux]`) about a **project-introduced auxiliary `def compl₂EDSAux`** that has no mathlib counterpart. Its mathlib fate is therefore **inherited** from that def — and the parent def was assessed **BORDERLINE-needs-human** (`compl₂EDSAux.md`), for reasons that survive scrutiny here.

The tension is genuine and the evidence does not force a resolution. On the one hand, `compl₂EDSAux` is genuinely **not** in mathlib (definitive grep + live docs), it is a *reused* named building block (cross-file consumers in `ω`, `map_ω`, `redInvarNum`, `ZSMul` + a value/naturality lemma cluster), and the object it builds — `WeierstrassCurve.ω` — is one of the few **explicitly TODO'd** items in mathlib's division-polynomial file. That pulls toward "ships upstream as a helper inside the `ω` PR that discharges the ωₙ TODO" (the disposition the sibling reports reached for `two_mul_ω`/`map_ω`). On the other hand: (1) it is a **one-line, literature-unnamed** convenience — the literature names the *whole* bracket and the complement, never the single subtrahend monomial; (2) mathlib **already** has the parent complement `complEDS₂` (= this fork's `compl₂EDS`, verbatim) and `complEDS₂_mul_b`, and mathlib's own ω plan in the docstring is `ωₙ = (ψ₂ₙ/ψₙ − …)/2`, i.e. routed *through* the `ψ₂ₙ/ψₙ` complement — under that phrasing `compl₂EDSAux` would be **subsumed** and need not exist as a separate def. Whether the upstream `ω` keeps this exact division-free auxiliary split (as the project's `WeierstrassCurve.ω` does, by construction, to stay division-free) or is restructured to ride on the already-upstream `complEDS₂` + the existing `ψ/φ` machinery is a **formalisation-design decision for the `ω`-PR author** that the evidence does not settle.

Because this is precisely a maintainer/taste judgment about the parent def — and this `_zero` lemma is pure `@[simp]` glue that inherits whatever that def's fate is — the correct bucket is **BORDERLINE-needs-human**, deferring to the parent-def design question. (It is *not* a clean `NO-mathlib-has-it`: mathlib demonstrably does **not** have `compl₂EDSAux` — the half — and `NO-mathlib-has-it` would mis-state the search result by conflating the half with the full `complEDS₂`. It is *not* `YES-add-as-is` for a standalone PR: a `simp` boundary lemma never ships alone. It is *not* a meaningful `NO-composable-from-mathlib`: you cannot inline a fact about a def mathlib lacks; the only "composition" is `simp [compl₂EDSAux]`, which presupposes the project's def.)

**Numbered questions (≤5) — the disposition is fully determined by how `WeierstrassCurve.ω` upstreams:**

1. The real subject is `def compl₂EDSAux` (this `_zero` lemma just inherits its fate). When mathlib discharges its `ωₙ` TODO (`DivisionPolynomial/Basic.lean`: "TODO: the bivariate polynomials ωₙ"), will `ω` be built via this **division-free auxiliary split** (`compl₂EDSAux` = the `ψ_{m−2}ψ_{m+1}²` summand) — in which case `compl₂EDSAux` and this lemma ship **with that `ω` PR** (effectively YES-add-as-is, grouped with `redInvarDenom`/`compl₂EDS`(=`complEDS₂`)/`redInvarNum`/`two_mul_ω`/`map_ω`)?
2. Or will the upstream `ω` use mathlib's docstring formula `ωₙ = (ψ₂ₙ/ψₙ − ψₙ(a₁φₙ + a₃ψₙ²))/2`, routed through the already-upstream `complEDS₂`/`complEDS₂_mul_b`? If yes → `compl₂EDSAux` is **subsumed**; inline/drop it → this lemma is `NO-composable-from-mathlib` (and disappears).
3. If `compl₂EDSAux` *does* ship: rename to mathlib's convention (e.g. `complEDS₂Aux` / `preComplEDS₂`, matching `complEDS₂` — the project spelling puts `₂` mid-word) and make it `private`/`protected` (it is not a literature object), shipped *together with* the whole `ω`/`redInvar` block as one PR rather than as an orphan auxiliary?

**Next action (verbatim):** user answers Q1–Q3, then re-run — better, run `/mathlibable` on `def compl₂EDSAux` first and let this `@[simp]` lemma's verdict inherit from it. If Q1=yes → resolves to **YES-add-as-is** (this lemma rides along inside the `feat(AlgebraicGeometry): add WeierstrassCurve.ω` PR that discharges the ωₙ TODO). If Q2=yes → **NO-composable-from-mathlib** (inline/subsume via `complEDS₂`). Decide it **jointly for the whole `ω`-family** of this fork (`redInvarDenom`, `compl₂EDS`/`complEDS₂`, `redInvarNum`, `two_mul_ω`, `map_ω`, the five `compl₂EDSAux_*` value lemmas), not in isolation. Do **not** delete it meanwhile (its `@[simp]` role normalises `ω_zero`).

---

## Reconciliation with sibling reports

The five `@[simp]` value lemmas of `compl₂EDSAux` were assessed across several sessions and currently carry **divergent buckets** — a coordination artifact, not a mathematical disagreement, since *all five inherit from the same parent def*:

| sibling | line | current bucket | note |
|---|---|---|---|
| `compl₂EDSAux_zero` (this) | 1019 | **BORDERLINE-needs-human** | realigned here to the parent def |
| `compl₂EDSAux_one` | 1020 | NO-composable-from-mathlib | treats it as glue around a project-local def |
| `compl₂EDSAux_neg_one` | 1021 | (see its report) | |
| `compl₂EDSAux_two` | 1022 | **BORDERLINE-needs-human** | same reasoning as here |
| `compl₂EDSAux_neg_two` | 1023 | NO-mathlib-has-it | treats the whole `compl₂EDS`/Aux track as a redundant `complEDS₂` fork |
| **parent** `compl₂EDSAux` (`def`) | 1016 | **BORDERLINE-needs-human** | the authoritative verdict the lemmas inherit |

This report follows the **parent def's** verdict (`compl₂EDSAux.md` → BORDERLINE-needs-human) and the directly-analogous `compl₂EDSAux_two`. The `NO-mathlib-has-it` framing (used for `_neg_two`) is defensible *for the full complement* `compl₂EDS` — which genuinely is mathlib's `complEDS₂` verbatim — but **over-claims for the half** `compl₂EDSAux`, which has no mathlib counterpart and exists to discharge the open `ωₙ` TODO. The `NO-composable-from-mathlib` framing (used for `_one`) understates the live upstreaming relevance (the `ωₙ` TODO). The single human decision in Q1/Q2 collapses **all five** lemmas + the parent def into one bucket simultaneously; they should be re-stamped together once that decision is made.

---

## Next step

Treat `compl₂EDSAux_zero` as **inherited from `def compl₂EDSAux`** (BORDERLINE-needs-human). Run `/mathlibable` on the parent `def compl₂EDSAux` and answer Q1–Q3 above; the whole `ω`-family of this fork (the def, its five `@[simp]` value lemmas, `compl₂EDSAux_mul_b`/`_neg`/`map_compl₂EDSAux`, `redInvarDenom`, `redInvarNum`, `two_mul_ω`, `map_ω`) should be bucketed in one decision against mathlib's open `ωₙ` TODO. Do not open a standalone PR for this `@[simp]` boundary lemma, and do not delete it (its `@[simp]` role normalises `ω_zero` and friends).
