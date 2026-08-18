# /mathlibable report — `LutzNagell.LutzNagellTheorem.x_integral_of_nsmul_x_integral_general`

> NOTE: this report supersedes an earlier draft that recorded **K = 1** call site
> ("GeneralIntegralMultiple.lean:106, used by `integral_of_nsmul_integral_general`").
> That was a **factual error**: the file is only 94 lines (no line 106), and a
> repo-wide grep shows the lemma name occurs **exactly once** — at its own
> declaration (line 66). The sibling `integral_of_nsmul_integral_general` (line 82)
> calls `PID.isInteger_of_nsmul_isInteger` *directly* (line 89), bypassing this
> lemma; the real consumers in `GeneralMain.lean` (lines 74, 102) call that sibling.
> So the true call count is **K = 0**, which changes the verdict (below).

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task brief — reasoned from source)
- decl `LutzNagell.LutzNagellTheorem.x_integral_of_nsmul_x_integral_general`:
                            resolved at `projects/NagellLutz/LutzNagell/LutzNagellTheorem/GeneralIntegralMultiple.lean:66` (theorem head; conclusion line 72)
- qualified name VERIFIED:  `LutzNagell.LutzNagellTheorem.x_integral_of_nsmul_x_integral_general` (namespaces `LutzNagell` → `LutzNagellTheorem`, file lines 26–27)
- kind:                     theorem
- has sorry:                no (body = one call to the general PID lemma + the defeq bridge `isInteger_int_iff`)
- module docstring summary: "Integral multiple implies integral point (general Weierstrass curves)" — the `ℤ/ℚ` specialisations (lines 17–23) of the `LutzNagell.PID` UFD-track lemmas.

### Statement (Phase 1)

`x_integral_of_nsmul_x_integral_general` is a **theorem** stating:

> Let `W` be a Weierstrass curve over `ℤ`, `curveQ W` its base-change to `ℚ`, and `P = (x,y)` a nonsingular affine rational point on `curveQ W`. Fix `n ≠ 0` and suppose `n • P = P' = (x', y')` with `P'` nonsingular. If the x-coordinate `x'` of `nP` is an integer (witness `c : ℤ`, `(c:ℚ)=x'`), then the x-coordinate `x` of `P` is an integer (`∃ x₀ : ℤ, (x₀:ℚ)=x`).

Mathematically this is the **x-coordinate integral-descent step of the Nagell–Lutz theorem**: `x(nP) = Φₙ(x)/Ψₙ²(x)`, so `x'·Ψₙ²(x) = Φₙ(x)`, making `x` a root of the monic ℤ-polynomial `Φₙ − C x' · Ψₙ²` (monic because `deg Φₙ = n² > n²−1 = deg Ψₙ²`); a rational root of a monic ℤ-polynomial is integral.

Variables (Lean): `W : WeierstrassCurve ℤ`; `x y x' y' : ℚ`; `n : ℤ`; `c : ℤ`.
Hypotheses (Lean): `hns`/`hns'` (both points nonsingular); `hn : n ≠ 0`; `hnP : n • (some hns) = some hns'`; `hc : (c:ℚ)=x'`.
Conclusion (math): `x(P) ∈ ℤ`.
Conclusion (Lean): `∃ x₀ : ℤ, (x₀:ℚ) = x`.

The proof body (lines 73–74) is literally:
```lean
isInteger_int_iff.mp <| PID.x_isInteger_of_nsmul_x_isInteger W hns hn (by exact_mod_cast hn)
  hns' hnP (by simpa only [...] using hc)
```
— one call to the **general UFD lemma** `PID.x_isInteger_of_nsmul_x_isInteger` plus the bridge `isInteger_int_iff` (line 34) that unfolds `IsLocalization.IsInteger ℤ x` to `∃ x₀:ℤ,(x₀:ℚ)=x`.

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: an explicit specialisation wrapper — the per-lemma docstring (line 65) and module docstring (lines 17–23) state it is the `ℤ/ℚ` (`R=ℤ, K=ℚ`) specialisation of `PID.x_isInteger_of_nsmul_x_isInteger`. Not a `## Main results` entry; not a named theorem (the *named* result is the downstream Nagell–Lutz statement in `GeneralMain`, not this x-descent shadow). One of three `*_general` specialisation wrappers in the file. (Literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `theorem` → n/a (one-line check is for `def`/`abbrev`/`structure`). Body is a 2-line delegating term.

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                              | Hit? | Standard form found | Notes |
|----|----------------------------------|----------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "if nP is integral then P is integral" division polynomial monic argument Nagell-Lutz proof        | yes  | proof-internal step in NL | Alpoge "Nagell-Lutz, quickly" (Harvard); arXiv 1108.3051 (valuations of div polys) |
|  2 | WebSearch (general / theorem)    | Nagell-Lutz theorem proof torsion point integral coordinates elliptic curve division polynomial    | yes  | NL: nontrivial torsion ⇒ integral coords; `[n]P=(φₙ/ψₙ²,…)` | Wikipedia; Silverman AEC VIII.7.1; Washington; Milne; Michigan/UChicago REU notes |
|  3 | WebSearch (Lean / mathlib)       | mathlib Nagell-Lutz theorem formalization elliptic curve torsion Lean                               | no   | — | no NL formalization in mathlib surfaced — confirms not upstream |
|  4 | ChatGPT MCP                      | (standard-form recognisability + general-vs-specialised upstreaming judgment)                       | n/a  | — | **Codex backend errored this session** (documented; task warned MCP may be down) — compensated by Wikipedia/Silverman + MathOverflow rows 2,9 |
|  5 | Local references                 | `refs/NagellLutz/` symlink absent; `.mathlib-quality/references/` absent                            | n/a  | — | references dir absent — recorded n/a |
|  6 | nLab                             | "Nagell-Lutz theorem" / "division polynomial"                                                       | partial | — | no dedicated NL / x-descent entry; concept is arithmetic-geometry, not nLab |
|  7 | nCatLab (categorical)            | —                                                                                                  | n/a  | — | not a categorical concept (concrete Diophantine integrality) |
|  8 | Stacks Project (alg geom)        | division polynomial / torsion integrality                                                           | n/a  | — | Stacks has no EC division-polynomial / NL material |
|  9 | MathOverflow / Math.SE           | Nagell-Lutz integrality via division polynomials; "x(nP) integral ⇒ x(P) integral"                 | yes  | proof-internal step | treated as a lemma *inside* NL proofs; not given a standalone name |
| 10 | recent arXiv (last 5 yrs)        | Nagell-Lutz imaginary quadratic / integral points + valuations of division polynomials             | yes  | NL generalised to number fields | arXiv 2509.07524, 1108.3051 — the result *generalised* is NL itself; x-descent stays internal |

Protocol passed: 3 WebSearch queries at different generality levels (specific x-descent / NL theorem / Lean angle); ChatGPT MCP attempted but the Codex backend errored (documented, compensated by Silverman + MathOverflow cross-checks); local refs / nLab / nCatLab / Stacks / MathOverflow / arXiv each checked or `n/a` with reason.

### Literature summary (Phase 3)

Concept identified as: the **x-coordinate integral-descent step of Nagell–Lutz**, via the **division-polynomial + monic / rational-root** argument.
Sources agree on the standard form: **yes** — every reference packages this as a *step inside* the NL proof; the standalone named result is the **Nagell–Lutz theorem** (Silverman AEC VIII.7.1), not the x-descent lemma. (Silverman's own proof routes through formal groups / p-adic valuations; the division-polynomial route used here is the Washington/"quickly" presentation.)
Most general standard form: over any integrally-closed / UFD base where the rational-root argument runs; the project's UFD form `PID.x_isInteger_of_nsmul_x_isInteger` (arbitrary UFD `R`, `K = Frac(R)`, `IsLocalization.IsInteger`) is at or above the literature's working generality.
Generality dimensions where literature varies: base ring ℤ (classical NL) → ring of integers of a number field (arXiv 2509.07524) → general UFD/Dedekind domain. Most general usable = **UFD with fraction field** = exactly the PID-track form.
Disagreement with the literature: none. Only the *packaging* (standalone named lemma vs. internal step) differs, and the literature treats it as an internal step.

### Generality analysis — `x_integral_of_nsmul_x_integral_general`

Literature-standard form (Phase 3): the x-descent over a general UFD/Dedekind base — exactly `PID.x_isInteger_of_nsmul_x_isInteger`, which this lemma is the `R=ℤ, K=ℚ` specialisation of.

| # | Parameter / hypothesis        | Current Lean form                    | Literature-standard form                  | Weaker form exists? | Reason |
|---|-------------------------------|--------------------------------------|-------------------------------------------|---------------------|--------|
| 1 | base ring fixed to `ℤ`        | `W : WeierstrassCurve ℤ`             | arbitrary UFD `R`                          | **yes — already realised** | `PID.x_isInteger_of_nsmul_x_isInteger` (`PIDIntegralMultiple.lean:65`) over `[CommRing R][IsDomain R][UniqueFactorizationMonoid R]`. This ℤ lemma is a strict specialisation of it. |
| 2 | fraction field fixed to `ℚ`  | `x y x' y' : ℚ`                       | `K = Frac(R)` (`IsFractionRing R K`)       | **yes — already realised** | the PID form abstracts ℚ to any fraction field. |
| 3 | integrality `∃ x₀:ℤ,(x₀:ℚ)=x` | concrete `∃`                         | `IsLocalization.IsInteger R x`             | **yes — re-phrasing** | the PID form uses mathlib's `IsLocalization.IsInteger`; this lemma unfolds it to the concrete `∃` purely for the `GeneralMain`/`GeneralDiscriminant` consumers (`isInteger_int_iff`). |
| 4 | model generality              | general Weierstrass `a₁..a₆`         | general                                    | NO (already general) | correct as-is. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** — by the file's own admission it is the `ℤ/ℚ` specialisation of the genuinely-general `PID.x_isInteger_of_nsmul_x_isInteger`.
Number of weakening opportunities: 3 (base ring, fraction field, integrality predicate) — **all already realised in the project's own PID track.**
Proposed restatement: the general form already exists as `LutzNagell.PID.x_isInteger_of_nsmul_x_isInteger`. This is not "generalise the proof"; it is "the general lemma already exists and this is its specialisation wrapper".
Cost of restatement: **n/a — already done.**

### Modern-idiom check (Phase 4c)

| #  | Question                                                       | Applies? | Proposed reformulation | Mathlib downstream |
|----|----------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | preambles → typeclasses/instances?                             | no       | — | already typeclass-driven (`WeierstrassCurve`, `IsFractionRing`) |
|  2 | sequences/metric → filters/topological?                        | no       | — | purely algebraic; no analysis |
|  3 | construct object → universal-property class?                   | no       | — | a proposition, not a construction |
|  4 | set+closure-predicate → bundled substructure?                  | no       | — | n/a |
|  5 | vector-space/field-specific → weaken typeclasses?              | **yes**  | the UFD form already does it (ℤ→UFD, ℚ→Frac, concrete-∃ → `IsLocalization.IsInteger`) | full `IsLocalization` API; reuse over rings of integers |
|  6 | 1-categorical → higher-categorical?                            | no       | — | not categorical |
|  7 | concrete index (ℤ,ℚ) → arbitrary structure?                    | **yes**  | identical to the PID generalisation (this IS the concrete ℤ/ℚ index the PID form abstracts) | unifies with arbitrary-UFD EC integrality |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** — and already realised as `PID.x_isInteger_of_nsmul_x_isInteger` (the `IsLocalization.IsInteger`-over-UFD form). The ℤ/ℚ lemma is the *narrow* shadow; the modern/general idiom is the PID one.
  - Cost: n/a (the general form exists).
  - Real improvement: the general form is reusable over rings of integers of number fields (the active NL generalisation direction, arXiv 2509.07524); the ℤ/ℚ form is not.

### Diamond / defeq risk — (Phase 4.5)

n/a — declaration kind is `theorem`.

### Mathlib search-status: `x_integral_of_nsmul_x_integral_general`

[A] Lean-Finder       index MCP unavailable this session                      n/a — substituted by [D]/[E] grep on the pinned tree
[B] Loogle            index MCP unavailable this session                      n/a — grep substitute
[C] LeanSearch        index MCP unavailable this session                      n/a — grep substitute
[D] Grep mathlib src  `Nagell`, `LutzNagell`, `x_isInteger_of_nsmul`, `x_integral_of_nsmul`, `IsInteger` in `NumberTheory/` + `AlgebraicGeometry/EllipticCurve/`  **no hits** for any integral-multiple / NL / torsion-integrality lemma (0 matches for "nagell" repo-wide in mathlib)
[E] Name pattern      `nsmul_x_integral`, `integral_of_nsmul`                  no hits in mathlib

Searched for both:
  - the user's ℤ/ℚ form — **absent**.
  - the literature-standard UFD form (`PID.x_isInteger_of_nsmul_x_isInteger`) — **also absent** from mathlib.

Building blocks that ARE in mathlib (the proof's primitives, confirmed by grep on `.lake/packages/mathlib`):
  - `isInteger_of_is_root_of_monic` — `Mathlib/RingTheory/Polynomial/RationalRoot.lean:115` (the integrality engine).
  - `WeierstrassCurve.Φ` (`.../DivisionPolynomial/Basic.lean:349`), `WeierstrassCurve.ΨSq` (`Basic.lean:242`), with `natDegree_Φ`, `leadingCoeff_Φ`, `natDegree_ΨSq` (`.../DivisionPolynomial/Degree.lean`).
  - `Polynomial.Monic.sub_of_left`, `IsLocalization.IsInteger` (`Mathlib/RingTheory/Localization/Integer.lean:45`).

Concluded: **not in mathlib** (both the ℤ/ℚ form and the general UFD form). Mathlib has the *primitives* but **no** "n•P integral ⇒ P integral" / Nagell-Lutz result, and no NL formalization at all. Crucially mathlib also lacks the **coordinate identity** `x(nP)=Φₙ(x)/Ψₙ²(x)` for the group law — the genuinely novel project mathematics (`PID.x_coord_nsmul_eq`).

### Call sites — `x_integral_of_nsmul_x_integral_general`

Internal use count: **K = 0** (no caller anywhere in the repo outside the declaring file).
External-to-file callers: 0.

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none)           | —             |

Repo-wide grep for the name `x_integral_of_nsmul_x_integral_general` across `projects/**/*.lean`: **exactly one hit — its own declaration at GeneralIntegralMultiple.lean:66.** No `.lean`, blueprint, or docs reference elsewhere.

Inline-derivation grep: the *adjacent* main wrapper `integral_of_nsmul_integral_general` (same file, line 82 — the one actually consumed by `GeneralMain.lean:74,102`) does **not** call this x-only lemma; it calls `PID.isInteger_of_nsmul_isInteger` directly (line 89). So even the file's own bundled result bypasses this x-coordinate fragment.

Signal (per the call-sites table): `K = 0` internal uses AND the sibling that would naturally use it re-derives via the PID layer → **strong NO-composable / redundant-dead-wrapper signal.** This corrects the earlier draft's erroneous "K=1, internal step the next theorem uses".

### Composition check (Phase 6)

Can `x_integral_of_nsmul_x_integral_general` be derived from mathlib in ≤3 chained calls?

Attempt 1 (from **mathlib** alone): `isInteger_of_is_root_of_monic <monic> <root>`.
  - Mathlib decls used: `isInteger_of_is_root_of_monic`.
  - Result: **fails as a ≤3 mathlib-call composition** — the call needs two non-trivial inputs mathlib does not supply: (a) monicity of `Φₙ − C c·Ψₙ²` (a degree argument — project lemma `monic_Φ_sub_smul_ΨSq`, though built on mathlib's `natDegree_Φ`/`leadingCoeff_Φ`/`natDegree_ΨSq`); and (b) `aeval x (Φₙ − C c·Ψₙ²) = 0`, which comes from the project coordinate identity `x_coord_nsmul_eq` (`x'·Ψₙ²(x)=Φₙ(x)`) — itself a ~25-line proof via the Jacobian/affine bridge that mathlib does **not** have.
  - Notes: the genuine content (the coordinate identity) is not a mathlib one-liner.

Attempt 2 (from the **project's own general lemma**): the actual body is `isInteger_int_iff.mp (PID.x_isInteger_of_nsmul_x_isInteger W hns hn (by exact_mod_cast hn) hns' hnP (by simpa … using hc))` — **one call** to `PID.x_isInteger_of_nsmul_x_isInteger` + the defeq bridge `isInteger_int_iff`.

Conclusion: **NOT-COMPOSABLE-FROM-MATHLIB** (mathlib lacks the coordinate identity, so neither this nor the general form composes from mathlib primitives). But *within the project* it is a 1-call specialisation of `PID.x_isInteger_of_nsmul_x_isInteger`. The real mathematical content lives in that general lemma + `PID.x_coord_nsmul_eq`; **this ℤ/ℚ lemma is a thin specialisation shadow.**

## Verdict: `LutzNagell.LutzNagellTheorem.x_integral_of_nsmul_x_integral_general`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the x-descent integrality step is a *proof-internal* lemma of Nagell–Lutz, standard but not separately named (the named result is the NL theorem, Silverman AEC VIII.7.1). Most general usable form = UFD base, which the project already has.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — this is the `ℤ/ℚ` specialisation of `PID.x_isInteger_of_nsmul_x_isInteger`; all 3 weakenings already realised in-project.
- Mathlib search (Phase 5): **not in mathlib** (neither this nor the general form; mathlib has no NL integrality result and lacks even the coordinate identity).
- Composition check (Phase 6): **NOT-COMPOSABLE from mathlib**, but **a 1-call specialisation of the project's own general lemma** `PID.x_isInteger_of_nsmul_x_isInteger`.

**Rationale:**

The mathematical engine belongs to the *general* lemma `PID.x_isInteger_of_nsmul_x_isInteger`, not to this ℤ/ℚ wrapper. By the file's own docstrings (lines 17–23, 63–65) this declaration is nothing more than the `R = ℤ, K = ℚ` instantiation of that UFD lemma, with `IsLocalization.IsInteger ℤ x` unfolded to the concrete `∃ x₀:ℤ,(x₀:ℚ)=x` for downstream convenience; its entire body is a single application of the general lemma plus the defeq bridge `isInteger_int_iff`. A ℤ/ℚ specialisation of a general result is exactly what mathlib does *not* duplicate (the modules-not-vector-spaces rule): if anything in this track is ever upstreamed, the unit is the general `PID` lemma, never this shadow. The bucket is `NO-composable-from-mathlib` rather than `NO-mathlib-has-it` only because mathlib does not have the general lemma either — it lacks the division-polynomial coordinate identity for the group law, which is the genuinely novel project mathematics.

The call-sites evidence makes the disposition unambiguous and corrects the earlier draft: this lemma has **zero** consumers anywhere in the repo (the only occurrence of its name is its own declaration), and even the file's own bundled `integral_of_nsmul_integral_general` — the one the real consumers in `GeneralMain.lean` use — bypasses it by calling `PID.isInteger_of_nsmul_isInteger` directly. So it is a **dead specialisation wrapper**: not a mathlib addition, and within the project either keep-as-API or inline. (Note: this verdict is driven by the dependency structure + dead-wrapper status, not by any "too expensive to generalise" cost argument — the general form already exists, so cost is moot.)

**WHY not (refactor-actionable):**
Mathlib has the *building blocks* — `isInteger_of_is_root_of_monic` (`RationalRoot.lean:115`), the division-polynomial degree/leading-coeff API (`natDegree_Φ`, `leadingCoeff_Φ`, `natDegree_ΨSq`), `Monic.sub_of_left` — but not this form, because the missing piece is the project-internal coordinate identity. Within the project, the form is a 1-call specialisation of `PID.x_isInteger_of_nsmul_x_isInteger`.

Mathlib building blocks: `isInteger_of_is_root_of_monic` (`Mathlib/RingTheory/Polynomial/RationalRoot.lean:115`); `WeierstrassCurve.natDegree_Φ`, `leadingCoeff_Φ`, `natDegree_ΨSq` (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`); `Polynomial.Monic.sub_of_left`. **Plus the project lemma** `LutzNagell.PID.x_isInteger_of_nsmul_x_isInteger` (`PIDIntegralMultiple.lean:65`) — the real composition target.

Composition sketch (≤3 lines; this is literally the existing body):
```lean
example … : ∃ x₀ : ℤ, (x₀ : ℚ) = x :=
  isInteger_int_iff.mp <| PID.x_isInteger_of_nsmul_x_isInteger W hns hn
    (by exact_mod_cast hn) hns' hnP (by simpa … using hc)
```

Call sites in our project (from Phase 6.0): **K = 0.**

Refactor plan (a *consolidation* call, not a mathlib-PR call — because K = 0 the lemma is currently dead):
  1. **Keep as-is** *iff* it is intentionally part of the project's published ℤ/ℚ API surface (the docstring frames the `*_general` trio as the concrete interface for `GeneralMain`/`GeneralDiscriminant`), accepting that the x-only fragment is presently unused while the bundled sibling is the one consumed.
  2. **Inline / delete** if minimalism is preferred: a future consumer wanting just the x-descent can write `isInteger_int_iff.mp (PID.x_isInteger_of_nsmul_x_isInteger …)` directly (the 3-line composition above); the wrapper carries no mathematical weight. There are zero call sites to update.

Either way it does **not** go to mathlib. If any decl from this track is ever upstreamed, it is the *general* `PID.x_isInteger_of_nsmul_x_isInteger` together with the coordinate identity `PID.x_coord_nsmul_eq` (the whole Nagell–Lutz division-polynomial integrality API) — a separate, larger judgment to be assessed on the PID lemma, not on this ℤ/ℚ shadow.

Next action: do **not** PR this to mathlib. Treat it as a project specialisation wrapper; for consolidation decide keep-vs-inline given K = 0. To assess this *track* for mathlib, re-run `/mathlibable LutzNagell.PID.x_isInteger_of_nsmul_x_isInteger` (and `PID.x_coord_nsmul_eq`), which hold the actual novel content.

---

## Next step

Do not submit this declaration to mathlib. It is the ℤ/ℚ specialisation of the project's own general lemma `LutzNagell.PID.x_isInteger_of_nsmul_x_isInteger` and has **zero** call sites (a dead wrapper; even the file's bundled sibling bypasses it). Mathlib lacks the underlying division-polynomial coordinate identity (so the *general* lemma is genuinely novel), but a ℤ/ℚ specialisation is never the upstreaming unit. For consolidation: decide keep-as-API vs. inline given K = 0. To assess this track for mathlib, run `/mathlibable LutzNagell.PID.x_isInteger_of_nsmul_x_isInteger`.
