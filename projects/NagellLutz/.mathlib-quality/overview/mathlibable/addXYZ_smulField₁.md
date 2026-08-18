# /mathlibable report — `WeierstrassCurve.Universal.Jacobian.addXYZ_smulField₁`

### Baseline (Phase 0)
- lake build:               (not re-run; local build stale per task note — reasoning from source)
- decl `WeierstrassCurve.Universal.Jacobian.addXYZ_smulField₁`: ✓ resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:530`
- qualified name:           `WeierstrassCurve.Universal.Jacobian.addXYZ_smulField₁` (namespaces `WeierstrassCurve` (l.76) → `Universal` (l.86) → `Jacobian` (l.395); lemma at l.530). **Matches the parsed name in the task.**
- kind:                     lemma  (⇒ Phase 4.5 diamond/defeq risk is **n/a**)
- has sorry:                no
- module docstring summary: This file proves `WeierstrassCurve.zsmul_eq_smulEval`: in Jacobian coordinates `n • P = (φₙ(x,y) : ωₙ(x,y) : ψₙ(x,y))` for any integer `n` and any nonsingular affine point `P=(x,y)` on a Weierstrass curve over a field. `addXYZ_smulField₁` is one of the internal universal-field identities that the even-odd induction reduces to (odd step).

### Statement (Phase 1)

```
lemma addXYZ_smulField₁ :
    addXYZ curveField (smulField n) (smulField (n + 1)) = smulField (2 * n + 1)
```

In words: **the consecutive-index (odd-step) case of the division-polynomial addition formula in Jacobian coordinates over the universal field.** On the universal Weierstrass curve over `Universal.Field = Frac(ℤ[A₁,A₂,A₃,A₄,A₆,X,Y]/⟨P_Weierstrass⟩)`, applying mathlib's Jacobian group-law addition formula `addXYZ` to the division-polynomial coordinate triples
`smulField n = polyToField ∘ ![φₙ, ωₙ, ψₙ]` (the Jacobian coordinates of `n • point`) and
`smulField (n+1) = polyToField ∘ ![φₙ₊₁, ωₙ₊₁, ψₙ₊₁]`
yields **exactly** `smulField (2n+1) = polyToField ∘ ![φ_{2n+1}, ω_{2n+1}, ψ_{2n+1}]` — with **no scaling factor**, because the general scaling factor `ψ_{(n+1)−n} = ψ_1 = 1`.

It is the `m = n`, `n ↦ n+1` specialisation of the parent lemma
`addXYZ_smulField : addXYZ curveField (smulField m) (smulField n) = polyToField (curve.ψ (n−m)) • smulField (n+m)` (l.499),
where the `ψ_{n−m}` "projective-coordinate fudge factor" collapses to `1`.

Proof (5 lines, l.532–535): `rw [addXYZ_smulField, add_sub_cancel_left, ψ_one, map_one, <1•_ = _ simp>]; congr 1; omega`.
i.e. invoke the parent, simplify the index `(n+1)−n = 1`, use `ψ_one : ψ 1 = 1` and `map_one`, drop the `1 • _` scaling, then reconcile `n+1+n = 2n+1` by `omega`.

Variables / objects involved (all **project-defined**, none in mathlib):
- `n : ℤ` (implicit section variable).
- Global universal objects: `curve` (universal Weierstrass curve over `MvPolynomial Coeff ℤ`), `curveField = baseChange curve Universal.Field`, `Universal.Field`/`Ring`/`Poly`, `polyToField : Poly →+* Universal.Field`, `smulField : ℤ → (Fin 3 → Universal.Field)`, `curve.ψ : ℤ → Poly` (the EDS / division-polynomial family).
- Only **`addXYZ`** itself is from mathlib (`Jacobian/Formula.lean:661`), as is the scaling lemma `addXYZ_smul` (`Formula.lean:673`) that the *parent* proof uses.

Hypotheses: none (universal identity).

### Size classification (Phase 2a)

Verdict: **BIG** (literature width set to EXHAUSTIVE regardless).
Reason: although the lemma *itself* is a 5-line specialisation, it is a named step of a project **main result** (`zsmul_eq_smulEval`, the division-polynomial multiplication formula), and the underlying concept (division polynomials / EDS / multiplication-by-n map) is classical and named-after (Ward 1948; Silverman). Treated as BIG to force the wide literature sweep. (Reused the EXHAUSTIVE sweep already performed for the parent `addXYZ_smulField` — same mathematical object.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → one-liner check is **n/a**. (Proof is a 5-line specialisation; not an `abbrev` wrapper.)

---

### Literature search table — EXHAUSTIVE protocol

Same mathematical object as the parent `addXYZ_smulField` (this is its `ψ_1 = 1` corollary); the full EXHAUSTIVE table is in `addXYZ_smulField.md` (Phases 1–10). Re-confirmed the load-bearing channels here:

| #  | Channel                       | Query                                                                                                  | Hit? | Standard form found | Notes |
|----|-------------------------------|--------------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)     | "division polynomials elliptic curve multiplication by n point coordinates Jacobian psi phi omega Silverman" | yes (affine) | `[n]P = (φₙ/ψₙ², ωₙ/ψₙ³)` | MIT 18.783 notes, Wikipedia "Division polynomials", Silverman *AEC*. The affine multiplication formula is standard; the **Jacobian triple `(φₙ:ωₙ:ψₙ)`** and the *consecutive-index addZ identity* are formalization-native. |
|  2 | WebSearch (EDS / named-after) | "elliptic divisibility sequence addition formula ψ(n+m)ψ(n−m) division polynomial multiplication-by-n point" | yes | EDS addition recurrence `u_{m+n}u_{m−n} = u_{m+1}u_{m−1}uₙ² − u_{n+1}u_{n−1}uₘ²` | Ward 1948; Silverman *AEC* Exercise 3.7. The `addZ_smulPoly`/`isEllSequence_ψ` (ZSMul.lean l.475–478) Z-coordinate identity is the EDS addition law; the `n+1,n` case is exactly the **odd step** of even-odd induction. |
|  3 | WebSearch (Lean / mathlib)    | "mathlib elliptic curve division polynomials Nagell-Lutz n • P formula zsmul division polynomial" (Junyan Xu) | partial | mathlib `DivisionPolynomial.Basic` defines the polys; Angdinata–Xu ITP 2023 builds the Jacobian group law | mathlib has the polynomials and the group law but **not** the bridge `n•P = (φₙ:ωₙ:ψₙ)`. This project fills exactly that gap; same author as mathlib's group-law file. |
|  4 | ChatGPT MCP                   | (MCP down per task note — substituted by direct mathlib-source inspection + Wikipedia "Division polynomials") | yes | confirms affine `[n]P = (φₙ/ψₙ², ωₙ/ψₙ³)`; no explicit Jacobian-triple form | The Jacobian `(X:Y:Z)=(φₙ:ωₙ:ψₙ)` and its consecutive-index addition identity are not literature objects. |
|  5 | Local references              | `ls projects/NagellLutz/.mathlib-quality/references/`                                                   | n/a  | directory absent    | No project refs dir. Recorded n/a. |
| 6–10 | nLab / Stacks / MO / arXiv  | "division polynomial", "elliptic divisibility sequence"                                                 | n/a / yes | classical arithmetic-geometry; modern arXiv generalises the *model* (genus-2/Mumford), not the Weierstrass Jacobian coordinate system | No dedicated nLab/Stacks page; concept is classical. (Full detail in `addXYZ_smulField.md` table.) |

### Literature summary (Phase 3)

Concept: **the multiplication-by-n map / division-polynomial coordinates of `n·P`** (equivalently the **EDS addition formula**; Ward 1948; Silverman *Arithmetic of Elliptic Curves*, Exercise 3.7). Standard *affine* form `[n]P = (φₙ(x)/ψₙ², ωₙ(x,y)/ψₙ³)` is agreed across all sources.

`addXYZ_smulField₁` is **not a textbook-named lemma**. It is a formalization-internal corollary: the **odd step** of the even-odd induction proving the multiplication formula — "`addXYZ` applied to the coordinates of `n•P` and `(n+1)•P` gives the coordinates of `(2n+1)•P`, on the nose". The "on the nose" (no `ψ` scaling) is precisely the `ψ_1 = 1` specialisation of the parent's `ψ_{n−m}` factor. There is **no mathlib counterpart** and no literature object at this granularity.

---

### Generality analysis (Phase 4)

- **Phase 4a (curve/coefficient generality):** MAXIMALLY GENERAL. The statement is over the *universal* curve `curveField` (`Frac(ℤ[A₁..A₆,X,Y]/⟨P⟩)`); any Weierstrass curve over any commutative ring/field is a base-change of it, so a single universal identity specialises to every curve (this is the whole point of the `Universal` apparatus, docstring l.41–56). No assumption can be weakened — there are no hypotheses, `n` ranges over all of `ℤ`.
- **Phase 4b (statement-shape generality):** the parent `addXYZ_smulField` (general `m, n`) is *strictly more general* — `addXYZ_smulField₁` is its `m = n, n ↦ n+1` instance. So at the lemma level this is a **specialisation**, not a maximally-general statement. The genuinely-general carriers in this development are: the parent `addXYZ_smulField` (field), `addXYZ_smulRing` (ring — the more primitive, since the field version is derived from it via `IsFractionRing.injective`), and the curve-level export `addXYZ_smulEval₁` / `zsmul_eq_smulEval`.
- **Phase 4c (right granularity — the open question):** the consumer-facing public unit of an upstreamed development is the curve-level `smulEval` / `zsmul_eq_smulEval` results (ZSMul.lean l.551–625), with the universal `…Field`/`…Ring` identities as the *proof engine*. Whether this **field-level consecutive-index corollary** should even exist as a named lemma upstream — versus being inlined, made `private`, or replaced by the `Ring` twin — is the granularity decision. Notably the field version `addXYZ_smulField₁` is **unused in-file** (inventory l.873): the load-bearing one downstream is the **ring** twin `addXYZ_smulRing₁` (→ `addXYZ_smulEval₁` → `zsmul_eq_smulEval`). So `addXYZ_smulField₁` is a *parallel-track symmetry lemma*, not a consumer.

### Mathlib search (Phase 5) — five methods

1. **Exact-name / leansearch / loogle (mathlib index):** no `smulField`, `smulPoly`, `smulRing`, `smulEval`, `addXYZ_smulField`, `addXYZ_smulField₁`, or `zsmul_eq_smulEval` in mathlib. (Index live per task note; concept absent.)
2. **Grep pinned mathlib (`.lake/packages/mathlib`, rev d90090f / `v4.32.0-rc1`):**
   - `grep -rn "smulField\|addXYZ_smul\|smulEval\|smulPoly\|smulRing"` → hits **only** in `Jacobian/Point.lean` and `Jacobian/Formula.lean`, and those are the **generic scaling-equivariance** lemmas `addXYZ_smul`, `dblXYZ_smul`, `add_smul_of_equiv/not_equiv`, `add_smul_equiv`, `smul_eq`, `toAffine_smul` (how `addXYZ` transforms under `u • P` rescaling). **None** is `smulField`/`addXYZ_smulField`.
   - `addXYZ` itself: `Jacobian/Formula.lean:661` (`noncomputable def addXYZ`); `addXYZ_smul` at l.673. ← these are what the *parent* proof uses.
3. **`Universal` curve construction:** `grep -rln "Universal.Field\|namespace Universal\|polyToField\|def curveField"` over `Mathlib/` → **no** division-polynomial `Universal` apparatus (only unrelated `UniversallyOpen`, `UniversalEnveloping`). The `Universal.Ring = CoordinateRing`, `Universal.Field = FractionRing`, `polyToField`, `curveField` machinery (project `Universal.lean` l.96–233) is entirely project-local.
4. **`DivisionPolynomial` dir:** mathlib ships only `DivisionPolynomial/Basic.lean` + `Degree.lean` — the polynomials `ψ, φ, ω` and their degrees, **no** connection to point multiples, **no** Jacobian-coordinate bridge.
5. **`EllipticDivisibilitySequence.lean`:** only the abstract EDS recurrence (`IsEllSequence`, `IsDivSequence`, `IsEllDivSequence`, and `IsEllSequence.smul` — scaling a *sequence* `ℤ→R`, not a point). **No** point-multiple / coordinate content.

**Conclusion (Phase 5): NOT in mathlib.** mathlib has every *building block* (`addXYZ`, `addXYZ_smul`, the division polynomials, `IsEllSequence`) but neither the `smul*` coordinate API nor the `n•P = (φₙ:ωₙ:ψₙ)` bridge — and `addXYZ_smulField₁` depends on the project's `smulField`/`Universal` apparatus.

### Composition check (Phase 6)

Can `addXYZ_smulField₁` be derived from **mathlib** in ≤3 chained calls?

- **From mathlib alone: NO.** The lemma references `smulField`/`curveField`/`curve.ψ`/`polyToField`, none of which exist in mathlib; even stating it requires the project's universal apparatus. Its proof depends entirely on the parent `addXYZ_smulField` (not in mathlib) plus the project's `ψ_one`.
- **From the project's own parent: YES, trivially (≤3 calls).** It is literally `addXYZ_smulField` (1 call) + `ψ_one`/`map_one` simp + `omega`. This is the relevant *intra-project* composability signal: `addXYZ_smulField₁` adds essentially **zero new mathematical content** over `addXYZ_smulField` — it only discharges the `ψ_1 = 1` and `n+1+n = 2n+1` bookkeeping.
- **Cross-project duplication:** the lemma (and its parent, and `addXYZ_smulRing`/`addXYZ_smulRing₁`) is **duplicated verbatim** in HasseWeil (`projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:604`, parent at l.573). Same statement, same proof body. This is the strongest "should be one shared copy, ideally upstream" signal.

**Conclusion:** NOT-COMPOSABLE-FROM-MATHLIB (it needs the whole `Universal`/`smul*` API), but TRIVIALLY-COMPOSABLE-FROM-ITS-OWN-PARENT (a 5-line `ψ_1=1` corollary). Therefore it is **not** independent new content — it is a thin specialisation of `addXYZ_smulField`, whose mathlib fate it shares.

---

## Verdict: `WeierstrassCurve.Universal.Jacobian.addXYZ_smulField₁`

**Category:** BORDERLINE-needs-human

**Evidence:**
- Literature (Phase 3): the *mathematics* (division-polynomial / EDS multiplication formula; odd-step addition identity) is classical (Ward, Silverman). The *Jacobian-coordinate universal-field consecutive-index form* is formalization-native, not a literature object. NOT in mathlib.
- Generality (Phase 4): MAXIMALLY GENERAL in curve/coefficient (universal curve), but a **specialisation** of the parent `addXYZ_smulField` at the statement level; the field version is moreover **unused in-file** (the Ring twin `addXYZ_smulRing₁` is the downstream carrier). The open question is upstream **granularity**, not weakening hypotheses.
- Mathlib search (Phase 5): NOT in mathlib; all building blocks present (`addXYZ`, `addXYZ_smul`, `DivisionPolynomial.Basic`, `IsEllSequence`), but no `smul*` coordinate API and no `n•P = (φₙ:ωₙ:ψₙ)` bridge.
- Composition (Phase 6): NOT-composable-from-mathlib (needs the `Universal`/`smul*` apparatus); trivially-composable-from-its-own-parent (a `ψ_1=1` corollary, ≤3 calls). Verbatim-duplicated in HasseWeil.

**Rationale:**

The result belongs to a development that is clearly mathlib-*worthy in spirit*: the missing bridge between mathlib's `DivisionPolynomial/Basic` (the polynomials) and mathlib's Jacobian group law (Angdinata–Xu, ITP 2023), establishing the textbook fact that `n • P` is computed by division-polynomial coordinates — headlined by `zsmul_eq_smulEval`, with no mathlib counterpart, written by the same author who built mathlib's group-law file, and **already duplicated across two AINTLIB projects** (NagellLutz + HasseWeil carry verbatim copies).

But `addXYZ_smulField₁` *specifically* is the wrong unit to decide alone, for two compounding reasons:
1. **It is a thin specialisation** (a `ψ_1 = 1`, `omega` corollary of `addXYZ_smulField`) that is **unused in its own file** — the load-bearing consecutive-index lemma downstream is the **ring** twin `addXYZ_smulRing₁`. So whether the *field* consecutive-index lemma should be a named public lemma, a `private` helper, or simply not exist upstream (with only `addXYZ_smulRing₁` + the curve-level `addXYZ_smulEval₁` exported) is a packaging-granularity decision.
2. **Its fate is bound to the parent's.** This lemma cannot sensibly be upstreamed in isolation; it ships (or doesn't) **together with** `addXYZ_smulField`, `dblXYZ_smulField`, `addXYZ_smulRing(₁)`, the whole `smul*` family, and the curve-level `…Eval` / `zsmul_eq_smulEval` results — as **one PR**, with one consistent public-API granularity choice. The sibling assessment for the parent (`addXYZ_smulField.md`) reached BORDERLINE on exactly this packaging question; this corollary inherits that verdict.

This is **not** a cost-driven downgrade (regeneralisation/repackaging is CHEAP — every proof already exists). It is genuinely "the right unit and the right public-API granularity for upstreaming need a maintainer call", which is what BORDERLINE-needs-human is for. Independently of the upstream decision, the **cross-project verbatim duplication (NagellLutz ↔ HasseWeil) must be de-duplicated into an AINTLIB `Common/` module** (a cleanup ticket), regardless of upstreaming.

**Numbered questions (≤5):**
  1. Should the upstream unit be the **whole** division-polynomial↔Jacobian bridge (`smulPoly/Ring/Field`, `dblXYZ_smul*`, `addXYZ_smul*` incl. the `…₁` consecutive-index lemmas, `…Eval`, `zsmul_eq_smulEval`) as a single new file (e.g. `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Jacobian.lean`)? (yes/no)
  2. If yes, should the **field** consecutive-index lemma `addXYZ_smulField₁` be a **public named lemma** at all, given it is unused in-file and the **ring** twin `addXYZ_smulRing₁` is the downstream carrier? (public / private / drop-and-keep-only-Ring)
  3. Is the **ring** identity (`addXYZ_smulRing₁`, hence `addXYZ_smulRing`) the intended *primary* statement, with the field version a derived/section helper? (yes/no)
  4. The lemma (and its parent + ring twins) is **duplicated verbatim in HasseWeil** (`Auxiliary/DivisionPolynomial.lean:604`). Regardless of upstreaming, de-duplicate into an AINTLIB `Common/` module first (a cleanup ticket)? (yes/no)
  5. The project **forks** mathlib's `EllipticDivisibilitySequence` + `DivisionPolynomial`. Must that fork be reconciled with mathlib before upstreaming, and is that a blocker or a parallel track? (blocker / parallel)

**Next action:** decide questions 1–5 together with the parent `addXYZ_smulField` (do not upstream this corollary in isolation). If the family is upstreamed with the **Ring** track as primary, `addXYZ_smulField₁` most likely becomes a `private`/section helper or is dropped in favour of `addXYZ_smulRing₁`. Independently, file an AINTLIB cleanup ticket to de-duplicate the NagellLutz/HasseWeil copies into `Common/`.

---

## Next step

Answer questions 1–5 (packaging granularity for the whole `smul*` family + Ring-vs-Field primary form + NagellLutz/HasseWeil dedup + fork reconciliation). The mathematics is mathlib-worthy and NOT in mathlib (the division-polynomial ↔ Jacobian-group-law bridge is a real gap); the open issues for *this* declaration are (i) whether the thin, in-file-unused field consecutive-index corollary should exist as public API upstream at all, decided **together** with its parent and the Ring twin as one PR, and (ii) resolving the verbatim cross-project duplication into a shared `Common/` location.
