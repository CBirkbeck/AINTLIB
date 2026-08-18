# /mathlibable report — `WeierstrassCurve.Universal.Affine.smulX_add`

## Verdict: **BORDERLINE-needs-human**

One-line rationale: an internal EDS-form x-coordinate addition identity on the
universal curve; the math is genuinely missing from mathlib, but shipping *this
exact scaffolding lemma* is a packaging call tied to upstreaming the whole
`Universal` layer (sibling `smulX` landed BORDERLINE for the same reason).

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task; reasoned from source — task-sanctioned)
- decl `WeierstrassCurve.Universal.Affine.smulX_add`: ✓ resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:300`
- kind:                      `lemma` (in `noncomputable section`; `Classical.propDecidable` is a local instance in `namespace Affine`)
- has sorry:                 no
- module docstring summary:  Proves `WeierstrassCurve.zsmul_eq_smulEval`: `n • P = (φₙ : ωₙ : ψₙ)`
  (Jacobian) / `(φₙ/ψₙ², ωₙ/ψₙ³)` (affine) for any integer `n` and nonsingular
  affine point `P` on a Weierstrass curve over a field. The docstring explicitly
  names `smulX_add` as one of the "fancy identities of division polynomials and
  elliptic divisibility sequences" that drive the induction step (line 65).

Qualified name verified from source: namespaces `WeierstrassCurve` (line 76) →
`Universal` (line 86) → `Affine` (line 157, ends line 393); `lemma smulX_add` at
line 300. The parsed name `WeierstrassCurve.Universal.Affine.smulX_add` is
**correct**.

Source (verbatim):
```lean
lemma smulX_add (hm : m ≠ 0) (hn : n ≠ 0) (add_ne : n + m ≠ 0) (sub_ne : n - m ≠ 0) :
    let ψ₂ x y := y - pointedCurve.toAffine.negY x y
    smulX (n + m) = smulX (n - m) -
      ψ₂ (smulX n) (smulY n) * ψ₂ (smulX m) (smulY m) / (smulX m - smulX n) ^ 2 := by
  change smulX (n + m) = smulX (n - m) -
    (smulY n - pointedCurve.toAffine.negY (smulX n) (smulY n)) *
    (smulY m - pointedCurve.toAffine.negY (smulX m) (smulY m)) / (smulX m - smulX n) ^ 2
  rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq']
  calc _ = ψᵤ (2 * n) / ψᵤ n ^ 4 * (ψᵤ (2 * m) / ψᵤ m ^ 4) /
      (ψᵤ (n + m) * ψᵤ (n - m) / (ψᵤ n * ψᵤ m) ^ 2) ^ 2 := by
        rw [smulY_sub_negY hm, smulY_sub_negY hn, smulX_sub_smulX hm hn]
      _ = ψᵤ (2 * n) * ψᵤ (2 * m) / (ψᵤ (n + m) * ψᵤ (n - m)) ^ 2 :=
        smulX_add_aux (ψᵤ_ne_zero hm) (ψᵤ_ne_zero hn)
          (ψᵤ_ne_zero add_ne) (ψᵤ_ne_zero sub_ne)
      _ = smulX (n - m) - smulX (n + m) :=
        (smulX_sub_sub_smulX_add add_ne sub_ne).symm
```

where (all proved earlier in the same file):
- `smulX k = polyToField (curve.φ k) / (ψᵤ k) ^ 2` (line 164) — candidate
  x-coordinate of `k • (X,Y)`,
- `smulY k = polyToField (curve.ω k) / (ψᵤ k) ^ 3` (line 168),
- `ψᵤ k = polyToField (curve.ψ k)` (line 132) — universal n-th division
  polynomial in `Universal.Field`,
- `pointedCurve = curve.baseChange Universal.Field` (Universal.lean) — the
  universal Weierstrass curve over `Universal.Field = Frac(ℤ[A₁..A₆,X,Y]/⟨W⟩)`,
- `ψ₂ x y := y − negY x y = 2y + a₁x + a₃` — the "vertical" 2-torsion form.

---

### Statement (Phase 1)

`smulX_add` is the **x-coordinate addition law on the universal Weierstrass
curve, written in elliptic-divisibility-sequence form**. With the local
abbreviation `ψ₂ x y := y − negY(x,y)` (= `2y + a₁x + a₃`), it asserts, for
nonzero `m, n, n+m, n−m`:

  `x((n+m)·P) = x((n−m)·P) − [ψ₂(x(nP),y(nP)) · ψ₂(x(mP),y(mP))] / (x(mP) − x(nP))²`

where `P = (X,Y)` is the generic point of the universal curve and
`x(kP) = smulX k = φₖ/ψₖ²`, `y(kP) = smulY k = ωₖ/ψₖ³` in `Universal.Field`.

Mathematically this is the classical **chord addition law** `x₃ = λ² − x₁ − x₂`
(here `x(n+m)` and `x(n−m)` are the two collinear sums `x(nP ± mP)`) fused with
the **EDS three-term recurrence** so the difference `x((n−m)P) − x((n+m)P)`
becomes a clean ratio of division polynomials. The proof literally exhibits this:
- `smulY_sub_negY` turns each `ψ₂(kP)` into `ψ(2k)/ψ(k)⁴` (line 310),
- `smulX_sub_smulX` turns `x(mP) − x(nP)` into `ψ(n+m)ψ(n−m)/(ψ(n)ψ(m))²`,
- the algebraic `smulX_add_aux` collapses the compound fraction, and
- `smulX_sub_sub_smulX_add` (line 196) identifies the result with
  `x((n−m)P) − x((n+m)P) = ψ(2n)ψ(2m)/(ψ(n+m)ψ(n−m))²`.

Variables / typeclasses (Lean side):
- `{m n : ℤ}` (ambient, line 97/169) — the two EDS indices.
- Hypotheses: `hm : m ≠ 0`, `hn : n ≠ 0`, `add_ne : n + m ≠ 0`,
  `sub_ne : n − m ≠ 0` (all four denominators must be nonzero so the division
  polynomials `ψ(m), ψ(n), ψ(n+m), ψ(n−m)` are invertible — `ψᵤ_ne_zero`).
- No typeclass parameters of its own: everything is fixed by the ambient
  `Universal` namespace (`curve`, `pointedCurve`, `Universal.Field`, `polyToField`,
  `ψᵤ`, `smulX`, `smulY`). `Universal.Field = Frac(ℤ[A₁..A₆,X,Y]/⟨W⟩)` is the
  single most general base — every Weierstrass curve over every commutative ring
  is a specialization of it.

Conclusion (math): an identity in `Frac(ℤ[A₁..A₆,X,Y]/⟨W⟩)` between the universal
n•P-coordinate rational functions.
Conclusion (Lean): a `Prop` (equality in `Universal.Field`), proved.

---

### Size classification (Phase 2a)

Verdict: **BIG** (as a member of a BIG development).
Reason: the lemma itself is short, but it is a **load-bearing step of a main
result** — `zsmul_eq_smulEval` (named in the module-docstring `## …` summary and
the project plan), explicitly cited at line 65 as one of the three EDS identities
(`smulX_sub_sub_smulX_add`, `smulX_add`, `smulY_add_sub_negY`) that power the
strong-induction proof of `zsmul_point_eq_smulX_smulY`. It sits on top of a
**new mathematical structure** (the universal Weierstrass curve and its function
field) that mathlib lacks. Literature width is EXHAUSTIVE regardless.

### One-line check (Phase 2b)

Body line count: it is a `lemma` (not a `def`), with a ~10-line `calc` proof
(3 substantive rewrite chains). The one-liner/def exemption matrix does **not**
apply to proved propositions; this check is informational. The lemma is *not* a
one-line restatement — it bundles three earlier identities plus a field
computation. (Carried into Phase 7: this is genuine content, not a defeq label.)

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic divisibility sequence addition formula x-coordinate nP mP division polynomial ψ φ Silverman" | yes  | EDS recurrence `ψ_{m+n}ψ_{m−n}ψ_r² = ψ_{m+r}ψ_{m−r}ψ_n² − ψ_{n+r}ψ_{n−r}ψ_m²`; `x(nP)=φₙ/ψₙ² = x − ψ_{n−1}ψ_{n+1}/ψ_n²` | Wikipedia EDS; Au-Yeung (Warwick) CM/EDS intro notes; arXiv:2102.07573. The three-term recurrence and the `φₙ/ψₙ²` coordinate are exactly the ingredients of `smulX_add`. |
|  2 | WebSearch (chord/addition law)   | "elliptic curve x(P+Q) x(P−Q) addition subtraction formula division polynomials universal curve"        | yes  | chord law `x₃ = λ² − x₁ − x₂`, `λ=(y₂−y₁)/(x₂−x₁)` | Stanford pbc explicit-formulae notes; cvut Gollová lecture. The general affine addition x-coordinate; `smulX_add` is this applied to the collinear pair `nP, mP` and rewritten via EDS. |
|  3 | WebFetch (Wikipedia EDS)         | quote the addition theorem relating x((n±m)P) to ψ; the three-term recurrence verbatim                  | yes  | `W_{n+m}W_{n−m}W_r² = W_{n+r}W_{n−r}W_m² − W_{m+r}W_{m−r}W_n²` | Confirmed verbatim. Wikipedia gives the **recurrence** but does **not** state this exact `x((n+m)P)=x((n−m)P)−ψ₂ψ₂/(Δx)²` repackaging — it is a derivation step, not a named theorem. |
|  4 | WebSearch (provenance)           | "Junyan Xu mathlib elliptic curve division polynomial n•P coordinate formula universal curve Nagell-Lutz" | yes  | author = Junyan Xu (`alreadydone`); Alpoge "Nagell-Lutz, quickly" is the math ref | The file author is the **original mathlib EC/division-polynomial author** (Xu+Angdinata, ITP 2023 group law). Strong signal this is upstreaming-track code. The repackaging is a Lean proof-engineering choice, not a literature object. |
|  5 | Local references                 | `.mathlib-quality/references/` present?                                                                  | n/a  | — | NagellLutz has no `references/` dir (only `overview/`); `refs/` symlink absent in this checkout. Recorded n/a. |
|  6 | nLab                             | elliptic curve / EDS / division-polynomial addition                                                     | n/a  | — | nLab treats elliptic curves scheme/moduli-theoretically; the explicit affine EDS addition identity is not an nLab concept. n/a with reason. |
|  7 | nCatLab                          | categorical reformulation of the EDS addition law                                                       | n/a  | — | Not a categorical concept — an identity of rational functions on one curve. n/a. |
|  8 | Stacks Project                   | division polynomials / EDS / explicit point arithmetic                                                  | n/a  | — | Stacks has no elliptic-curve division-polynomial / explicit-arithmetic chapter. n/a with reason. |
|  9 | MathOverflow / MSE               | "x-coordinate of sum of multiples of a point via division polynomials"                                  | yes  | same as #1–2; consistently a derived step | The `φ/ψ²` x-coordinate and the chord law are standard; the precise `smulX_add` shape is universally an intermediate, never elevated to a named result. |
| 10 | recent arXiv (last 5 yrs)        | arXiv:2102.07573 (EDS recurrence), arXiv:2503.15428 (division polys for isogenies), arXiv:1108.3051 (valuations of division polys) | yes  | EDS recurrence + `x(nP)=φₙ/ψₙ²` | Modern treatments reproduce the recurrence and the coordinate formula; none names the `x((n+m)P)=x((n−m)P)−…` repackaging — it is implicit in deriving `x(nP)=φₙ/ψₙ²`. |

### Literature summary (Phase 3)

Concept identified as: **the x-coordinate addition law in EDS form** — the
chord-addition `x₃ = λ² − x₁ − x₂` for the collinear pair `nP, mP`, fused with the
EDS three-term recurrence so that
`x((n−m)P) − x((n+m)P) = ψ(2n)ψ(2m)/(ψ(n+m)ψ(n−m))²`, equivalently the
project's form with `ψ₂(kP) = ψ(2k)/ψ(k)⁴` and `x(mP)−x(nP) = ψ(n+m)ψ(n−m)/(ψ(n)ψ(m))²`.
Sources agree on the **ingredients**: yes (channels 1–3, 9, 10 give the identical
EDS recurrence and `φ/ψ²` coordinate; channel 2 gives the chord law).
Most general standard form: the identity lives over the **universal curve over ℤ**
(initial Weierstrass base) — the project already uses this maximal base.
Disagreement with the literature: **none** mathematically. But the literature
**never names this precise repackaged identity** as a standalone theorem: it is an
unnamed intermediate on the way to `x(nP) = φₙ/ψₙ²`. Its existence as a *separate
lemma* is a Lean proof-architecture decision (the affine strong-induction route),
not a textbook object.

---

### Generality analysis — `WeierstrassCurve.Universal.Affine.smulX_add` (Phase 4)

Literature-standard form (Phase 3): the EDS x-coordinate addition law over any
Weierstrass curve / any base — here over the **universal** curve, which is the
*maximal* base (every other curve is a specialization, recovered by the file's
`ringEval`/`polyEval` specialization maps).

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | base / curve           | `pointedCurve` over `Universal.Field` (universal curve at its generic point) | any Weierstrass curve `W/F`, point `P`, with the relevant `ψ`'s ≠ 0 | NO (already maximal) | The universal curve over `ℤ[A₁..A₆,X,Y]/⟨W⟩` is the **initial** Weierstrass base; the whole point of the `Universal` layer is to prove once and specialize. Cannot be made more general. |
| 2 | indices `m,n`          | `ℤ` | `ℤ` (EDS indices) | no | EDS are ℤ-indexed by definition. Correct index type. |
| 3 | nonvanishing hyps      | `m,n,n+m,n−m ≠ 0` | same (denominators must be invertible) | no | These are exactly the conditions making `ψ(m),ψ(n),ψ(n±m)` invertible (`ψᵤ_ne_zero`); they are necessary, not removable. |
| 4 | coupling to project API| stated via `smulX`,`smulY`,`ψᵤ`,`pointedCurve.negY` | could be stated for an *abstract* EDS `W : ℤ→R` + a chord law | **packaging** | This is the live question (see 4c): the identity could instead be phrased purely on `normEDS`/`net` over an arbitrary ring — but that is a *reformulation/packaging* decision, and it would still need the missing "EDS = point-multiplication coordinates" bridge to be the same theorem. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL on the base** (universal curve = initial
object; nothing to weaken in the curve/field/index/hypothesis axes). The only
"generalisation" available is a **repackaging** (state on an abstract EDS rather
than on the universal n•P coordinates), which is the Phase-4c packaging question,
not an assumption-weakening. → not YES-but-generalise-first on weakening grounds;
the open issue is packaging, which is a human/reviewer call (Phase 7 gate).
Number of *weakening* opportunities found: 0.
Cost of any restatement: would require re-architecting the universal layer (NOT cheap).

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream |
|---|----------|----------|------------------------|--------------------|
| 1 | bundled-hyp → typeclass? | no | the four `≠ 0` hyps are genuine side conditions on the EDS, not a bundleable structure | — |
| 2 | sequences/metric → filters/topology? | no | purely algebraic identity in a field | — |
| 3 | construction → universal-property class? | partial | the *ambient* `Universal` curve **is** a universal-property device already; the lemma is a fact about it, not a construction to re-class | — |
| 4 | set+closure-pred → bundled substructure? | no | not a substructure | — |
| 5 | field/EC-specific → abstract EDS over a ring? | **yes (packaging)** | state the x-addition identity for an abstract `IsEllSequence`/`normEDS` + a chord-law hypothesis, then specialize to `smulX` | this is exactly the BORDERLINE packaging axis — see sibling `smulX.md` Q1–Q2 |
| 6 | 1-categorical → higher-categorical? | no | not categorical | — |
| 7 | concrete index ℕ/ℤ → general monoid? | no | EDS are intrinsically ℤ-indexed | — |

Modern-idiom verdict: the only live reformulation is **#5 (abstract-EDS
packaging)** — and that is precisely the human-reviewer decision flagged for the
sibling `smulX` (BORDERLINE). It is not a mechanical weakening; it changes what
the theorem *is about* and still requires the missing point↔EDS bridge.
One-line reason: maximally general on its own terms; the remaining choice is how
to *package* the whole universal-curve development, not how to weaken this lemma.

---

### Diamond / defeq risk — `WeierstrassCurve.Universal.Affine.smulX_add` (Phase 4.5)

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | none | It is a proved `Prop`; anchors no instance. |
| 2 | Reducibility leak | none | A lemma, not a `def`/`@[reducible]`; nothing unfolds it. |
| 3 | Non-canonical unfolding | none | The `let ψ₂` in the statement is immediately `change`d to the explicit `y − negY x y` form; no hidden defeq surface. |
| 4 | Instance priority collision | n/a | Not an `instance`. |
| 5 | Universe issues | none | Monomorphic in `Universal.Field`. |
| 6 | Coercion ambiguity | none | No coercions introduced. |

### Risk verdict (Phase 4.5)
Overall risk: **NONE**. Risk is not what blocks this; the blocker is the
packaging/upstreaming judgment about the whole `Universal` development.

---

### Mathlib search-status: `WeierstrassCurve.Universal.Affine.smulX_add` (Phase 5)

Note: local mathlib oleans/source not unpacked this session (build stale, per
task); `lean_loogle`/`lean_leansearch` deferred tools were **not surfaced** in this
environment. Searched instead via the mathlib4 GitHub source + mathlib4_docs +
WebSearch, and the project's own forked copies. Evidence is conclusive.

[A] mathlib4 source — `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
    (fetched master): contains **only abstract integer/ring-indexed sequences** —
    `IsEllSequence`, `IsDivSequence`, `IsEllDivSequence`, `preNormEDS`,
    `normEDS`, `complEDS`, `map_*`. **No** `smulX`, `smulY`, `smulX_add`, **no**
    `Universal` namespace, **no** `polyToField`, **no** point-coordinate formula,
    **no** `net` (the project's 4-variable `net`/`net_add_sub_iff` are
    fork-additions, not in mathlib).
[B] mathlib4_docs — `DivisionPolynomial/Basic` + `…/Degree`: define the
    polynomials `preΨ, ΨSq, Ψ, Φ, ψ, φ` (and TODO `ωₙ`) **at the polynomial level
    only**. The docstring explicitly states the classical motivation
    `φₙ := Xψₙ² − ψₙ₊₁ψₙ₋₁` and `x(nP) = φₙ/ψₙ²` — but **does not implement** the
    coordinate formula; there is no evaluation-at-a-point / n•P-coordinate result.
[C] mathlib4_docs — `Affine/Formula`, `Projective/*`, `Jacobian/*`: have the
    general chord-tangent **group law** (`slope`, `addX`, `addY`, `add`) but
    **no** division-polynomial coordinate formula for `n • P`, and **no**
    universal-curve / generic-point development.
[D] Name pattern: `smulX_add`, `Universal.Affine.smul*`, `zsmul_eq_smulEval`,
    `polyToField` — **zero** hits anywhere in mathlib; the only in-repo hits are
    this project + a verbatim duplicate in HasseWeil.

Searched for both:
  - user's current form (EDS x-addition on the universal curve) — **not in mathlib**;
  - literature-standard ingredients (EDS recurrence + `φ/ψ²` coordinate) — the
    *polynomials* and the *abstract recurrence* are in mathlib, but the
    **coordinate identity `x(nP)=φₙ/ψₙ²` and everything downstream (including
    `smulX_add`) is NOT** — mathlib's own docstring flags it as motivation only.

Concluded: **NOT in mathlib.** The lemma presupposes a universal-curve
function-field layer that mathlib does not have, and states a coordinate identity
mathlib explicitly leaves unformalized.

---

### Call sites — `WeierstrassCurve.Universal.Affine.smulX_add` (Phase 6.0)

Internal use count (NagellLutz): **K = 1** — `ZSMul.lean:366`, inside the `X_eq`
step of `zsmul_point_eq_smulX_smulY` (line 365–367), establishing
`smulX (n₂+1) = addX (smulX n₂) (smulX 1) L` (i.e. the induction step matching the
EDS x-formula to the actual group-law `addX`).
External-to-file callers within NagellLutz: **0** (only `ZSMul.lean` uses it; the
docstring mention at line 65 is prose).

| Caller file:line          | Usage pattern (one-line excerpt)                                                                 |
|---------------------------|--------------------------------------------------------------------------------------------------|
| LutzNagell/ZSMul.lean:366 | `rw [Nat.cast_add, Nat.cast_one, smulX_add one_ne_zero (by omega) (by omega) (by omega), Affine.addX_eq_addX_negY_sub _ _ ne, …]` |

Cross-project duplicate (verbatim fork): **HasseWeil** re-derives the identical
lemma — `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:371`
(`lemma smulX_add …`, same `smulX_add_aux` at :366, used once at :438) — confirming
the construction is reusable across projects *and* is currently fork/duplicate
code (a dedup/consolidation concern, and itself an argument for upstreaming the
shared layer). **No** General*/PID* track copy exists.

Inline-derivation grep: the x-addition identity is **not** re-derived inline
elsewhere; where it is needed it goes through `smulX_add`.

Composability signal: K = 1 internal use but **load-bearing** for a main theorem,
+ a second project depends on the same construction → genuine, reusable content,
leans YES-* on substance; the duplication is both reuse-evidence and a dedup flag.

### Composition check (Phase 6)

Can `smulX_add` be derived from mathlib in ≤3 chained calls?

Attempt 1: assemble it from mathlib's group law + division polynomials directly.
  - Would need: a mathlib statement of `x(kP) = φₖ/ψₖ²` (the coordinate formula),
    the chord law `addX`, and the EDS recurrence on the *coordinate* sequence.
  - Result: **fails** — mathlib has the chord law and the abstract recurrence, but
    **not** the `x(kP)=φₖ/ψₖ²` coordinate bridge (its docstring leaves it as
    motivation), and **not** the universal-curve function field in which the
    identity is even stated. The target type (`Universal.Field`) and all the
    operands (`smulX`, `smulY`, `ψᵤ`) do not exist upstream.

Attempt 2: build the universal layer from mathlib `FractionRing`/`AdjoinRoot`/
`MvPolynomial`, then run the project's three-lemma chain.
  - This **constructs the entire `Universal` development** (`Universal.lean` +
    much of `ZSMul.lean`: `smulX`, `smulY`, `ψᵤ`, `smulX_sub_smulX`,
    `smulX_sub_sub_smulX_add`, `smulY_sub_negY`, and the fork-extended EDS
    `net`/`net_add_sub_iff`) before `smulX_add` can even be *stated*. Far more
    than 3 calls; it is the project's job, not a composition.

Conclusion: **NOT-COMPOSABLE** in ≤3 mathlib calls. `smulX_add` presupposes the
missing universal-curve coordinate layer; it is a step in a bespoke development,
not a short composition of existing mathlib lemmas.

---

## Verdict: `WeierstrassCurve.Universal.Affine.smulX_add`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature search (Phase 3): the ingredients — EDS three-term recurrence and
  `x(nP) = φₙ/ψₙ²` — are fully standard (Wikipedia EDS, Au-Yeung, Silverman,
  arXiv:2102.07573); the chord law `x₃=λ²−x₁−x₂` is standard. But this **precise
  repackaged identity is unnamed in the literature** — it is an intermediate on
  the way to `x(nP)=φₙ/ψₙ²`, surfaced as a separate lemma only because of the
  project's affine strong-induction proof architecture. Author = Junyan Xu
  (mathlib's EC author) → upstreaming-track code.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL on the base** (universal
  curve over ℤ = initial Weierstrass object; 0 weakening opportunities). The only
  open axis is **packaging** (abstract-EDS reformulation, Phase 4c #5), which is a
  reviewer decision, not a mechanical weakening.
- Mathlib search (Phase 5): **NOT in mathlib** — `EllipticDivisibilitySequence`
  is abstract sequences only; `DivisionPolynomial/Basic` is polynomials only and
  its docstring explicitly leaves `x(nP)=φₙ/ψₙ²` *unimplemented*; no `Universal`
  layer, no `smulX`/`smulX_add`, no `net`.
- Composition check (Phase 6): **NOT-COMPOSABLE** — presupposes the missing
  universal-curve coordinate layer; the target type and operands don't exist
  upstream.

**Rationale:**

The *mathematical content* `smulX_add` participates in — the universal
division-polynomial formula for `n • P` and the universal-curve infrastructure
(`Universal.Ring`, `Universal.Field`, `polyToField`, `ψᵤ`, `smulX`, `smulY`) — is
clearly mathlib-worthy and **genuinely missing**: mathlib has the division
polynomials and the abstract EDS recurrence, its own docstring points at exactly
`x(nP)=φₙ/ψₙ²` as the motivation, yet neither the universal curve nor the n•P
coordinate identities are formalized there. `smulX_add` is one of the three EDS
identities (with `smulX_sub_sub_smulX_add`, `smulY_add_sub_negY`) that the module
docstring names as the engine of the induction step. The HasseWeil verbatim
duplicate confirms it is reusable across projects (and is currently fork code).

What pushes this to BORDERLINE rather than a clean YES — and aligns it exactly
with its sibling `WeierstrassCurve.Universal.Affine.smulX` (also BORDERLINE) — is
that `smulX_add` is an **internal scaffolding lemma whose value is entirely tied
to the project's chosen proof route** (the affine strong-induction derivation of
`zsmul_point_eq_smulX_smulY`). It is correct, maximally general, and well
supported, but whether mathlib wants *this specific intermediate, with this
statement, as a free-standing lemma* is precisely the API-packaging judgment a
mathlib reviewer makes when the surrounding development is upstreamed. Plausible
outcomes: (a) take it essentially as-is as a named EDS x-addition lemma on the
universal curve; (b) restate it on an *abstract* EDS (`normEDS`/`net` over a ring)
plus a chord-law bridge, with the universal-curve version a one-line
specialization; or (c) reorganize the universal layer so this step is spelled
differently (e.g. folded into the proof of `x(nP)=φₙ/ψₙ²` and never named). The
lemma cannot be assessed in isolation from that decision, and the decision is not
one the skill should make alone.

The correct unit of upstreaming is **the whole universal-curve + n•P-formula
development** (the same conclusion as `smulX.md`), not this single lemma — so the
actionable recommendation is to route the *file/development* to a human + mathlib
reviewer, with `smulX_add` flagged as "belongs, modulo packaging".

**Numbered questions (for the user / a mathlib reviewer):**

1. Should the **entire `Universal` Weierstrass-curve layer** (`Universal.Ring`,
   `Universal.Field`, `curve`, `polyToField`, `ψᵤ`, `smulX`, `smulY`, the three
   EDS identities `smulX_sub_sub_smulX_add` / **`smulX_add`** / `smulY_add_sub_negY`,
   and the n•P formula `zsmul_eq_smulEval`) be upstreamed to mathlib as one
   development? (If yes, `smulX_add` rides along as part of the PR unit.)
2. If yes to (1): keep `smulX_add` as a **named universal-curve lemma** (current
   form), or **restate it on an abstract EDS** (`normEDS`/`net` over a ring) with
   the universal version a one-line specialization? (Phase-4c packaging axis.)
3. Is mathlib's EC maintainer (Junyan Xu / `alreadydone`, the file author and
   original division-polynomial contributor) **already preparing** this
   upstreaming? The NagellLutz↔HasseWeil duplicate suggests in-flight work; if a
   mathlib PR exists, this is **NO-mathlib-has-it (pending)** and the project
   should track that PR rather than re-upstream.
4. Independent of mathlib: the **verbatim duplication** between
   `NagellLutz/…/ZSMul.lean:300` and
   `HasseWeil/…/Auxiliary/DivisionPolynomial.lean:371` should be consolidated into
   AINTLIB `Common/` regardless of the mathlib decision — file a dedup ticket now?

**Next action:** user answers Q1–Q4 (especially Q3 — check whether the
universal-curve / n•P formula is already an open mathlib PR by Junyan Xu). If
upstreaming is desired, treat the *whole universal-curve development* as the PR
unit and run `/generalise` / `/cleanup` on the file, not on `smulX_add` alone.
Independently, file an AINTLIB dedup ticket for the NagellLutz↔HasseWeil duplicate.

---

## Next step

Do not upstream `smulX_add` as an isolated lemma, and do not delete it — it is a
load-bearing EDS x-coordinate addition identity in a genuinely-missing
universal-curve development, but the packaging of this exact intermediate is a
mathlib-reviewer call. Route the **whole `Universal` layer** (assessed together
with the sibling `smulX`, also BORDERLINE) to a human + mathlib reviewer, after
checking whether Junyan Xu already has it in flight upstream. Independently, file
an AINTLIB `Common/` dedup ticket for the verbatim NagellLutz↔HasseWeil copy.
