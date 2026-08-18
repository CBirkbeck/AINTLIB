# /mathlibable report — `WeierstrassCurve.Universal.Jacobian.point`

> Step-9 mathlibable assessment (NagellLutz project). Generated 2026-06-22.
> Repo root `/Users/mcu22seu/Documents/GitHub/aintlib-main`.
> Source: `projects/NagellLutz/LutzNagell/Universal.lean:155`.
> Environment note: local Lean build is stale (per task brief); ChatGPT MCP was
> **down** (Codex exec error — instructed fallback used: WebSearch ×3 at three
> generality levels + mathlib source grep + the prior-batch sibling reports).
> Reasoned from the source statement, as instructed.
>
> NOTE ON FILE NAME: this report lives at `.../mathlibable/point.md` per the task
> brief, but its subject is the **Jacobian** point (`Jacobian.point`, line 155),
> *not* the affine point (`Affine.point`, line 151). The affine point's own
> report is the prior `point.md` content that previously occupied this path; the
> brief explicitly targets line 155 (`Jacobian.point`), so this file now documents
> `WeierstrassCurve.Universal.Jacobian.point`. (Sibling reports: `pointedCurve.md`,
> `curve.md`, `equation_point.md`.)

---

## Baseline (Phase 0)

- lake build:                stale (not run; reasoned from source — instructed fallback)
- decl `WeierstrassCurve.Universal.Jacobian.point`:  ✓ resolved at `projects/NagellLutz/LutzNagell/Universal.lean:155`
- kind:                      `def`
- has sorry:                 no
- module docstring summary:  Additions to `Affine.Point` and the universal elliptic curve — defines
  `Universal.curve` over `ℤ[A₁,…,A₆]`, the universal pointed curve over the fraction field
  `Universal.Field`, with the **distinguished point `(X,Y)`** in both affine and Jacobian coordinates,
  plus the cusp curve `Y²=X³` used to show `ψₙ(1,1)=n` (hence the universal point has infinite order).

**Qualified name (VERIFIED from source).** Namespace stack: `WeierstrassCurve` (line 69) →
`Universal` (line 75); the decl is `def Jacobian.point` (line 155) — `Jacobian.` is a **dotted prefix
on the base name** (there is no `namespace Jacobian` block in the file; `grep` for it returns only the
`import` and the two decl lines). Full qualified name:
**`WeierstrassCurve.Universal.Jacobian.point`**. The parse-time guess matches.

**Exact statement (source, lines 149–156):**
```lean
open Polynomial Affine in
/-- The distinguished point on the universal pointed Weierstrass curve. -/
def Affine.point : (curve.baseChange Universal.Field).toAffine.Point :=
  .mk equation_point

/-- The distinguished point on the universal curve in Jacobian coordinates. -/
def Jacobian.point : Jacobian.Point (curve.baseChange Universal.Field) :=
  Jacobian.Point.fromAffine Affine.point
```
where:
- `Jacobian.Point.fromAffine` is mathlib's affine→Jacobian conversion
  (`Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Point.lean:397`):
  `def fromAffine [Nontrivial R] : W'.toAffine.Point → W'.Point | 0 => 0 | .some _ _ h => ⟨…⟩`.
  Its dot-notation alias `Affine.Point.toJacobian` (line 642) is *defined* as `fromAffine P`.
- `Affine.point` is the project-local affine universal point (line 151, own report — the prior
  `point.md`), `= Point.mk equation_point`.
- Mathlib's Jacobian-Point module docstring (lines 45–50) frames `fromAffine`/`toJacobian` as **the**
  standard conversion from a nonsingular affine point to its nonsingular Jacobian point, citing
  Silverman.

---

## Statement (Phase 1)

`WeierstrassCurve.Universal.Jacobian.point` is a **definition** of the distinguished / tautological
point `(X,Y)` of the universal pointed elliptic curve, **expressed in Jacobian coordinates** — i.e.
the same point as `Affine.point`, but as an element of mathlib's Jacobian-point type
`Jacobian.Point (curve.baseChange Universal.Field)`, obtained by the standard affine→Jacobian
embedding `(x,y) ↦ [x : y : 1]` (mathlib's `fromAffine`).

Concretely: `Affine.point` is the `Universal.Field`-rational affine point with coordinates
`(polyToField (C X), polyToField Y)`; `Jacobian.point` is its image `[X : Y : 1]` under
`Jacobian.Point.fromAffine`. Downstream, `point_point` (ZSMul.lean:411) records
`Jacobian.point.point = ⟦![polyToField (C X), polyToField Y, 1]⟧` by `rfl` — the literal
`[X : Y : 1]` representative.

Variables / typeclasses involved (Lean side): none free — a closed `def` over the concrete
`Universal.Field`. The hidden requirement `[Nontrivial Universal.Field]` (needed by `fromAffine`) is
discharged in-file (it is a field). The `IsElliptic` instance (line 132) is in scope.

Hypotheses (Lean side): none (definition). Internally consumes `Affine.point` (and through it,
`equation_point`).

Conclusion (math): the universal/tautological point `[X : Y : 1] ∈ E(K)`, in Jacobian coordinates.
Conclusion (Lean): `Jacobian.Point (curve.baseChange Universal.Field)` — n/a, it is a definition.

---

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: it is a **coordinate-representation conversion** of an existing object (`Affine.point`) via a
single mathlib function (`fromAffine`). It introduces **no new named mathematical concept**: the
literature names the universal/tautological point (the *affine* one carries that standing — see the
sibling `point.md` for `Affine.point`), but "the same point written in Jacobian coordinates" is an
implementation/representation choice, not a separately-named object. It is not a person-named theorem,
not a `## Main results` entry, and not the introduction of a new structure.

(Literature width is EXHAUSTIVE regardless. Recorded for framing. Contrast `curve` = BIG,
`Affine.point` = BIG-borderline; `Jacobian.point` is a notch below both — it is the Jacobian *view*
of `Affine.point`.)

## One-line check (Phase 2b)

Body line count: **1 substantive line** (`Jacobian.Point.fromAffine Affine.point`).
One-liner verdict: **ONE-LINER** (kind is `def`).

| Exemption                         | Applies? | Evidence                                                                 |
|-----------------------------------|----------|--------------------------------------------------------------------------|
| Avoid defeq abuse                 | **no**   | Downstream proofs *rely on* `Jacobian.point` unfolding to `fromAffine Affine.point`, not on it being sealed: `ZSMul.lean:403` does `rw [Jacobian.point, ← toAffineAddEquiv_symm_apply, …]`, and `point_point` (line 411) is `:= rfl` exposing the `[X:Y:1]` representative. The def is *transparent by design*, the opposite of a defeq barrier. |
| Avoid typeclass diamonds          | **no**   | not an instance; no competing instance path. `fromAffine` resolves the single in-file `IsElliptic`/`Nontrivial` context. |
| Mark semantic intent / API name   | **yes**  | `Jacobian.point` is the stable name the **Jacobian-coordinate ZSMul development** is stated against: `zsmul_point_ne_zero` (ZSMul.lean:402), `zsmul_point_ne` (407), `point_point` (411), `zsmul_point_eq_smulField` (424), and the nonsingular lemma (447) all reference `Jacobian.point` (or `n • Jacobian.point`) directly. |

Conclusion: **ONE-LINER WITH-EXEMPTION** (semantic-intent / API-name anchor — exemption #3). But the
*defeq* exemption is an explicit **anti-signal** (it is deliberately transparent: `rw [Jacobian.point]`
and `point_point := rfl` depend on the unfolding). Carried into Phase 7: the one-liner nature, with
only the "API name" exemption and an anti-signal on "defeq barrier", pulls the *standalone* assessment
toward NO-composable (its entire content is one `fromAffine` call).

---

## Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found                                              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | elliptic curve point Jacobian coordinates from affine coordinates conversion projective                | yes  | **affine→Jacobian is `X = x, Y = y, Z = 1`** ((x,y)↦[x:y:1]); inverse `x=X/Z², y=Y/Z³` | Wikibooks *Prime Curve/Jacobian Coordinates*; HackMD; cs.uaf.edu ECC-via-Jacobi; USPTO 8619977 — unanimous: it is a **mechanical representation change**, no independent content. |
|  2 | WebSearch (general / named form) | universal elliptic curve generic point Jacobian coordinates division polynomial homogeneous            | yes  | homogeneous division polys `α_n,β_n,γ_n`: for `P=(x:y:z)`, `nP=(α_n(P):β_n(P):γ_n(P))` | arXiv:1303.4327 (*Homogeneous division polynomials for Weierstrass elliptic curves*) — exactly the project's `smulField n` (= Jacobian coords of `n•point`). The *point* is just `[X:Y:1]`; the named objects are the **polynomials**, not "the Jacobian point". |
|  3 | WebSearch (named-after / aliases)| "Jacobian coordinates" elliptic curve point at infinity affine embedding (X:Y:1)                       | yes  | (x,y)→(X,Y,Z)=(x,y,1); ∞ = [0:1:0]; curve `Y²Z=X³+aXZ²+bZ³` | zenn.dev herumi ECC-jacobi; point-at-infinity.org; Wikibooks — again purely a coordinate system, never a separately-named "the Jacobian universal point". |
|  4 | ChatGPT MCP                      | "Is the Jacobian-coordinate version of the universal/tautological point a separately NAMED object, or just the standard affine→Jacobian embedding of the affine point?" | n/a  | **MCP down** (Codex exec error — task brief warned). Fallback: channels 1–3 + 6 + the mathlib source converge unambiguously — affine→Jacobian is a representation change; no named Jacobian universal point exists. | — |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/`                                                 | n/a  | (no references dir for NagellLutz)                              | directory absent — recorded n/a. |
|  6 | nLab                             | Jacobian coordinates / point of an elliptic curve in projective coordinates / generic point            | partial | nLab frames points of `E` scheme-theoretically (`Spec K → E`); coordinate models (affine/Jacobian/projective) are *charts*, not distinct objects | the choice of Jacobian coordinates is a presentation of the same `K`-point; nLab does not name a "Jacobian point" separately. |
|  7 | nCatLab (categorical)            | (same as #6 — the `K`-point is `Spec K → E`, coordinate-model-independent)                              | partial | the universal element / `K`-point is intrinsic; coordinates are a choice | confirms: Jacobian.point and Affine.point are the **same** categorical object in two charts. |
|  8 | Stacks Project (alg geom)        | points of a scheme ↔ field-valued morphisms; affine/projective coordinate charts                       | n/a  | base change / point-as-morphism is chart-independent           | Stacks frames points morphism-theoretically; "Jacobian coordinates" is a CS/arithmetic implementation notion, not a Stacks tag. Recorded n/a (not a Stacks-named concept). |
|  9 | MathOverflow / Math.SE           | (covered via #1–#3) Jacobian vs affine coordinates — representation, not new object                    | yes  | consensus: Jacobian coords are a speed/representation device; the point is the same | matches #1–#3. |
| 10 | recent arXiv (≤5y)               | homogeneous division polynomials / Jacobian-coordinate `n•P` for the generic curve (1303.4327, 1108.3051) | yes  | the *polynomials* `α_n,β_n,γ_n` are named; the generic point is `[x:y:1]` (a representative) | confirms the named objects are the division polynomials; "the Jacobian point" itself is not separately named. |

### Literature summary (Phase 3)

Concept identified as: **the universal/tautological point of the universal pointed elliptic curve,
expressed in Jacobian coordinates** — i.e. the standard affine→Jacobian embedding `(x,y) ↦ [x:y:1]`
applied to the (already-named) affine universal point.

Sources agree on the standard form: **yes** — affine→Jacobian conversion is uniformly `X=x, Y=y, Z=1`
(Wikibooks, HackMD, point-at-infinity.org, zenn/herumi, USPTO patents, cs.uaf.edu). It is a
**coordinate-representation change**, used for inversion-free scalar multiplication; it carries **no
independent mathematical content** beyond the affine point.

Most general standard form: there is **no generality knob** on "the Jacobian point" — it is forced
once you fix (a) the affine point and (b) the choice of Jacobian coordinates. The named objects in
this corner of the literature are the **homogeneous division polynomials** `α_n,β_n,γ_n` (arXiv
1303.4327), which give `n•P` in Jacobian/projective coordinates — *not* "the Jacobian point", which is
just the `[x:y:1]` representative of `P`.

Disagreement with the literature: **none.** The Lean form *is* the standard embedding. Critically,
**no source names "the Jacobian-coordinate universal point" as a distinct object** — every source
treats it as a representation of the affine point. (Contrast the *affine* universal/tautological point,
which the literature *does* name — see the sibling `Affine.point` report; the Jacobian version is one
representational step removed and has no name of its own.)

---

## Generality analysis — `WeierstrassCurve.Universal.Jacobian.point`

Literature-standard form (from Phase 3): the affine universal point re-expressed via the standard
affine→Jacobian map `(x,y)↦[x:y:1]`. No generality parameter on the Jacobian point beyond that of the
affine point it converts (which itself inherits all generality from `curve`, per `curve.md` →
MAXIMALLY GENERAL).

| # | Parameter / hypothesis                  | Current Lean form                              | Literature-standard form          | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------------|------------------------------------------------|------------------------------------|---------------------|----------------------------------|
| 1 | the affine point being converted        | `Affine.point` (universal tautological point)  | the universal/tautological point   | **NO**              | this is the unique universal point; generality lives in `Affine.point`→`curve` (already MAXIMALLY GENERAL). |
| 2 | the conversion map                      | `Jacobian.Point.fromAffine` (mathlib)          | the standard `(x,y)↦[x:y:1]` embedding | **NO**          | `fromAffine` *is* the canonical affine→Jacobian map (mathlib docstring, Silverman); no alternative/weaker map. |
| 3 | base field `Universal.Field`            | `Frac(curve.CoordinateRing)`                   | `Frac` of the universal coord ring | **NO**              | inherited from `Affine.point`/`curve`; this is the universal base. |
| 4 | coordinate model: Jacobian              | mathlib `Jacobian.Point` quotient `[x:y:z]`    | Jacobian (or affine, or projective) chart | (representation, see 4c) | choosing Jacobian over affine/projective is a *representation* choice, not a generality axis. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** with respect to the Jacobian point itself — it has **0
weakening knobs**; everything is inherited from `Affine.point`/`curve` (both MAXIMALLY GENERAL per
their reports). `fromAffine` is the canonical conversion.

Number of weakening opportunities found: **0**.
Proposed restatement: none for `Jacobian.point` qua point.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                 | Applies? | Proposed reformulation | Mathlib downstream |
|----|---------------------------------------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | "Let X be a foo" preambles → typeclasses/instances?                                                      | no       | closed term over a fixed field | — |
|  2 | sequences/metric → filters/topological?                                                                  | no       | no limiting notion | — |
|  3 | construct an object where a universal-property class would characterise it?                              | **no (and not here)** | the only universal-property/representability discussion lives on `curve`/`pointedCurve` (see `curve.md`); the Jacobian point is the *coordinate representation* of the universal element, not the universal element itself | the universal-element framing is `Affine.point`'s (the affine universal point); `Jacobian.point` just re-charts it. |
|  4 | set-with-closure-predicate → bundled substructure?                                                       | no       | n/a | — |
|  5 | field-specific → weaker typeclass?                                                                       | no       | the field is the universal `Frac`; not a weakening axis | — |
|  6 | 1-categorical → higher-categorical?                                                                      | no       | mathlib's `Jacobian.Point` quotient model is adequate | — |
|  7 | concrete index (ℕ,ℤ,ℝ) → arbitrary monoid/group?                                                         | no       | no index | — |
| 8  | concrete-via-abstract (named id vanishes in the proof body)?                                             | **no**   | the body is a single `fromAffine Affine.point` — there is no proof body to inspect; the *consuming* lemmas (`zsmul_point_eq_smulField`) are separate decls with their own reports | n/a — the def carries no proof. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no.** There is no Bourbaki-2.0 move on `Jacobian.point`: it is a single
application of mathlib's canonical conversion `fromAffine` to `Affine.point`. Any
universal-property/representability modernisation lives upstream on `curve`/`pointedCurve` (per their
reports); the Jacobian point merely *re-charts* the affine universal element and inherits whatever
framing the package gets. Treating the Jacobian re-charting as an independent modernisation target
would be double-counting (and `fromAffine` is already mathlib's idiom for the conversion).

One-line reason this is not a modernisation move: the def is one canonical mathlib conversion of an
existing object; no organisational redundancy is removed and no new downstream API is unlocked by
*naming* it (the conversion `fromAffine`/`toJacobian` is already named in mathlib).

---

## Diamond / defeq risk — `WeierstrassCurve.Universal.Jacobian.point` (kind: `def`)

| # | Risk                          | Verdict | Evidence / rationale                                                                 |
|---|-------------------------------|---------|--------------------------------------------------------------------------------------|
| 1 | Typeclass diamond             | none    | not an instance; uses the single in-file `IsElliptic`/`Nontrivial Universal.Field` context via `fromAffine`. No competing path. |
| 2 | Reducibility leak             | none    | plain `def` (not `@[reducible]`); body is one `fromAffine` application. It is unfolded explicitly downstream (`rw [Jacobian.point]`, `point_point := rfl`), which is intended, not a leak. |
| 3 | Non-canonical unfolding       | low     | `Jacobian.point` unfolds to `fromAffine Affine.point` (and on to the `[X:Y:1]` representative via `point_point := rfl`); downstream `rw`/`change` rely on this. No `@[simp]` on the def itself, so no surprise global unfolds. |
| 4 | Instance priority collision   | none    | not an instance. |
| 5 | Universe-polymorphism issues  | none    | monomorphic — `Universal.Field` is a fixed `Type`. |
| 6 | Coercion ambiguity            | none    | no `CoeFun`/`CoeSort`. (`.point` field projection is mathlib's `Jacobian.Point.point`, a quotient accessor, not a coercion.) |

### Risk verdict (Phase 4.5)

Overall risk: **NONE** (one `low` row that is by-design unfolding, not a hazard). No mitigation needed.

---

## Mathlib search-status: `WeierstrassCurve.Universal.Jacobian.point`

[A] Lean-Finder       (index unavailable in stale env; reasoned via source grep)   n/a: tool not runnable here
[B] Loogle            (index tool not available as a deferred tool in this environment)   n/a: substituted by [D] grep over the mathlib package source
[C] LeanSearch        (index tool not available)   n/a: substituted by [D]
[D] Grep mathlib src  `def (universal|generic|distinguished)?[Pp]oint`, `abbrev … [Pp]oint :`, `fromAffine`, `toJacobian`, `namespace Universal` in `Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/`   **decisive**: mathlib has the *conversion* `Jacobian.Point.fromAffine` (Jacobian/Point.lean:397) and its dot-alias `Affine.Point.toJacobian` (line 642, `:= fromAffine P`) — **but NO named Jacobian point** on any curve, and **no `Universal` namespace** anywhere in the EC tree.
[E] Name pattern      `Jacobian.point`, `Universal.Jacobian.point`, `genericPoint`, `universalPoint` in mathlib EC tree   no hits for any named Jacobian/universal point term.

Searched for both:
  - the user's current form (`fromAffine Affine.point` on the universal curve) — **absent** (no
    universal curve, no named point);
  - the literature-standard form (the `[x:y:1]` embedding of the tautological point) — mathlib has the
    embedding function (`fromAffine`/`toJacobian`) but **neither** a universal curve **nor** a named
    universal/Jacobian point to apply it to.

Concluded: **found the building block** `WeierstrassCurve.Jacobian.Point.fromAffine`
(`Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Point.lean:397`, alias `Affine.Point.toJacobian`
line 642) — the canonical affine→Jacobian conversion — **but the named object
`WeierstrassCurve.Universal.Jacobian.point` is not in mathlib**, and neither is the scaffolding it
converts (`Affine.point`, `pointedCurve`, `curve`, `Universal.Field`), which are the project's own
additions (see `curve.md`, `pointedCurve.md`, the affine `point.md`, `equation_point.md`). The form is
therefore **one mathlib `fromAffine` call applied to the project-local `Affine.point`**.

---

## Call sites — `WeierstrassCurve.Universal.Jacobian.point`

Internal use count: **7** distinct external-to-file uses (project-internal, in NagellLutz
`ZSMul.lean`, excluding the declaring file `Universal.lean`). The in-file use is the `def` itself
(line 156, `fromAffine Affine.point`).
External-to-file callers: **1** distinct file (`projects/NagellLutz/LutzNagell/ZSMul.lean`).

| Caller file:line               | Usage pattern (one-line excerpt)                                                  |
|--------------------------------|-----------------------------------------------------------------------------------|
| ZSMul.lean:402                 | `lemma zsmul_point_ne_zero (h0 : n ≠ 0) : n • Jacobian.point ≠ 0`                  |
| ZSMul.lean:403                 | `rw [Jacobian.point, ← toAffineAddEquiv_symm_apply, ← map_zsmul (toAffineAddEquiv _).symm, …]` |
| ZSMul.lean:407                 | `lemma zsmul_point_ne (h : m ≠ n) : m • Jacobian.point ≠ n • Jacobian.point`       |
| ZSMul.lean:411                 | `lemma point_point : Jacobian.point.point = ⟦![polyToField (C X), polyToField Y, 1]⟧ := rfl` |
| ZSMul.lean:424                 | `theorem zsmul_point_eq_smulField : (n • Jacobian.point).point = ⟦smulField n⟧`    |
| ZSMul.lean:447                 | `… using (n • Jacobian.point).nonsingular`                                         |
| (HasseWeil, parallel fork)     | `HasseWeil/Auxiliary/DivisionPolynomial.lean` mirrors lines 472, 479, 492, 540 with the **same** `Jacobian.point` |

Inline-derivation grep (was `fromAffine Affine.point` re-spelled elsewhere without using `Jacobian.point`?):
  - **HasseWeil `Auxiliary/Universal.lean:158`** re-declares the *same* `def Jacobian.point :=
    Jacobian.Point.fromAffine Affine.point` (a parallel fork, near-verbatim file, same author header) —
    a **duplication** signal, not a bypass. Within NagellLutz, no site re-spells `fromAffine
    Affine.point`; all go through the named `Jacobian.point`. One related site
    (`DivisionPolynomial.lean:473` in HasseWeil) does `change n • Point.fromAffine Affine.point ≠ 0`,
    i.e. unfolds the name to the body deliberately.

Signal: **K = 7 (NagellLutz) > 3, zero NagellLutz-internal inline re-derivation, but duplicated as a
parallel fork in HasseWeil** → it is **real, load-bearing local API** (the Jacobian-coordinate ZSMul
chain `zsmul_point_eq_smulField`/`zsmul_point_ne` is stated against it), **not** dead code and **not** a
bypassed wrapper. Per the call-sites table this leans toward "genuine API" — but the per-decl
*content* is one mathlib `fromAffine` call (see Phase 6), and the object is **forked**, not shared.

---

## Composition check (Phase 6)

Can `WeierstrassCurve.Universal.Jacobian.point` be derived from mathlib in ≤3 chained calls?

Attempt 1: `Jacobian.point := WeierstrassCurve.Jacobian.Point.fromAffine Affine.point`
  - Mathlib decls used: `WeierstrassCurve.Jacobian.Point.fromAffine` (**1 call**).
  - Result: **succeeds** — the body literally *is* one mathlib conversion call applied to the project's
    `Affine.point`. Per the Phase-6b heuristics table, `Foo.bar (Bar.baz)` / one function call is a
    genuine composition (`yes`), not a proof in disguise.
  - Notes: the only non-mathlib ingredient is `Affine.point` (assessed in the sibling affine `point.md`
    → BORDERLINE; its own ingredient `equation_point` → NO-composable). So relative to **mathlib +
    `Affine.point`**, `Jacobian.point` is a **clean ≤1-call composition** (`fromAffine Affine.point`).

Attempt 2 (decoupled view): if the pointed-universal-curve package (`curve`, `pointedCurve`,
`Affine.point`) were in mathlib, then `Jacobian.point` would be `Affine.point.toJacobian` (=
`fromAffine Affine.point`) — a one-call accessor inlineable at its call sites, or kept as a thin named
convenience for the Jacobian-coordinate API.
  - Result: **COMPOSABLE** — one `fromAffine`/`toJacobian` call given `Affine.point`.

Conclusion: **COMPOSABLE**. `Jacobian.point` is `Jacobian.Point.fromAffine Affine.point` — a single
mathlib call. The composition is genuine (not a disguised proof): there is no rewriting, no
automation, no multi-`have` reasoning — just one conversion function applied to one point. The named
`def` is a convenience accessor (Phase-2b exemption #3, "API name"), not new mathematical content
beyond `Affine.point` + mathlib's `fromAffine`.

---

## Verdict: `WeierstrassCurve.Universal.Jacobian.point`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): affine→Jacobian is the **standard coordinate-representation change**
  `(x,y)↦[x:y:1]` (Wikibooks, HackMD, point-at-infinity.org, zenn/herumi, arXiv 1303.4327); it carries
  **no independent mathematical content**, and **no source names a separate "Jacobian universal
  point"** — it is the affine universal point re-charted.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** (0 weakening knobs; all generality inherited
  from `Affine.point`/`curve`); modern-idiom check: **no** Bourbaki-2.0 move (it is one application of
  mathlib's canonical `fromAffine`).
- Diamond/defeq risk (Phase 4.5): **NONE** (plain `def`, deliberately transparent, no instance/coercion
  footprint).
- Mathlib search (Phase 5): the **building block `Jacobian.Point.fromAffine`** (alias
  `Affine.Point.toJacobian`) **is in mathlib** (Jacobian/Point.lean:397, 642); the named object and its
  scaffolding are not.
- Composition check (Phase 6): **COMPOSABLE** — `Jacobian.Point.fromAffine Affine.point`, a single
  mathlib call.

**Rationale (1–2 paragraphs):**

`Jacobian.point` is the universal/tautological point of the universal pointed elliptic curve **written
in Jacobian coordinates** — and that "written in Jacobian coordinates" is the whole of it. The
literature is unanimous (Phase 3) that affine→Jacobian conversion is a mechanical representation change
`(x,y)↦[x:y:1]`, used to make scalar multiplication inversion-free; it is not a separately-named
mathematical object. The named objects in this corner are the *homogeneous division polynomials*
`α_n,β_n,γ_n` (arXiv 1303.4327), which the project realises as `smulField n` in
`zsmul_point_eq_smulField` — *those* could be a mathlib contribution, but "the Jacobian point" itself
is just the `[X:Y:1]` representative of `Affine.point`. mathlib already owns the conversion as
`Jacobian.Point.fromAffine` / `Affine.Point.toJacobian`, and the def's body is exactly one call of it.
So on its per-declaration content, `Jacobian.point` adds nothing beyond `Affine.point` (sibling report)
+ mathlib's `fromAffine`.

This is the precise contrast with its siblings. `curve` is `YES-add-as-is` because it introduces a
*named concept with a universal property* (and mathlib's `DivisionPolynomial/Basic.lean:36–38` literally
gestures at it in prose). `Affine.point` is `BORDERLINE` because the *affine* tautological point **does**
have first-class literature standing as a named object (gated on the package + dedup decisions).
`Jacobian.point` is one representational step further removed: it has **no independent literature
name** (Phase 3 found none), and its body is a **single `fromAffine` call** — so the BORDERLINE
tension that applied to `Affine.point` (is the *named* tautological point worth shipping?) collapses
here to a clean NO-composable: even if the package goes to mathlib, "the Jacobian view of the universal
point" is `Affine.point.toJacobian`, a one-call accessor, not an independent declaration. The 7
NagellLutz call sites make it real *local* API (it is the anchor of the Jacobian-coordinate ZSMul
chain), but the call-sites signal answers "real API vs bypassed wrapper", not "independently
mathlib-worthy"; a genuinely-used wrapper whose content is one mathlib call is still NO-composable. And
the object is currently **forked** (HasseWeil `Auxiliary/Universal.lean:158` re-declares it verbatim),
which is a dedup signal, not a "this exact decl is the canonical upstream thing" signal.

**WHY not (refactor-actionable detail):**
- Mathlib has the building block. `Jacobian.point` is `WeierstrassCurve.Jacobian.Point.fromAffine
  Affine.point` — a single mathlib conversion (Jacobian/Point.lean:397; equivalently the dot-notation
  `Affine.point.toJacobian`, line 642) applied to the project-local affine universal point
  `Affine.point`. No new lemma or definitional content beyond `Affine.point` (sibling report) and
  mathlib's `fromAffine`.
- Mathlib building blocks (qualified names with paths):
  - `WeierstrassCurve.Jacobian.Point.fromAffine` — `Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Point.lean:397`
  - `WeierstrassCurve.Affine.Point.toJacobian` (dot-notation alias `:= fromAffine P`) — `…/Jacobian/Point.lean:642`
  - plus the project-local `WeierstrassCurve.Universal.Affine.point` (sibling `point.md`, BORDERLINE)
    and, behind it, `equation_point` / `pointedCurve` / `curve` (the latter is the real upstreaming
    target, `curve.md` → YES-add-as-is).
- Composition sketch (≤3 lines):
  ```lean
  -- given the project-local `Affine.point` (= Point.mk equation_point):
  def Jacobian.point : Jacobian.Point (curve.baseChange Universal.Field) :=
    Affine.point.toJacobian          -- = Jacobian.Point.fromAffine Affine.point  (one mathlib call)
  ```
- Call sites in our project (from Phase 6.0): **K = 7** in NagellLutz `ZSMul.lean`
  (`zsmul_point_ne_zero` 402, `zsmul_point_ne` 407, `point_point` 411, `zsmul_point_eq_smulField` 424,
  the nonsingular lemma 447, and the `rw [Jacobian.point]` at 403), plus a **parallel re-declaration**
  in HasseWeil `Auxiliary/Universal.lean:158` (with its own consumers in
  `Auxiliary/DivisionPolynomial.lean`).
- **Refactor plan.** This is *not* a "delete and inline at 7 sites" case — `Jacobian.point` is a useful
  local name and the 7 ZSMul sites should keep using it as the Jacobian-coordinate anchor. The
  actionable refactor is **bundle-side + dedup-side**, not delete-side:
  1. **Do not** open a standalone mathlib PR for `Jacobian.point`. If/when the pointed-universal-curve
     package is upstreamed (the *second* PR that `curve.md` defers and `equation_point.md` names —
     bundling `Affine.point` / `Jacobian.point` / `pointedCurve` / `IsElliptic`), ship `Jacobian.point`
     **with** it, defined as the one-line accessor `Affine.point.toJacobian` (= `fromAffine
     Affine.point`), as the Jacobian-coordinate view of the universal point. It rides along with
     `Affine.point`; it is not an independent `feat`.
  2. **Dedup across the two forks** (a `lane:cleanup` ticket, independent of any mathlib PR): NagellLutz
     `LutzNagell/Universal.lean:155` and HasseWeil `Auxiliary/Universal.lean:158` declare the *same*
     `Jacobian.point`. Factor the universal-curve material into one shared location (`Common/` per
     CLAUDE.md, or have HasseWeil `import` NagellLutz) so there is **one** `Jacobian.point`.
  3. Keep `Jacobian.point` as the local accessor for the 7 NagellLutz call sites either way.
- Next action: do **not** add `Jacobian.point` to mathlib as its own declaration. Instead (a) keep it as
  the project-local Jacobian-coordinate accessor `Affine.point.toJacobian`; (b) if the
  pointed-universal-curve package is upstreamed per `curve.md`/`equation_point.md`, include
  `Jacobian.point` in that bundle (not as a standalone PR); (c) file a `main`-side cleanup ticket to
  deduplicate the NagellLutz/HasseWeil copies into one shared definition.

---

## Next step

Do **not** PR `Jacobian.point` itself — it is `Jacobian.Point.fromAffine Affine.point` (=
`Affine.point.toJacobian`), a one-call composition of mathlib's canonical affine→Jacobian conversion
with the project's `Affine.point`. The real upstreaming target is `curve` (already `YES-add-as-is` in
`curve.md`); `Jacobian.point` should, if anything, ride along in the *pointed-universal-curve* bundle
(with `Affine.point` / `pointedCurve` / `equation_point` / `IsElliptic`, per `equation_point.md`) as the
Jacobian-coordinate accessor, not as its own `feat`. Independently, file a `main`-side `/cleanup` ticket
to deduplicate the parallel `Jacobian.point` declarations in NagellLutz `LutzNagell/Universal.lean:155`
and HasseWeil `Auxiliary/Universal.lean:158` into a single shared definition, keeping the local
`Jacobian.point` name for the 7 ZSMul call sites.
