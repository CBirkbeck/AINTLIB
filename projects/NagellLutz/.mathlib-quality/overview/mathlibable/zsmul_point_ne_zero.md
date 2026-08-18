# /mathlibable report — `WeierstrassCurve.Universal.Affine.zsmul_point_ne_zero`

> Step-9 single-declaration mathlibable assessment (NagellLutz / `/overview`).
> Date: 2026-06-22. Local build stale per task brief; reasoned from source + the mathlib
> tree at `.lake/packages/mathlib` + WebSearch / loogle / leansearch.
> NOTE: the assigned target is the **Affine** lemma at ZSMul.lean:**389**
> (`...Universal.Affine.zsmul_point_ne_zero`). There is a sibling **Jacobian** lemma of the
> same base name at line 402; that is a *different* decl and is not the subject of this report.

---

### Baseline (Phase 0)
- lake build:               ⚠ not re-run (local build stale per task brief; reasoned from
                            source + mathlib tree).
- decl `WeierstrassCurve.Universal.Affine.zsmul_point_ne_zero`:
                            ✓ resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:389`.
- qualified name VERIFIED from source:
    `namespace WeierstrassCurve` (ZSMul.lean:76) → `namespace Universal` (86) →
    `namespace Affine` (157); lemma `zsmul_point_ne_zero` (389), inside `end Affine` (393).
- kind:                      lemma (theorem).
- has sorry:                 no.
- module docstring summary:  ZSMul.lean proves `n • P = (φₙ : ωₙ : ψₙ)` in Jacobian
  coordinates for any integer `n` and nonsingular point `P = (x,y)` on a Weierstrass curve
  over a field, via the **universal pointed Weierstrass curve** and division polynomials.

### Statement (Phase 1)

`WeierstrassCurve.Universal.Affine.zsmul_point_ne_zero` states:

> For the distinguished point `P = (X, Y)` on the **universal** pointed Weierstrass curve
> (the curve `Y² + A₁XY + A₃Y = X³ + A₂X² + A₄X + A₆` over the field
> `K = Frac(ℤ[A₁,A₂,A₃,A₄,A₆][X,Y]/⟨Weierstrass poly⟩)`, with `P` the tautological/generic
> point given by the residue classes of `X` and `Y`), and any nonzero integer `n`, the
> multiple `n • P` is not the point at infinity `O`. Equivalently: the generic point `P`
> is **non-torsion** (of infinite order).

Source (ZSMul.lean:388–391):
```lean
/-- The distinguished point `(X,Y)` on the universal curve is not torsion. -/
lemma zsmul_point_ne_zero (h0 : n ≠ 0) : n • Affine.point ≠ 0 := by
  obtain ⟨ns, eq⟩ := zsmul_point_eq_smulX_smulY h0
  rw [eq]; exact Affine.Point.some_ne_zero ns
```

Variables / typeclasses involved (Lean side):
- `n : ℤ` (section `variable`, scoped over `Affine`).
- All curve data is fixed (`curve`, `pointedCurve`, `Universal.Field`, `Affine.point`) — no
  free typeclass parameters; this is a statement about one specific, fully-determined object.

Hypotheses (Lean side):
- `h0 : n ≠ 0`.

Conclusion (math): `n • P ≠ O`, i.e. `P` is not a torsion point.
Conclusion (Lean): `n • Affine.point ≠ 0`
  where `Affine.point : (curve.baseChange Universal.Field).toAffine.Point` (Universal.lean:151,
  `:= .mk equation_point`).

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-direction glue lemma (`n • point ≠ 0`) sitting directly on top of the
substantive `zsmul_point_eq_smulX_smulY` (ZSMul.lean:344, the ~50-line `Int.negInduction` +
`Nat.strong_induction_on` engine). Not a `## Main result`, not named after a person/place,
introduces no new structure. (Note: literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: 2 substantive lines (`obtain ⟨ns, eq⟩ := zsmul_point_eq_smulX_smulY h0`;
`rw [eq]; exact Affine.Point.some_ne_zero ns`).
One-liner verdict: n/a — kind is `lemma`, not `def`. The defeq/diamond/API-name exemption
analysis applies only to one-line *definitions*; skipped for proofs. (Recorded for the verdict:
the deceptively short body rests entirely on a large helper — see Phase 6.)

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found                                   | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|-------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "universal Weierstrass curve generic point non-torsion division polynomials Nagell-Lutz"        | yes  | universal curve + universal point is a standard object | arXiv:1303.4327 ("universal point corresponding to the identity map on the smooth Weierstrass curve"); Alpoge "Nagell-Lutz, quickly"; valuation-of-ψₙ papers (arXiv:1108.3051) |
|  2 | WebSearch (general / mathlib)    | "mathlib WeierstrassCurve Universal curve zsmul_point division polynomial Junyan Xu PR"          | partial | confirms Angdinata–Xu mathlib EC development; no standalone PR for this decl | ITP 2023 "Elementary Formal Proof of the Group Law on Weierstrass Elliptic Curves in Any Characteristic" (Angdinata, Xu); mathlib has DivisionPolynomial/EDS files but no `Universal` object |
|  3 | WebSearch (named-after / route)  | (within #1) "non-torsion of generic point" vs "ψₙ ≠ 0" framing                                  | yes  | non-torsion of the generic point ⇔ ψₙ does not vanish identically | the two are interchangeable; literature usually states the ψₙ-nonvanishing form |
|  4 | ChatGPT MCP                      | "is generic point of universal Weierstrass curve non-torsion a named theorem or technical lemma; generality?" (2 attempts) | n/a  | —                                                    | **MCP DOWN** — Codex CLI failed (stdin error) on both attempts; recorded n/a per environment note; compensated by reading arXiv:1303.4327 + standard Silverman framing |
|  5 | Local references                 | `ls projects/NagellLutz/.mathlib-quality/references/`                                           | n/a  | (no references dir present)                            | directory absent — recorded n/a |
|  6 | nLab                             | "elliptic curve", "division polynomial", "universal elliptic curve"                            | n/a  | nLab "universal elliptic curve" = moduli-stack notion, not this affine generic-point lemma | different (moduli) object; no statement of this lemma |
|  7 | nCatLab (categorical)            | —                                                                                              | n/a  | not a categorical concept                              | statement is about one group element's order; no categorical content |
|  8 | Stacks Project (alg geom)        | "Weierstrass equation", generic point order                                                    | n/a  | Stacks has Weierstrass-equation generalities, not torsion-of-generic-point | wrong granularity; Stacks doesn't carry this elementary EC lemma |
|  9 | MathOverflow / Math.SE           | "generic point of universal elliptic curve infinite order / non-torsion"                       | yes (qualitative) | folklore: a curve with generic/transcendental coefficients has the tautological point of infinite order | well-known but treated as a routine specialization / ψₙ argument, not a citable named theorem |
| 10 | recent arXiv (last 5y)           | "explicit valuations of division polynomials" (1108.3051); homogeneous division polys (1303.4327) | yes  | ψₙ-nonvanishing on the universal curve is the working tool | confirms the fact is used as machinery, not stated as a headline theorem |

### Literature summary (Phase 3)

Concept identified as: **non-torsion (infinite order) of the tautological/generic point on the
universal Weierstrass curve** — equivalently, the engine behind "the universal `n`-division
polynomial `ψₙ` does not vanish identically".

Sources agree on the standard form: **yes**, with a framing caveat. The literature almost
always packages this as **"ψₙ ≢ 0 on the universal curve"** (a polynomial-nonvanishing
statement) and derives point-nonvanishing from it. In this project the order is reversed:
`ψᵤ_ne_zero` (ZSMul.lean:142) is proved *first* by specializing to the cusp, and
`zsmul_point_ne_zero` is the downstream point-theoretic consequence via the coordinate formula
`zsmul_point_eq_smulX_smulY`. Either way the mathematical content — generic point has infinite
order — is standard and uncontroversial.

Most general standard form: "the generic point of an elliptic curve over a function field whose
coefficients are algebraically independent is non-torsion." The universal curve over
`ℤ[A₁..A₆]` (used here) is the maximally-general instance — every pointed Weierstrass curve is a
specialization of it.

Generality dimensions where the literature varies:
  - base ring: `k(j)`, `k(A₁..A₆)`, `ℚ̄(t)`; the **universal** `ℤ[A₁..A₆]` form (used here) is
    the most general — it specializes to all of them.
  - framing: "point is non-torsion" (this lemma) vs "ψₙ ≠ 0" (more common in the literature).

Disagreement with the literature: none. The Lean statement is a faithful instance of the
standard folklore fact, specialized to the universal curve.

### Generality analysis — `WeierstrassCurve.Universal.Affine.zsmul_point_ne_zero`

Literature-standard form (Phase 3): generic point of the universal pointed Weierstrass curve
over `ℤ[A₁..A₆]` is non-torsion. (Already the most-general base.)

| # | Parameter / hypothesis | Current Lean form                              | Literature-standard form          | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------------------------------------|------------------------------------|---------------------|----------------------------------|
| 1 | base object            | THE universal curve over `ℤ[A₁..A₆]`, base-changed to `Universal.Field` | the universal curve (terminal case) | NO | already the universal object; every pointed Weierstrass curve is a base-change of it. Nothing more general to weaken *to*. |
| 2 | `n : ℤ`, `h0 : n ≠ 0`  | integer multiple                                | integer multiple                   | NO                  | torsion order is intrinsically a ℤ-action statement; ℤ is the correct index. |
| 3 | the point              | the distinguished `point = (X,Y)`               | the tautological/generic point     | NO                  | the statement is specifically *about this point*; generalizing the point changes the theorem. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (as a statement about the universal curve, which is
itself the terminal object — there is no broader base to lift it to).
Number of weakening opportunities found: 0.
Cost of restatement: n/a.

Note on a *different* repackaging: one could later state a downstream-facing general lemma "for
any pointed Weierstrass curve over a domain in which all `ψₙ` are nonzero, the point is
non-torsion." That is a *different* (consumer) lemma, not a generalization of this one — this
lemma is precisely the **base case** for the universal `ψₙ ≠ 0`, from which such a general
statement would be derived by specialization. So it is not a "generalise-first" target; it is
the foundational instance. (See 4c.)

### Modern-idiom check (Phase 4c)

| #  | Question                                                            | Applies? | Proposed reformulation | Mathlib downstream |
|----|---------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                  | no       | — | object fully fixed; no hypotheses to instance-ify |
|  2 | sequences/metric → filters/topology?                                | no       | — | no analytic content |
|  3 | construction → universal-property class?                            | no (already) | — | the *curve* already is "the universal" object; this is a property of it |
|  4 | set-with-closure-predicate → bundled substructure?                  | no       | — | no substructure |
|  5 | vector-space/field-specific → weaken typeclass hierarchy?           | no       | — | already at the universal base ring `ℤ[A₁..A₆]` |
|  6 | 1-categorical → higher-categorical?                                 | no       | — | elementary group-order statement |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary monoid?                            | no       | — | `n : ℤ` is the intrinsic index for additive-group torsion |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. A concrete, already-maximally-general property of a fixed
universal object; no contemporary mathlib reformulation improves its organisation. One-line
reason: it is an elementary "this specific group element has infinite order" fact about the
terminal pointed Weierstrass curve — nothing to filter-ise, bundle, or categorify.

### Diamond / defeq risk — Phase 4.5

n/a — declaration kind is `lemma` (introduces no definitional equality or typeclass-search path).

### Mathlib search-status: `WeierstrassCurve.Universal.Affine.zsmul_point_ne_zero`

[A] Lean-Finder        n/a (offline index)        — relied on authoritative mathlib-source grep (method D) for existence.
[B] Loogle             `WeierstrassCurve.Universal.*`, `_ • _ ≠ 0` on EC `Point`  — no hits; mathlib has no `WeierstrassCurve.Universal` namespace at all.
[C] LeanSearch         "universal Weierstrass curve point non torsion", "elliptic curve point infinite order"  — no hits.
[D] Grep mathlib src   `WeierstrassCurve.Universal`, `namespace Universal`, `baseChange curve`, `pointedCurve`, `zsmul_eq_smulEval`, `IsTorsion`/`nonTorsion`/`AddOrderOf`/`zsmul_ne_zero` under `Mathlib/AlgebraicGeometry/EllipticCurve/`  — **all empty**. Mathlib's only `Universal*` files are `Morphisms/UniversallyOpen.lean`, `Lie/UniversalEnveloping.lean` (unrelated). Mathlib's EC directory has **zero** torsion / non-torsion / point-order lemmas. DivisionPolynomial/Basic.lean mentions "the characteristic-0 universal ring `ℤ[A₁..A₆][X,Y]`" as *motivating prose only* — not constructed as a Lean object.
[E] Name pattern       `zsmul_point`, `point_ne_zero`, `some_ne_zero` in mathlib EC  — only `WeierstrassCurve.Affine.Point.some_ne_zero` (Affine/Point.lean:608) exists; that is the trivial "a `some` point ≠ 0" fact, NOT this lemma.

Searched for both:
  - the user's form (universal point non-torsion) — not in mathlib.
  - the literature-standard form (universal `ψₙ ≠ 0`, generic point infinite order) — not in mathlib.
  - the generic group-theory escape (`IsAddTorsionFree.zsmul_eq_zero_iff*`,
    `Mathlib/Algebra/Group/Torsion.lean:78`) — exists, but **inapplicable**: needs an
    `IsAddTorsionFree` instance on the EC `Point` group, which **does not exist** in mathlib
    (it is false in general; torsion-freeness of the universal point is exactly what is proved here).

Concluded: **not in mathlib** (all methods exhausted, plus the literature-standard form and the
generic-group escape). The only building block mathlib provides is
`WeierstrassCurve.Affine.Point.some_ne_zero`, which discharges only the trivial final line.

### Call sites — `WeierstrassCurve.Universal.Affine.zsmul_point_ne_zero`

Internal use count (NagellLutz, excluding the declaring file's own lines): **1**
External-to-file callers: 1 distinct file *outside* NagellLutz (a duplicate fork in HasseWeil).

| Caller file:line                                                | Usage pattern |
|------------------------------------------------------------------|---------------|
| `projects/NagellLutz/LutzNagell/ZSMul.lean:405`                  | `exact Affine.zsmul_point_ne_zero h0` — consumed by the **Jacobian** `zsmul_point_ne_zero` (line 402), which feeds `zsmul_point_ne` (407), used at ZSMul.lean:522 inside the main `zsmul_eq_smulEval` development |
| `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:475` | `exact Affine.zsmul_point_ne_zero h0` — a **near-verbatim duplicate** of the same lemma (forked from the same Angdinata–Xu source; the HasseWeil copy is at line 457) |

Inline-derivation grep: the HasseWeil copy (`Auxiliary/DivisionPolynomial.lean:457`) is the same
statement re-proved independently (cross-project duplication), not an inline bypass.

Call-sites signal: K = 1 internal use, but it is a **load-bearing** rung in the chain
`zsmul_point_eq_smulX_smulY → Affine.zsmul_point_ne_zero → Jacobian.zsmul_point_ne_zero →
zsmul_point_ne → zsmul_eq_smulEval` (the file's main result). Not dead code.

### Composition check (Phase 6)

Can `zsmul_point_ne_zero` be derived from mathlib in ≤3 chained calls? **No.**

Attempt 1: `WeierstrassCurve.Affine.Point.some_ne_zero _`.
  - Mathlib decls used: `WeierstrassCurve.Affine.Point.some_ne_zero`.
  - Result: **partial / fails** — `some_ne_zero` only fires once you already KNOW
    `n • point = some _ _ h` for some nonsingular `(smulX n, smulY n)`. Producing that equality
    *is* the content of `zsmul_point_eq_smulX_smulY` (ZSMul.lean:344): a ~50-line proof by
    `Int.negInduction` + `Nat.strong_induction_on` invoking the addition/doubling formulas,
    `smulX_add`, `smulY_add_sub_negY`, `addX_eq_addX_negY_sub`, `nonsingular_add`, etc. That is a
    genuine new proof, not a composition.

Attempt 2 (generic-group angle): `IsAddTorsionFree.zsmul_eq_zero_iff_right`.
  - Result: **fails** — requires `[IsAddTorsionFree ((curve.baseChange Universal.Field).Point)]`,
    which mathlib does not provide and which is exactly the hard fact (the EC point group is not
    torsion-free in general).

Conclusion: **NOT-COMPOSABLE.** The lemma's one-line body is deceptive — its truth rests entirely
on the project-specific `zsmul_point_eq_smulX_smulY` engine, which mathlib does not have.

## Verdict: `WeierstrassCurve.Universal.Affine.zsmul_point_ne_zero`

**Category:** YES-but-generalise-first

**Evidence:**
- Literature search (Phase 3): standard folklore fact (generic point of the universal curve is
  non-torsion ⇔ universal `ψₙ ≠ 0`); arXiv:1303.4327, Angdinata–Xu ITP 2023. Standard framing is
  the **ψₙ-nonvanishing** statement, of which this is the point-theoretic face.
- Generality analysis (Phase 4): MAXIMALLY GENERAL as a statement about the universal curve
  (terminal object); no modern-idiom restatement available (4c all `no`).
- Mathlib search (Phase 5): **not in mathlib** — no `Universal` namespace, no EC torsion lemma;
  only `Affine.Point.some_ne_zero` (trivial final step) exists.
- Composition check (Phase 6): **NOT-COMPOSABLE** — rests on the ~50-line
  `zsmul_point_eq_smulX_smulY` engine; the generic `IsAddTorsionFree` lemma is inapplicable.

**Rationale:**

The result is genuinely new to mathlib and genuinely useful: it is the point-theoretic
non-torsion fact at the heart of the universal-curve / division-polynomial machinery
(Angdinata–Xu lineage), exactly the kind of elliptic-curve API mathlib is actively growing. It
exists in mathlib in **no** form, and it does **not** fall out of any ≤3-call composition — its
one-line body sits on top of the substantial project-specific induction
`zsmul_point_eq_smulX_smulY`. So this is neither NO-mathlib-has-it nor NO-composable.

It lands in **YES-but-generalise-first** rather than YES-add-as-is for a *packaging* reason, not
a generality-weakening one. `zsmul_point_ne_zero` is a thin glue lemma
(`obtain … ; rw ; exact some_ne_zero`) that is meaningless in isolation: it can only be
upstreamed *together with* the whole development it depends on — `Universal.curve`,
`pointedCurve`, `Affine.point`, `ψᵤ_ne_zero`, `zsmul_point_eq_smulX_smulY`, and (downstream) the
Jacobian `zsmul_eq_smulField` — i.e. the `LutzNagell.Universal` + `ZSMul` files essentially in
full. The "generalise first" action here is therefore: **bundle this lemma into the
universal-curve PR as one rung of the `zsmul_eq_smulEval` ladder**, and export the
literature-canonical headline form (`WeierstrassCurve.Universal.ψ_ne_zero` / "the universal `ψₙ`
does not vanish") as the *named* result, with `Affine.zsmul_point_ne_zero` (and its Jacobian
sibling at line 402) as supporting lemmas. A secondary, follow-on generalisation: once shipped,
mathlib will want the downstream lemma "a point whose all `ψₙ` are nonzero is non-torsion" — but
that is a new consumer lemma, not a rewrite of this decl.

A blocking practical note for upstreaming: there is a **near-verbatim duplicate** in
`projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:457–475`. Whichever copy is
canonicalised, the other should be deleted and re-imported; shipping two is a defect. This is a
`main`-side cleanup/dedup task in addition to the upstreaming.

**For YES-but-generalise-first:**

Reason for the generalisation:
  - MODERN-IDIOM / PACKAGING: the standalone glue lemma should be upstreamed as part of the whole
    universal-curve development and exported under the literature-canonical headline
    (`ψₙ`-nonvanishing), with `zsmul_point_ne_zero` as a supporting rung — not as an isolated
    `feat` decl.
  - (NOT literature-weakening: Phase 4b found the form already maximally general.)

Proposed restatement (packaging target — this decl's own statement does **not** change):
```lean
namespace WeierstrassCurve.Universal
-- headline export (already present as `ψᵤ_ne_zero`, ZSMul.lean:142 — promote/rename for mathlib):
theorem ψ_ne_zero {n : ℤ} (hn : n ≠ 0) : ψᵤ n ≠ 0 := …
-- supporting rungs shipped in the same PR:
namespace Affine
theorem zsmul_point_ne_zero {n : ℤ} (h0 : n ≠ 0) : n • point ≠ 0 := …   -- THIS decl, unchanged
end Affine
namespace Jacobian
theorem zsmul_point_ne_zero {n : ℤ} (h0 : n ≠ 0) : n • point ≠ 0 := …
theorem zsmul_point_ne {m n : ℤ} (h : m ≠ n) : m • point ≠ n • point := …
end Jacobian
end WeierstrassCurve.Universal
```
Estimated cost of regeneralisation: **CHEAP** for this decl itself (no proof change — already in
final form). The real cost is upstreaming the *whole* `Universal` / `ZSMul` development, which is
MODERATE–EXPENSIVE but is the substantive Angdinata–Xu contribution and out of scope for this
single-decl assessment. (Cost does not downgrade the verdict.)

Mathlib downstream this enables:
  - the multiplication-by-`n` formula `n • P = (φₙ : ωₙ : ψₙ)` in Jacobian coordinates
    (`zsmul_eq_smulEval`) — the headline theorem of this file;
  - non-vanishing of evaluated division polynomials `ψₙ(P) ≠ 0` for non-torsion `P`, used across
    HasseWeil (`ψ_m_evalEval_mulByInt_ne_zero`) and for Nagell-Lutz;
  - the general "all-`ψₙ`-nonzero ⇒ non-torsion" lemma as an easy follow-on.

Next action: do **not** open a standalone `feat(…): add zsmul_point_ne_zero` PR. Route this
through the universal-curve upstreaming effort (the `LutzNagell.Universal` + `ZSMul` development,
Angdinata–Xu lineage); within that PR keep `Affine.zsmul_point_ne_zero` as a supporting lemma
under `WeierstrassCurve.Universal.Affine`. Separately, file a `main`-side dedup ticket to unify
with the HasseWeil copy (`Auxiliary/DivisionPolynomial.lean:457`). Run `/generalise` on the
*headline* `ψᵤ_ne_zero` (not this glue lemma) when preparing the PR.
