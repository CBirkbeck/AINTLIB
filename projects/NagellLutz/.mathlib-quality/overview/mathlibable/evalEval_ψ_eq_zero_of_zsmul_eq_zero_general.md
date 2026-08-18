# /mathlibable report — `LutzNagell.LutzNagellTheorem.evalEval_ψ_eq_zero_of_zsmul_eq_zero_general`

## Verdict (TL;DR)

**Category: YES-but-generalise-first.**

The mathematical content (group-law torsion ⟹ division-polynomial `ψ_n` vanishes — the
forward half of the textbook iff "P is n-torsion ⟺ ψ_n(P) = 0") is genuinely missing from
mathlib and worth having. But *this* declaration is a one-line `ℤ/ℚ` specialization of the
genuinely-general result `LutzNagell.PID.evalEval_ψ_eq_zero_of_zsmul_eq_zero`
(`PIDPrimeOrder.lean:62`), which already holds over an arbitrary commutative-ring base `R`
with any algebra `K` (no domain/UFD/fraction-field hypotheses are even used — they are all
`omit`ted). The thing to upstream is the PID version; the ℚ wrapper should be dropped /
inlined at its call sites.

---

### Baseline (Phase 0)
- lake build:               not run (project build is stale per task; reasoning from source — task-sanctioned)
- decl `…evalEval_ψ_eq_zero_of_zsmul_eq_zero_general`: ✓ resolved at `projects/NagellLutz/LutzNagell/LutzNagellTheorem/GeneralPrimeOrder.lean:56`
- qualified name (VERIFIED from source): `LutzNagell.LutzNagellTheorem.evalEval_ψ_eq_zero_of_zsmul_eq_zero_general`
  (namespaces `namespace LutzNagell` then `namespace LutzNagellTheorem`, lines 19–20)
- kind:                      theorem
- has sorry:                 no (body is a single term: `PID.evalEval_ψ_eq_zero_of_zsmul_eq_zero W hns n htors`)
- module docstring summary:  prime-order & order-4 torsion integrality for general Weierstrass curves over ℤ.

---

### Statement (Phase 1)

`evalEval_ψ_eq_zero_of_zsmul_eq_zero_general` states: for a general Weierstrass curve
`W : WeierstrassCurve ℤ` with base change `curveQ W = W.map (algebraMap ℤ ℚ)`, if `(x, y)` is a
nonsingular ℚ-point and `n • P = 0` in the **Jacobian point group** (where
`P = Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)`), then the `n`-th division
polynomial of `curveQ W` evaluates to zero at `(x, y)`: `(curveQ W).ψ n |>.evalEval x y = 0`.

This is the forward direction of the classical characterization of torsion via division
polynomials: a point `P` is `n`-torsion iff `ψ_n(P) = 0`.

Variables / typeclasses (Lean side):
- `W : WeierstrassCurve ℤ` — the integral Weierstrass model (base ring fixed to `ℤ`).

Hypotheses (Lean side):
- `hns : (curveQ W).toAffine.Nonsingular x y` — `(x,y)` is a nonsingular affine point over ℚ.
- `n : ℤ` — the multiplier.
- `htors : n • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0` — `n`-torsion in the
  Jacobian point group.

Conclusion (math): `ψ_n(x, y) = 0`.
Conclusion (Lean): `((curveQ W).ψ n).evalEval x y = 0`.

---

### Size classification (Phase 2a)

Verdict: SMALL.
Reason: a specialization wrapper — one term-mode line delegating to the PID-generic theorem.
It is neither a named theorem, nor a new structure, nor a `## Main results` entry (the main
results of the file are the integrality theorems `x_integral_of_odd_prime_torsion_general`,
`integrality_of_order_four_general`, which *consume* this lemma).

### One-line check (Phase 2b)

Kind is `theorem`, so the formal def-oriented one-liner gate is `n/a`. BUT the spirit applies:
the body is the single term `PID.evalEval_ψ_eq_zero_of_zsmul_eq_zero W hns n htors`, i.e. a pure
re-export of a strictly-more-general result with `R := ℤ, K := ℚ`. This is the classic
"specialization wrapper" negative signal. There is no defeq-barrier, diamond-avoidance, or
API-stability reason for the wrapper to exist as a separate mathlib decl (it is an artifact of
the project's General*/PID* duplicated tracks). Carried into Phase 7: biases away from
YES-add-as-is.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | Nagell–Lutz proof, division polynomial `ψ_n` torsion point vanishes                                     | yes  | Nagell–Lutz: torsion pts integral; proof via `ψ_n` | Harvard "Nagell-Lutz, quickly"; Galperin REU; Wikipedia Nagell–Lutz |
|  2 | WebSearch (general/iff form)      | `"division polynomial"` torsion `nP=O` iff `ψ_n(P)=0` (Silverman)                                       | yes  | **"P is n-torsion ⟺ ψ_n(P)=0"** — standard | Wikipedia "Division polynomials"; Springer EJM 2016; arXiv 1603.00401 |
|  3 | WebSearch (named-after / aliases) | division polynomials torsion characterization (Silverman/Washington exercise) | yes  | `E[n]` is exactly the zero locus of `ψ_n` (for `n` odd / off 2-torsion) | confirms #2 from multiple sources |
|  4 | ChatGPT MCP                      | standard form + generality + history of "ψ_n(P)=0 ⟺ n-torsion"                                          | n/a  | (MCP down per task env)          | fell back to WebSearch ×3 + nLab + textbook knowledge as instructed |
|  5 | Local references                 | grep `.mathlib-quality/references/`                                                                     | n/a  | (dir absent)                     | `projects/NagellLutz/.mathlib-quality/references/` does not exist; `refs/NagellLutz/` absent |
|  6 | nLab                             | "division polynomial" / elliptic curve torsion                                                          | n/a  | nLab has no dedicated division-polynomial entry | concept is classical AG/NT, not categorical; recorded n/a-thin |
|  7 | nCatLab (categorical)             | —                                                                                                      | n/a  | not a categorical concept        | — |
|  8 | Stacks Project (alg geom)         | division polynomial / torsion of elliptic curve                                                        | n/a  | Stacks does not develop division polynomials | not in Stacks' scope (it stops short of this explicit EC torsion machinery) |
|  9 | MathOverflow / MSE                | division polynomial vanishing ⟺ torsion, generality over rings                                          | yes  | confirms iff; usually stated over a field / alg. closed field | classical statements are field-based; the *polynomial identity* itself is ring-level |
| 10 | recent arXiv (≤5 yr)              | division polynomials arbitrary isogenies / torsion (Stange 2025; 2509.07524)                            | yes  | reaffirms `ψ_n` ↔ torsion; modern work over general bases | arXiv 2509.07524 (Nagell–Lutz over imag. quad. fields), eprint 2025/521 |

### Literature summary (Phase 3)

Concept identified as: **the division-polynomial characterization of torsion** — "a point `P`
is an `n`-torsion point iff `ψ_n(P) = 0`" (Silverman *AEC* Exercise 3.7; Washington *Elliptic
Curves* §3.2; Wikipedia "Division polynomials").
Sources agree on the standard form: yes (the iff is textbook).
Most general standard form: the **polynomial identity** `nP = (φ_n/ψ_n², ω_n/ψ_n³)` holds over
any base where the division polynomials are defined (commutative ring); the *vanishing-⟺-torsion*
phrasing is usually stated over a field / algebraically closed field, but the **forward
direction `nP = O ⟹ ψ_n(P) = 0`** that this decl proves needs no field hypotheses — it follows
from the group-law/coordinate identity. (Confirmed by the PID source proof using none of the
domain/UFD/FractionRing hypotheses.)
Generality dimensions where the literature varies:
  - base ring: literature ranges from `ℚ`/number fields (Nagell–Lutz papers) → arbitrary fields
    (Silverman/Washington) → the underlying identity over any comm. ring. The most general for
    *this direction* is **arbitrary commutative base ring** (matches the PID version's actual
    hypotheses).
Disagreement with the literature: none. This decl is a correct (forward) specialization to ℚ.

---

### Generality analysis — `…_general`

Literature-standard form (Phase 3): the forward implication `nP = O ⟹ ψ_n(P) = 0` holds over an
arbitrary commutative-ring base (no field needed). The project *already proves exactly this* as
`PID.evalEval_ψ_eq_zero_of_zsmul_eq_zero` (`PIDPrimeOrder.lean:62`), whose signature is:
```
{R} [CommRing R] {K} [Field K] [Algebra R K] (W : WeierstrassCurve R)
  {x y : K} (hns : (curveK R K W).toAffine.Nonsingular x y) (n : ℤ)
  (htors : n • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0) :
  ((curveK R K W).ψ n).evalEval x y = 0
```
with `[IsDomain R] [UniqueFactorizationMonoid R] [DecidableEq K] [IsFractionRing R K]` all
explicitly `omit`ted — so the real content needs only `CommRing R`, `Field K`, `Algebra R K`.
(The proof uses `zsmul_eq_smulEval` + `Jacobian.Point.zero_point` + `Z_eq_zero_of_equiv` — none
field-specific beyond `Field K`, and `Field K` is likely itself weakenable; see 4c.)

| # | Parameter / hypothesis        | Current Lean form (`_general`)        | Literature / PID-standard form        | Weaker form exists? | Reason |
|---|-------------------------------|----------------------------------------|----------------------------------------|---------------------|--------|
| 1 | base ring                     | fixed `ℤ` (via `W : WeierstrassCurve ℤ`)| arbitrary `[CommRing R]`               | YES                 | PID version already does it; ℤ is a needless specialization |
| 2 | coefficient field of points   | fixed `ℚ` (via `curveQ = W.map (alg ℤ→ℚ)`)| arbitrary `[Field K] [Algebra R K]`  | YES                 | PID version uses `curveK R K`; ℚ is `K := ℚ` |
| 3 | `hns`, `n`, `htors`           | identical shape                        | identical                              | —                   | same (these are already maximally general) |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (it is `R := ℤ, K := ℚ` of an
already-existing general theorem).
Number of weakening opportunities found: 2 (base ring; point field).
Proposed restatement: **none needed for the project** — `PID.evalEval_ψ_eq_zero_of_zsmul_eq_zero`
*is* the general restatement and already exists, sorry-free. The upstreaming target is that decl.
Cost of "regeneralisation": CHEAP — it's already done; the action is to upstream the general one
and delete the ℚ wrapper.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Proposed reformulation | Downstream |
|----|--------------------------------------------------------------------------|----------|------------------------|------------|
|  1 | bundled "let W be over ℤ" preamble → typeclass/instance?                  | yes (already) | base as `[CommRing R]` + `Algebra R K` — the PID form | composes with every base-ring instantiation |
|  2 | sequences/metric → filters/topological?                                  | no       | — | purely algebraic identity |
|  3 | construct object → universal property?                                   | no       | — | — |
|  4 | set+closure-predicate → bundled substructure?                            | no       | — | — |
|  5 | field/metric-specific → weaken typeclasses (module/(semi)ring)?          | maybe    | `Field K` → domain `K`? the proof's use of `Z_eq_zero_of_equiv` over `K` may only need a domain | would let `K` be a fraction-ring/loc. without `Field` — a real further weakening, *for the PID version* |
|  6 | 1-categorical → higher-categorical?                                      | no       | — | — |
|  7 | concrete index `ℤ` → general additive structure?                         | partial  | base ring `ℤ → R` (= row #1) | unifies with arbitrary-base elliptic-curve API |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: yes — but it is exactly the base-ring generalization the PID version
already realizes (plus a possible further `Field K → domain K` weakening to investigate when
upstreaming the PID version). It does **not** rescue *this* ℚ wrapper into YES-add-as-is; it
reinforces that the general PID statement is the right object.

Phase 4.5 (diamond/defeq risk): **n/a — declaration kind is theorem.**

---

### Mathlib search-status: `…evalEval_ψ_eq_zero_of_zsmul_eq_zero_general`

[A] Lean-Finder       (tool unavailable in env)                         n/a — not callable here
[B] Loogle            (tool unavailable in env)                         n/a — not callable here
[C] LeanSearch        (tool unavailable in env)                         n/a — not callable here
[D] Grep mathlib src  `Jacobian.Point|Affine.Point|Projective.Point` ∩ `ψ|Ψ|preΨ|divisionPolynomial`  → **only `DivisionPolynomial/Basic.lean`** (the file that *defines* `ψ`; it contains no group-law↔vanishing lemma). Also greps for `evalEval ψ`, `smulEval`, `zsmul.*ψ`, `torsion.*ψ`, `fromAffine.*ψ` across all of `Mathlib/` → **no hit** linking the point group to division-polynomial vanishing.
[E] Name pattern      `evalEval`, `smulEval`, `eq_zero_of_*smul_eq_zero` in EllipticCurve/  → `evalEval` exists only for `polynomial`/`polynomialX/Y` (Affine/Jacobian Basic); **no `ψ`/torsion vanishing lemma; `smulEval` absent from mathlib**.

Searched for both: the user's ℚ form AND the general `(curveK R K W).ψ n …` form.

Concluded: **not in mathlib.** Mathlib has the *ingredients* — `WeierstrassCurve.ψ`
(`DivisionPolynomial/Basic.lean:401`), the Jacobian point group with
`Jacobian.Point.fromAffine` (`Jacobian/Point.lean:641`), `Jacobian.Z_eq_zero_of_equiv`
(`Jacobian/Basic.lean:187`) — but **not** the bridge `n • P = 0 ⟹ ψ_n(P) = 0`, nor the
underlying `zsmul_eq_smulEval` (the coordinate formula `n • P = ⟦smulEval W x y n⟧`), which is
project-local at `ZSMul.lean:590`. So neither the specialization nor the general form is present.

---

### Call sites — `…_general`

Internal use count: 5 (all within NagellLutz, outside the declaring lines 56/61).
External-to-file callers: 2 distinct files (`GeneralMain.lean`, `GeneralDiscriminant.lean`);
plus 3 self-file uses in `GeneralPrimeOrder.lean` (lines 86, 123, 171).

| Caller file:line                | Usage pattern (one-line excerpt)                                            |
|---------------------------------|------------------------------------------------------------------------------|
| GeneralMain.lean:163            | `have hψ₂ := evalEval_ψ_eq_zero_of_zsmul_eq_zero_general (shortCurveZ A B) hpt 2` |
| GeneralDiscriminant.lean:69     | `have hψ₂ := evalEval_ψ_eq_zero_of_zsmul_eq_zero_general W hns 2 h2Jac`      |
| GeneralPrimeOrder.lean:86       | `have hψ := evalEval_ψ_eq_zero_of_zsmul_eq_zero_general W hns (p : ℤ) htors` |
| GeneralPrimeOrder.lean:123      | `have hψ₄ := evalEval_ψ_eq_zero_of_zsmul_eq_zero_general W hns 4 h4`         |
| GeneralPrimeOrder.lean:171      | `have hψ := evalEval_ψ_eq_zero_of_zsmul_eq_zero_general W hns 2 h2`          |

Inline-derivation grep: the **PID** twin `evalEval_ψ_eq_zero_of_zsmul_eq_zero` (un-suffixed) is
itself called directly in the PID track (`PIDPrimeOrder.lean:119/157/183`, `PIDMain.lean:274`) —
i.e. the *same statement* is consumed via the general decl on the other (duplicated) track. This
is the General*/PID* duplication noted in the project context, not an independent re-derivation.

Signal: K = 5 internal uses → real API *within the project*. But every use is on the ℤ/ℚ
"General" track and is definitionally the PID theorem with `R:=ℤ, K:=ℚ` (`curveQ W` and
`curveK ℤ ℚ W` are the *same* `abbrev` body `W.map (algebraMap ℤ ℚ)`). So the consumers attest to
the *content's* usefulness, not to the wrapper's necessity.

---

### Composition check (Phase 6)

Can `…_general` be derived from mathlib in ≤3 chained calls? **NO.**

Attempt 1: `PID.evalEval_ψ_eq_zero_of_zsmul_eq_zero W hns n htors` — succeeds, but the callee is
**project code, not mathlib**. As a mathlib-composition this fails (the callee doesn't exist in
mathlib).
Attempt 2 (mathlib-only): would need `n • P = 0 ⟹ Z-coord of the Jacobian rep is 0`
(`Z_eq_zero_of_equiv`, mathlib) **composed with** the coordinate identity `n • P = ⟦smulEval …⟧`
relating the abstract scalar action to the explicit `ψ`-built Jacobian point. The latter
(`zsmul_eq_smulEval`, `ZSMul.lean:590`) is a multi-hundred-line strong induction over `n` — **not**
a 1–3 call composition and **not** in mathlib.

Conclusion: **NOT-COMPOSABLE** from mathlib. The bridge is genuine new content (lives in the
project's forked/extended EDS + ZSMul machinery).

---

## Verdict: `LutzNagell.LutzNagellTheorem.evalEval_ψ_eq_zero_of_zsmul_eq_zero_general`

**Category: YES-but-generalise-first**

**Evidence:**
- Literature search (Phase 3): the iff "P is `n`-torsion ⟺ `ψ_n(P)=0`" is textbook (Silverman,
  Washington, Wikipedia). The forward direction needs no field hypotheses.
- Generality analysis (Phase 4b): **STRICTLY NARROWER THAN STANDARD** — this is `R:=ℤ, K:=ℚ` of
  an already-proved general theorem.
- Mathlib search (Phase 5): **not in mathlib** (neither form); mathlib lacks the group-law↔`ψ`
  bridge and the `zsmul_eq_smulEval` coordinate formula.
- Composition check (Phase 6): **NOT-COMPOSABLE** from mathlib.

**Rationale:**

The *content* — group-law torsion forces the division polynomial to vanish — is real, standard,
and absent from mathlib (mathlib defines `ψ` but never connects it to the Jacobian/Affine point
group; the exhaustive grep links the two only inside `DivisionPolynomial/Basic.lean`, which just
defines `ψ`). That makes the underlying result a legitimate mathlib target. However, the gate
forbids YES-add-as-is here for two independent reasons: (a) Phase 4b is STRICTLY NARROWER — the
decl fixes the base to `ℤ` and the point field to `ℚ`, whereas the project *already* contains the
fully general `PID.evalEval_ψ_eq_zero_of_zsmul_eq_zero` over `[CommRing R] [Field K] [Algebra R
K]` (the domain/UFD/FractionRing instances are `omit`ted, proving they're unused); and (b)
Phase 2b flags this as a specialization wrapper whose body is the single term
`PID.evalEval_ψ_eq_zero_of_zsmul_eq_zero W hns n htors`, with no defeq/diamond/API-stability
exemption. So the right mathlib object is the **general** statement, and this ℚ wrapper is a
duplicated-track artifact to drop locally.

**Reason for the generalisation:** LITERATURE-WEAKENING (Phase 4b found the user's form strictly
narrower than both the literature-standard and the project's own already-existing general form).

**Proposed restatement (already exists in-project — upstream THIS, not the wrapper):**
```lean
-- LutzNagell.PID.evalEval_ψ_eq_zero_of_zsmul_eq_zero  (PIDPrimeOrder.lean:62), sorry-free:
theorem evalEval_ψ_eq_zero_of_zsmul_eq_zero
    {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K] (W : WeierstrassCurve R)
    {x y : K} (hns : (W.map (algebraMap R K)).toAffine.Nonsingular x y) (n : ℤ)
    (htors : n • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0) :
    ((W.map (algebraMap R K)).ψ n).evalEval x y = 0 := by
  sorry  -- existing proof: zsmul_eq_smulEval + Jacobian.Point.zero_point + Z_eq_zero_of_equiv
```
Estimated cost of regeneralisation: **CHEAP** — the general theorem is already written and
sorry-free; "generalise first" here means *upstream the general one and delete the ℚ wrapper*.

**Mathlib downstream this enables:**
- First-ever link in mathlib between `WeierstrassCurve.ψ` / `DivisionPolynomial` and the
  `Jacobian.Point` (and Affine) group law — currently those two subtrees are disconnected.
- A reusable handle for torsion computations / Nagell–Lutz-style integrality results over any
  base, which is the structural prerequisite (along with its converse) for the textbook
  "n-torsion ⟺ ψ_n = 0" iff that mathlib is missing.
- Prerequisite: the bridging lemma `zsmul_eq_smulEval` (project `ZSMul.lean:590`, the formula
  `n • P = ⟦smulEval W x y n⟧`) must be upstreamed too — it is the genuinely new infrastructure
  and is itself mathlib-worthy. Group these as one PR series.

**Next action:** run `/generalise` on `LutzNagell.PID.evalEval_ψ_eq_zero_of_zsmul_eq_zero` (test
the Phase-4c `Field K → domain K` weakening), then PR the general theorem together with its
`zsmul_eq_smulEval` prerequisite to `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/`
(or a new `…/DivisionPolynomial/Torsion.lean`). Locally, **delete**
`evalEval_ψ_eq_zero_of_zsmul_eq_zero_general` and repoint its 5 call sites at the PID theorem
(they already pass `W : WeierstrassCurve ℤ`; supply `R := ℤ, K := ℚ` — `curveQ W` is defeq to
`curveK ℤ ℚ W`, so the sites need at most trivial elaboration hints).

---

## Next step

run `/generalise` on the PID twin, then upstream the general theorem + `zsmul_eq_smulEval` as one
PR series; delete the ℚ wrapper and repoint its 5 call sites at the general decl.
