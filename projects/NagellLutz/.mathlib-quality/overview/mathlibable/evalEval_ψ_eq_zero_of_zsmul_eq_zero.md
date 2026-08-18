# /mathlibable report — `LutzNagell.PID.evalEval_ψ_eq_zero_of_zsmul_eq_zero`

## Verdict (TL;DR)

**Category: YES-but-generalise-first.**

The mathematical content — the forward half of the textbook iff "`P` is `n`-torsion ⟺
`ψ_n(P) = 0`": *if `n • P = 0` in the point group, then the `n`-th division polynomial vanishes
at `P`* — is genuinely missing from mathlib and worth having. Mathlib defines `WeierstrassCurve.ψ`
and the Jacobian `Point` group independently but never connects them; this lemma is the first
bridge. It is **not composable** from mathlib in ≤3 calls (its prerequisite `zsmul_eq_smulEval` is
a several-hundred-line induction, project-local, also absent from mathlib).

This PID declaration is *already* the most-general form the project carries (it is the upstream
target named by the sibling assessment of the ℚ wrapper `…_general`). But it is **not yet in the
mathlib-idiomatic shape**: it is phrased over a base ring `R` with an algebra `K` via the
base-change abbreviation `curveK R K W := W.map (algebraMap R K)`, whereas *this lemma's* content
is purely field-level — it never uses `R` except as the source of `curveK R K W`, which is just
"some `WeierstrassCurve K`". The mathlib statement should drop the `R`/`Algebra` packaging and be
stated directly over a field `F` with `W : WeierstrassCurve F` (strictly more general, since not
every `WeierstrassCurve K` base-changes from a chosen `R`). Hence **generalise first**, then PR —
bundled with its `zsmul_eq_smulEval` prerequisite as one series.

---

### Baseline (Phase 0)
- lake build:               not run (project build is stale per task; reasoning from source — task-sanctioned)
- decl `…PID.evalEval_ψ_eq_zero_of_zsmul_eq_zero`: ✓ resolved at `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDPrimeOrder.lean:62`
- qualified name (VERIFIED from source): `LutzNagell.PID.evalEval_ψ_eq_zero_of_zsmul_eq_zero`
  (namespaces `namespace LutzNagell` (l.24) then `namespace PID` (l.25); base name `evalEval_ψ_eq_zero_of_zsmul_eq_zero`)
- kind:                      theorem
- has sorry:                 no (4-line tactic proof, lines 67–71)
- module docstring summary:  prime-order torsion integrality for Weierstrass curves over UFDs (generalises `GeneralPrimeOrder` from ℤ/ℚ to a UFD `R` with fraction field `K`).

---

### Statement (Phase 1)

`evalEval_ψ_eq_zero_of_zsmul_eq_zero` states: for `W : WeierstrassCurve R` over `[CommRing R]`
with `K` a field and `[Algebra R K]`, writing `curveK R K W = W.map (algebraMap R K)` for the
base-changed curve over `K`, if `(x, y)` is a nonsingular `K`-point and `n • P = 0` in the
**Jacobian point group** (`P = Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)`), then the
`n`-th division polynomial of `curveK R K W` evaluates to zero at `(x, y)`:
`((curveK R K W).ψ n).evalEval x y = 0`.

This is the forward direction of the classical division-polynomial characterization of torsion.

Signature (Lean side, with omits applied):
```
{R : Type*} [CommRing R]                         -- [IsDomain R] [UniqueFactorizationMonoid R] OMITTED
{K : Type*} [Field K] [Algebra R K]              -- [DecidableEq K] [IsFractionRing R K]     OMITTED
(W : WeierstrassCurve R)
{x y : K} (hns : (curveK R K W).toAffine.Nonsingular x y) (n : ℤ)
(htors : n • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0) :
((curveK R K W).ψ n).evalEval x y = 0
```
The `omit [IsDomain R] [UniqueFactorizationMonoid R] [DecidableEq K] [IsFractionRing R K]` on
line 60 proves the only typeclasses the proof actually needs are `CommRing R`, `Field K`,
`Algebra R K`.

Proof (lines 67–71), 4 lines:
1. `heval := zsmul_eq_smulEval (curveK R K W) hns n` — the coordinate formula `n • P = ⟦smulEval⟧`.
2. `hzero := Jacobian.Point.zero_point` — the point at infinity is `⟦![1,1,0]⟧`.
3. rewrite `htors` through `Jacobian.Point.ext_iff`, `heval`, `hzero`.
4. `(Jacobian.Z_eq_zero_of_equiv (Quotient.exact htors)).mpr rfl` — the `Z`-coordinate (= `ψ_n`) is 0.

---

### Size classification (Phase 2a)

Verdict: SMALL-to-MEDIUM (treated as a real lemma, not a wrapper).
Reason: unlike its ℚ twin `…_general` (a one-term re-export), THIS is the substantive lemma —
a 4-line tactic proof that actually performs the bridge (invokes `zsmul_eq_smulEval`, transports
through `Point.ext_iff`, applies `Z_eq_zero_of_equiv`). It is consumed by every torsion-integrality
result in both the PID and General tracks. It is the upstream target. So Phase-2b's
"specialization-wrapper" negative signal does **not** apply here (that was the ℚ wrapper's problem).

### One-line check (Phase 2b)

Kind is `theorem` → formal def gate `n/a`. The body is **not** a single re-export term; it is a
genuine 4-line derivation. No specialization-wrapper signal. Carried into Phase 7: this is the real
content, biasing toward YES — modulo the generality reshape below.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                           | Hit? | Standard form found              | Notes |
|----|----------------------------------|-------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific/forward form)| EC division polynomial `ψ_n` torsion point vanishes; mathlib `WeierstrassCurve` ψ Jacobian      | yes  | "ψ_n used to determine when a point is n-torsion"; mathlib has ψ but no group↔ψ link | math.iisc mathlib docs; MIT 18.783 Lec 6 (isogeny kernels/division polys); Poonen curvetorsion |
|  2 | WebSearch (iff form)             | EC division polynomial `ψ_n(P)=0` ⟺ `P` n-torsion, Silverman                                    | yes  | **"P is n-torsion ⟺ ψ_n(P)=0"** — textbook | Wikipedia "Division polynomials" (ψ_n encodes E[n]); Silverman AEC GTM 106 |
|  3 | WebSearch (mathlib status)       | mathlib zsmul Jacobian Point ψ_n bridge                                                          | yes  | mathlib `WeierstrassCurve`/ψ exist; **no surfaced lemma** linking `n•P` to ψ_n | confirms the connector is not (publicly) in mathlib |
|  4 | ChatGPT MCP                      | standard form + generality + base-ring of "ψ_n=0 ⟺ n-torsion"                                   | n/a  | (MCP down per task env)          | fell back to WebSearch ×3 + local mathlib grep + textbook knowledge, per task instructions |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/`, `refs/NagellLutz/`                      | n/a  | (dirs absent)                    | neither directory exists in this checkout |
|  6 | Sibling /mathlibable reports     | `…_general`, `integrality_of_order_four_general`, `bounded_den_of_order_two_general` (.md)       | yes  | **named THIS decl as the upstream target** | `evalEval_ψ_eq_zero_of_zsmul_eq_zero_general.md` → YES-but-generalise-first → "upstream PID twin" |
|  7 | nLab / Stacks                    | division polynomial / EC torsion                                                                 | n/a  | neither develops division polynomials | classical AG/NT, outside nLab(categorical)/Stacks(scheme-theoretic) scope |
|  8 | recent arXiv (≤5 yr)             | division polynomials / explicit valuations / torsion over general bases (1108.3051; Stange)     | yes  | reaffirms ψ_n ↔ torsion; modern work over general bases | arXiv 1108.3051 (integral pts & explicit valuations of div. polys) |

### Literature summary (Phase 3)

Concept identified as: **the division-polynomial characterization of torsion** — "a point `P` is
`n`-torsion iff `ψ_n(P) = 0`" (Silverman *AEC*; Washington *Elliptic Curves* §3.2; Wikipedia
"Division polynomials"). This decl proves the **forward direction** `n•P = O ⟹ ψ_n(P) = 0`.
Sources agree on the standard form: yes (the iff is textbook; ψ_n "encodes the whole n-torsion").
Most general standard form: the coordinate identity `nP = (φ_n/ψ_n², ω_n/ψ_n³)` and hence the
forward vanishing implication hold over **any field** where the group law is defined (and the
underlying polynomial identity over any comm. ring); the iff is usually phrased over a field /
algebraically closed field.
Generality dimensions where literature varies: base field — ℚ/number fields (Nagell–Lutz) →
arbitrary fields (Silverman/Washington). For *this forward implication*, the maximally general
realizable form (given mathlib's field-only Jacobian point group) is **an arbitrary field `F`**.
Disagreement with the literature: none. The decl is mathematically correct.

---

### Generality analysis (Phase 4b)

Literature-standard form: forward implication over **an arbitrary field `F`**, stated directly on
`W : WeierstrassCurve F`.

The decl's *actual* hypotheses (after `omit`) are `CommRing R`, `Field K`, `Algebra R K`, and the
curve enters only as `curveK R K W = W.map (algebraMap R K) : WeierstrassCurve K`. The proof
(lines 67–71) touches **only** the field-`K` curve `curveK R K W` — `zsmul_eq_smulEval`,
`zero_point`, `Z_eq_zero_of_equiv` all act on the `WeierstrassCurve K`. `R` is never used except as
the source of the base change. Therefore:

| # | Parameter / hypothesis                  | Current Lean form                                  | Standard / idiomatic form                  | Weaker form exists? | Reason |
|---|------------------------------------------|----------------------------------------------------|--------------------------------------------|---------------------|--------|
| 1 | base packaging `R` + `[Algebra R K]`     | `W : WeierstrassCurve R`, curve = `curveK R K W`   | `W : WeierstrassCurve F` directly          | **YES**             | the lemma is field-level; `R`/`Algebra` is a needless costume from the Nagell–Lutz application. Plain-field is **strictly more general** (not every `WeierstrassCurve K` base-changes from a chosen `R`) |
| 2 | point field `[Field K]`                  | `Field K`                                          | `Field F`                                  | NO (already general)| see 4c — **not** weakenable to a domain: mathlib's Jacobian `Point` group is **defined only over a field** |
| 3 | domain/UFD/FractionRing on `R`           | OMITTED                                            | absent                                     | —                   | already gone (proven unused by `omit`) |
| 4 | `hns`, `n`, `htors`, conclusion          | maximal                                            | identical                                  | —                   | already maximally general |

### Generality verdict (Phase 4b)

Current form is: **SLIGHTLY NARROWER / NON-IDIOMATIC** vs. the standard form — not because of a
missing weakening of mathematical strength on the *field* (that is already maximal), but because
the `R`-with-`Algebra` packaging is an *unnecessary specialization* of the natural plain-field
statement (it can only express base-changed curves). Within the project this PID form is the
most-general one (correctly identified as the upstream target by the `…_general` report); for
mathlib it should be **reshaped to the plain-field statement**.
Number of weakening/idiom opportunities found: 1 substantive (drop `R`/`Algebra`).
Cost of reshape: **CHEAP** — the proof is verbatim reusable; only the signature changes
(`curveK R K W` ↦ `W : WeierstrassCurve F`, drop `R`, `[Algebra R K]`). The project keeps its
`curveK`-flavoured corollary by instantiating `F := K`, `W := curveK R K W` (defeq).

### Modern-idiom check (Phase 4c)

| #  | Question                                                              | Applies? | Proposed reformulation | Downstream |
|----|----------------------------------------------------------------------|----------|------------------------|------------|
|  1 | bundled "let W be over R with Algebra R K" preamble → drop to a field?| **yes**  | `W : WeierstrassCurve F` over `[Field F]` | composes with every EC-over-a-field instantiation; the project's `R/K` use is the special case `F := K` |
|  5 | field-specific → weaken typeclass (domain/(semi)ring)?               | **no**   | `Field F` cannot become a domain | mathlib's Jacobian `Point` `AddCommGroup` (`Jacobian/Point.lean:83`: `{W : Jacobian F} [Field F]`) and `zsmul_eq_smulEval` (`ZSMul.lean:584`: `[Field F]`) are **field-only**. The sibling report's speculative "Field K → domain" is **not actionable** at mathlib's current state — the point group does not even exist over a non-field |
|  2,3,4,6,7 | sequences→filters / universal property / substructure / higher-cat / concrete index | no | — | purely algebraic field-level identity |

### Modern-idiom verdict (Phase 4c)

Idiom available: **yes** — restate directly over a field `F` (drop the `R`/`Algebra` base-change
packaging). This is the only real reshape, and it is a genuine (mild) generalization, so it gates
the verdict to **generalise-first** rather than add-as-is. The `Field → domain` lever is closed by
mathlib's field-only Jacobian group.

Phase 4.5 (diamond/defeq risk): **n/a — declaration kind is theorem.**

---

### Mathlib search-status: `…PID.evalEval_ψ_eq_zero_of_zsmul_eq_zero`

[A] Lean-Finder       (mathlib index tool not callable in this env)              n/a
[B] Loogle            (mathlib index tool not callable in this env)              n/a
[C] LeanSearch        (mathlib index tool not callable in this env)              n/a
[D] Grep mathlib src  (`.lake/packages/mathlib`, toolchain v4.32.0-rc1, rev 09b373db6e24):
      - `grep -rn "smulEval\|zsmul_eq_smul\|smulRing\|ringEval"  Mathlib/`  → **NO hit**
        (only `Mathlib/Algebra/Group/Defs.lean:1045 zpow_eq_pow`'s `to_additive` alias `zsmul_eq_smul`,
        unrelated). The entire `smulEval`/`zsmul_eq_smulEval` machinery is **absent from mathlib**.
      - `ls Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/`  → only `Basic.lean`, `Degree.lean`
        (no `Torsion.lean`, no point-group link).
      - `grep -rn "n • P\|torsion"` in `DivisionPolynomial/*.lean`  → only doc-comment keyword hits
        ("…, torsion point" in `Basic.lean:91`, `Degree.lean:50`); **no lemma**.
      - Jacobian `Point` group uses `nsmul := nsmulRec`, `zsmul := zsmulRec` (`Jacobian/Point.lean:589–590`)
        — the **generic recursive** scalar action, with **no closed-form `ψ_n` connection**.
[E] Name pattern      `evalEval`, `smulEval`, `eq_zero_of_*smul_eq_zero` in `EllipticCurve/`  →
      `evalEval` exists only for `polynomial`/`polynomialX/Y` (Affine/Jacobian Basic); **no ψ/torsion
      vanishing lemma; `smulEval` absent**.

Searched for both: the user's `R/K` `curveK …` form AND the plain-field `W : WeierstrassCurve F` form.

Concluded: **NOT in mathlib (neither form).** Mathlib has the *ingredients* — `WeierstrassCurve.ψ`
(`DivisionPolynomial/Basic.lean`), the Jacobian point group with `Jacobian.Point.fromAffine`
(`Jacobian/Point.lean:641`), `Jacobian.Point.zero_point` (`Point.lean:389`), `Jacobian.Z_eq_zero_of_equiv`
(`Jacobian/Basic.lean:187`) — but **not** the bridge `n • P = 0 ⟹ ψ_n(P) = 0`, and crucially **not**
the underlying coordinate formula `zsmul_eq_smulEval` (`n • P = ⟦smulEval W x y n⟧`), which is
project-local at `ZSMul.lean:590` (authored by Junyan Xu, 2024).

---

### Call sites — `…PID.evalEval_ψ_eq_zero_of_zsmul_eq_zero`

Internal use count: ≥7 across the project.
- `GeneralPrimeOrder.lean:61` — the ℚ wrapper `…_general` is literally `PID.evalEval_ψ_eq_zero_of_zsmul_eq_zero W hns n htors`.
- `PIDPrimeOrder.lean:119` — `x_isInteger_of_odd_prime_torsion_squarefree` (odd-prime integrality).
- `PIDPrimeOrder.lean:157` — `integrality_of_order_four_squarefree` (order-4 integrality, via `ψ_four`).
- `PIDPrimeOrder.lean:183` — `den_dvd_of_order_two` (order-2 denominator bound, via `ψ_two`).
- `PIDMain.lean:274` (per sibling report) — Nagell–Lutz assembly.
- plus the 5 `…_general` call sites that route through the ℚ wrapper (`GeneralMain.lean:163`,
  `GeneralDiscriminant.lean:69`, `GeneralPrimeOrder.lean:86/123/171`).

Signal: **K ≫ 5 genuine consumers** → this is real, load-bearing API. It is the single funnel
through which *all* Nagell–Lutz torsion-integrality results (orders 2, 4, and odd primes; both
tracks) extract "ψ_n vanishes" from a torsion hypothesis. Strong evidence of mathlib value.

---

### Composition check (Phase 6)

Can it be derived from mathlib in ≤3 chained calls? **NO.**

Attempt 1 (mathlib-only forward path): `n • P = 0`
  → `Quotient.exact`/`Point.ext_iff` to get the Jacobian-rep equivalence (mathlib, 1 step)
  → `Jacobian.Z_eq_zero_of_equiv` to learn the `Z`-coordinate of the rep is `0` (mathlib, 1 step)
  → **but** the `Z`-coordinate of `(n • P).point` is only known to equal `ψ_n(x,y)` via the
    coordinate identity `n • P = ⟦smulEval W x y n⟧` (`smulEval`'s component 2 is `evalEval x y (W.ψ n)`).
    That identity is `zsmul_eq_smulEval` — **not in mathlib**, and itself a several-hundred-line
    strong/even-odd induction on `n` over the universal division-polynomial ring (`ZSMul.lean`,
    Junyan Xu). This is **not** a 1–3-call composition and **not** present.

Conclusion: **NOT-COMPOSABLE** from mathlib. The missing link `zsmul_eq_smulEval` is genuine new
infrastructure (the project's forked/extended EDS + ZSMul machinery), itself mathlib-worthy.

---

## Verdict: `LutzNagell.PID.evalEval_ψ_eq_zero_of_zsmul_eq_zero`

**Category: YES-but-generalise-first**

**Evidence:**
- Literature (Phase 3): "P is `n`-torsion ⟺ `ψ_n(P)=0`" is textbook (Silverman, Washington,
  Wikipedia). This decl proves the forward half; over a field needs no further hypotheses.
- Generality (Phase 4b/4c): the field `K` is already maximal (mathlib's Jacobian group is
  field-only, so `Field → domain` is *not* available), **but** the `R`-with-`[Algebra R K]`
  base-change packaging (`curveK R K W = W.map (algebraMap R K)`) is a **needless specialization**
  of the natural, strictly-more-general plain-field statement over `W : WeierstrassCurve F`.
- Mathlib search (Phase 5): **not in mathlib** (neither form). Mathlib defines `ψ` and the Jacobian
  `Point` group but never links them; `zsmul_eq_smulEval` (the coordinate formula) is also absent.
- Composition (Phase 6): **NOT-COMPOSABLE** in ≤3 mathlib calls (the `n•P = ⟦smulEval⟧` step is a
  large project-local induction, not in mathlib).

**Rationale:**

The content — group-law torsion forces the division polynomial to vanish — is real, standard, and
absent from mathlib (the `ψ`/`DivisionPolynomial` subtree and the `Jacobian.Point` subtree are
currently disconnected; the exhaustive grep links them only inside `DivisionPolynomial/Basic.lean`,
which merely defines `ψ`). With ≥5 genuine in-project consumers it is clearly mathlib-worthy. The
gate withholds YES-add-as-is for one reason: Phase 4c finds a real (if mild) generalisation — *this
lemma is field-level* and should be stated directly over a field `F` on `W : WeierstrassCurve F`,
dropping the `R`/`Algebra` costume that the Nagell–Lutz application imposes (the proof, lines 67–71,
uses `R` nowhere but as the source of the base change; the plain-field form is strictly more general
because not every `WeierstrassCurve K` base-changes from a chosen `R`). Hence **generalise first**.

**Reason for the generalisation:** IDIOM/PACKAGING-WEAKENING (Phase 4c) — replace the bundled
`R`-base + `[Algebra R K]` preamble with a direct field hypothesis; strictly more general and
mathlib-idiomatic. (NOT a field→domain weakening — that is blocked by mathlib's field-only group.)

**Proposed restatement (mathlib-idiomatic, plain field):**
```lean
open WeierstrassCurve Polynomial in
/-- If `n • P = 0` in the Jacobian point group, then `ψ_n(x, y) = 0`. -/
theorem evalEval_ψ_eq_zero_of_zsmul_eq_zero
    {F : Type*} [Field F] (W : WeierstrassCurve F)
    {x y : F} (hns : W.toAffine.Nonsingular x y) (n : ℤ)
    (htors : n • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0) :
    (W.ψ n).evalEval x y = 0 := by
  have heval := zsmul_eq_smulEval W hns n
  have hzero := Jacobian.Point.zero_point (W' := W.toJacobian)
  rw [Jacobian.Point.ext_iff] at htors
  rw [heval, hzero] at htors
  exact (Jacobian.Z_eq_zero_of_equiv (Quotient.exact htors)).mpr rfl
```
(The project's existing `R/K` corollary is then `F := K`, `W := curveK R K W` — defeq, free.)
Estimated cost: **CHEAP** — proof verbatim; signature edit only.

**Mathlib downstream this enables:**
- The **first link in mathlib** between `WeierstrassCurve.ψ` / `DivisionPolynomial` and the
  Jacobian (and Affine) `Point` group law — currently disjoint subtrees.
- A reusable handle for torsion computations and Nagell–Lutz-style integrality over any field; the
  structural prerequisite (with its converse) for the missing textbook iff "n-torsion ⟺ ψ_n = 0".
- **Hard prerequisite to upstream together:** `WeierstrassCurve.zsmul_eq_smulEval` (project
  `ZSMul.lean:590`, the coordinate formula `n • P = ⟦smulEval W x y n⟧`, Junyan Xu 2024) — the
  genuinely new infrastructure, itself mathlib-worthy. Group these as one PR series, likely a new
  `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Torsion.lean` (or the existing
  Jacobian `Point` file alongside `zsmul_eq_smulEval`).

**Relation to the sibling assessment:** the ℚ wrapper `…_general`'s report
(`evalEval_ψ_eq_zero_of_zsmul_eq_zero_general.md`) was rated YES-but-generalise-first and named
**this PID decl** as the upstream target. This report refines that: the upstream object is not the
`R/K` PID statement verbatim either, but its **plain-field reshape** above — still
YES-but-generalise-first, one notch further generalised.

---

## Next step

run `/generalise` on `LutzNagell.PID.evalEval_ψ_eq_zero_of_zsmul_eq_zero` to reshape it to the
plain-field form `{F} [Field F] (W : WeierstrassCurve F) …` above (recover the `curveK` corollary
by instantiation), then upstream it **together with its `zsmul_eq_smulEval` prerequisite** as one
PR series to `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/`. Drop the ℚ wrapper
`…_general` and repoint all call sites at the reshaped theorem.
