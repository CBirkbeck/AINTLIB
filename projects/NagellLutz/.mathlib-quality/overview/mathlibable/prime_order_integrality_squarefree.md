# /mathlibable report — `LutzNagell.PID.prime_order_integrality_squarefree`

_Assessment date: 2026-06-22. Mathlib pin: `d90090f` (Lean v4.31.0-rc2), read directly from
`.lake/packages/mathlib`. Local lake build NOT re-run (environment build stale per task brief);
reasoned from the Lean source + the vendored mathlib tree._

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task brief); reasoned from source + `.lake/packages/mathlib`.
- decl resolved:            ✓ `theorem prime_order_integrality_squarefree` at
  `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDPrimeOrder.lean:202` (theorem head; `:= by` body
  opens at line 207).
- kind:                      theorem
- has sorry:                 no (body is a 4-line wrapper; no `sorry`/`admit`).
- true qualified name:       **`LutzNagell.PID.prime_order_integrality_squarefree`**. The file opens
  `namespace LutzNagell` then `namespace PID` (lines 23–24), so the parsed brief name
  `LutzNagell.PID.prime_order_integrality_squarefree` is CONFIRMED correct.
- module docstring summary:  "Prime-order torsion integrality for Weierstrass curves over UFDs" —
  generalization of `GeneralPrimeOrder.lean` from `ℤ/ℚ` to a UFD `R` with fraction field `K`. When
  `(p : R)` is squarefree ("p does not ramify in R"), torsion points of odd prime order `p` have integral
  coordinates; more generally every prime factor of the denominator must appear with multiplicity ≥ 2 in
  the division polynomial's leading coefficient.

---

### Statement (Phase 1)

Section variables (`PIDPrimeOrder.lean:29–31`):
`{R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]`,
`{K : Type*} [Field K] [DecidableEq K] [Algebra R K] [IsFractionRing R K]`,
`(W : WeierstrassCurve R)`. The decl carries `omit [DecidableEq K]`.

```
theorem prime_order_integrality_squarefree
    {x y : K} (hns : (curveK R K W).toAffine.Nonsingular x y)
    {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (htors : (p : ℤ) • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0)
    (hsf : Squarefree (p : R)) :
    (IsLocalization.IsInteger R x) ∧ IsLocalization.IsInteger R y
```

Mathematics: Let `W` be a Weierstrass curve over a UFD `R` (fraction field `K`), `P = (x, y)` a
nonsingular affine `K`-point. Let `p` be an odd prime with `p · P = 0` in the (Jacobian-model) point
group, and suppose the image of `p` in `R` is squarefree. Then both coordinates `x, y` are integral
(lie in the image of `R → K`). This is the **single-prime-order integrality step** of the Nagell–Lutz
theorem, in the squarefree-prime / UFD generalization.

Proof shape (4 substantive lines, `PIDPrimeOrder.lean:207–211`): pure composition —
1. `x_isInteger_of_odd_prime_torsion_squarefree W hns hp hodd htors hsf` gives `x ∈ R`;
2. destructure to `⟨x₀, hx₀⟩`;
3. `y_isInteger_of_x_isInteger_on_curve W (curveK_equation_iff …).mp hns.left hx₀` gives `y ∈ R`.
All three callees are **project-local** (`x_isInteger_of_odd_prime_torsion_squarefree`,
`y_isInteger_of_x_isInteger_on_curve` in this same file; `curveK_equation_iff` in `PIDCurve.lean`). No
mathlib lemma is invoked directly in this wrapper.

Where the real content lives (one level down):
- `x_isInteger_of_odd_prime_torsion_squarefree` (same file, l.113): `p·P=0` ⇒ `ψ_p(x,y)=0`
  (`evalEval_ψ_eq_zero_of_zsmul_eq_zero`), then `ψ_p = preΨ_p` for odd `p` (`evalEval_ψ_odd`,
  base-change via `map_preΨ`), so `x` is a root of `preΨ_p ∈ R[X]`; its leading coefficient is
  `(p : R)` (project lemma `leadingCoeff_preΨ`), squarefree by hypothesis; conclude via
  `isInteger_of_root_squarefree_leading_coeff`.
- `isInteger_of_root_squarefree_leading_coeff` (same file, l.82): the genuinely-new abstract core.
  `den_dvd_of_is_root` (mathlib rational-root theorem) gives `den(x) ∣ leadingCoeff`; if `den(x)` were
  a non-unit it would have a prime factor `q` (UFD: `WfDvdMonoid.exists_irreducible_factor` +
  `irreducible_iff_prime`); squarefreeness forbids `q² ∣ den`, but the curve denominator lemma
  `den_no_simple_prime_factor_of_on_curve` (project, `PIDDenominators.lean`) forbids `q ∣ den` with
  `q² ∤ den` — contradiction; hence `den` is a unit, so `x ∈ R` via `isInteger_of_isUnit_den`.

The `Squarefree (p : R)` hypothesis is a **project bookkeeping device**: it is exactly the algebraic
condition that makes the "no simple prime factor" denominator lemma collapse the denominator to a unit
without invoking reduction theory. The classical/literature statement (over `ℚ`, or over a Dedekind/DVR
base) instead phrases the hypothesis via **good reduction / `p ∤ Δ`** and the **formal group / reduction
map** (see Phase 3).

---

### Size classification (Phase 2a)

Verdict: **BIG** — it is a load-bearing proof step of a **person-named theorem** (Nagell–Lutz). It is a
`theorem` (not a new structure), and its body is a 4-line wrapper, but by the skill's "named after a
person ⇒ treat as BIG, run the wide literature sweep" criterion it is BIG. Its sole call site is
`PIDMain.lean:98`, inside the private helper `integrality_of_odd_prime_factor` that assembles the
full-order PID Nagell–Lutz integrality theorem `lutz_nagell_integrality_pid`.

(Literature width run EXHAUSTIVE regardless of BIG/SMALL.)

### One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure`; one-line definitional check n/a. The body is ≈4
substantive lines of pure composition over two project lemmas. The mathematical content is NOT in this
wrapper — it is in `x_isInteger_of_odd_prime_torsion_squarefree` →
`isInteger_of_root_squarefree_leading_coeff` one and two levels down.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel        | Query                                                                                   | Hit? | Standard form found                                  | Notes |
|----|----------------|-----------------------------------------------------------------------------------------|------|------------------------------------------------------|-------|
| 1  | WebSearch      | mathlib Nagell-Lutz theorem elliptic curve torsion points integral coordinates formalized | partial | Classical Nagell–Lutz (Silverman VIII.7; Alpoge "Nagell-Lutz, quickly") | No evidence of a mathlib formalization; results are math expositions only. |
| 2  | WebSearch      | Nagell-Lutz torsion integral coordinates squarefree division polynomial leading coefficient | partial | Same classical statement; standard proof via reduction/formal group | No source states the "squarefree `(p:R)`" hypothesis form — confirms it is a project device, not literature-standard. |
| 3  | WebSearch (incidental) | (returned) arXiv 2509.07524 "Nagell-Lutz Theorem for Imaginary Quadratic Fields with Class Number One" | yes | Generalization of NL to imaginary quadratic fields, class number 1 | Independent confirmation that the **UFD / class-number-1 generalization is a genuine research-level statement**, not a routine corollary — and recent (2025), not in mathlib. |
| 4  | grep mathlib   | `Nagell` / `NagellLutz` / `nagell_lutz` across `.lake/packages/mathlib/Mathlib`           | no   | —                                                    | Mathlib has NO Nagell–Lutz theorem of any form. |
| 5  | grep mathlib   | `IsInteger` / `integral` in `Mathlib/AlgebraicGeometry/EllipticCurve/**`                 | no (wrong sense) | `Reduction.lean`, `DivisionPolynomial/Degree.lean`, `Affine/Point.lean` | The `IsInteger` hits concern **integral models / reduction**, never torsion-point integrality. No torsion ↦ `IsInteger` result. |
| 6  | grep mathlib   | `Squarefree` in `Mathlib/AlgebraicGeometry/EllipticCurve/**`                             | no   | —                                                    | No squarefree-coefficient integrality result for elliptic curves. |
| 7  | grep mathlib   | `Squarefree … leadingCoeff` / `leadingCoeff … Squarefree` across all of mathlib          | no   | —                                                    | The abstract core "squarefree leading coeff ⇒ integral root on the curve" has no mathlib analog. |
| 8  | ChatGPT MCP    | (unavailable this session — server down per task brief)                                 | —    | —                                                    | Fallback: WebSearch (#1–3) + direct mathlib grep (#4–7) + reading the proof's leaf lemmas. |

Channels covered: WebSearch ✓, local mathlib `grep`/source read ✓, project references (module docstrings
cite Nagell, Lutz, and Alpoge's "Nagell-Lutz, quickly") ✓. ChatGPT MCP down — substituted with the
arXiv generalization paper + exhaustive mathlib grep, which is sufficient to settle presence/absence.

**Literature-standard form (Phase 3 anchor):** Nagell–Lutz integrality — *a finite-order point on an
elliptic curve over `ℚ` (resp. a number field / Dedekind base with the appropriate reduction hypotheses)
has integral coordinates* — proved via the **reduction map and formal group**: the kernel of reduction
mod a prime of good reduction is torsion-free in the residue characteristic, so prime-order torsion
injects into the (good) reduction and cannot have a pole. The hypothesis is **good reduction / `p ∤ Δ`**,
not "`(p:R)` squarefree". The squarefree hypothesis is a clever project substitute that lets the
denominator-divisibility argument run **without** building reduction/formal-group theory.

---

### Mathlib five-method exhaustive search (Phase 2c)

1. exact-name / `grep` for the decl name and obvious synonyms in mathlib — **absent**.
2. statement-shape grep (`torsion`/`IsOfFinAddOrder` ↦ `IsInteger`) in EllipticCurve namespace — **absent**.
3. structural: division-polynomial machinery (`preΨ`, `ψ`, `Ψ₂Sq`, `leadingCoeff_preΨ`) — mathlib HAS
   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/{Basic,Degree}.lean` (this project FORKS
   the `ψ`/`preΨ` API and EDS), but mathlib has NO integrality/Nagell–Lutz consequence built on it.
4. rational-root corollaries: mathlib HAS `den_dvd_of_is_root`, `isInteger_of_is_root_of_monic`,
   `isInteger_of_isUnit_den` (`Mathlib/RingTheory/Polynomial/RationalRoot.lean`) — these are the generic
   building blocks the project's core lemma composes, but the elliptic-specific "squarefree leading coeff
   ⇒ integral" packaging is not present.
5. downstream/`exact?`-style: no single mathlib lemma yields `(htors, hsf) ⊢ IsInteger x ∧ IsInteger y`.

Conclusion of Phase 2c: **mathlib does not contain this theorem, nor a strictly more general one.**

---

### Generality analysis (Phase 3)

- The decl is already a generalization of the `ℚ` version (`prime_order_integrality_general`,
  `GeneralPrimeOrder.lean:149`) to an arbitrary UFD base `R`. Good direction.
- But it is **NOT the literature-maximal form**. The mathlib-canonical Nagell–Lutz integrality would be
  the **reduction-theoretic** statement over a Dedekind/DVR base (hypothesis: good reduction at the
  relevant prime, i.e. residue characteristic ∤ order), proved via the reduction map + formal group.
  The sibling report `lutz_nagell_integrality_pid.md` already records this target verbatim:
  `WeierstrassCurve.torsion_isInteger_of_goodReduction` over `[IsDedekindDomain R]`, blocked on mathlib
  lacking **elliptic-curve reduction maps** and **formal-group torsion** (cost: EXPENSIVE).
- The `Squarefree (p : R)` hypothesis is **non-standard** and **stronger/awkward** relative to the
  literature `p ∤ Δ` condition; it is a project-internal device to avoid reduction theory. A mathlib
  reviewer would want the hypothesis re-expressed in reduction terms, which changes the proof entirely.
- Mechanical weakenings (drop `DecidableEq K`, relax `UniqueFactorizationMonoid` → `IsDedekindDomain`)
  do NOT reach the canonical form: relaxing UFD to Dedekind **breaks this proof** (the denominator
  argument uses unique factorization of elements, not of ideals), so it is a genuine re-proof, not a
  parameter loosening.

This places the decl squarely in the established pattern of its sibling steps, which were assessed as
**BORDERLINE-needs-human** precisely because they are genuine, non-trivially-composable Nagell–Lutz proof
steps stated in a **project-bespoke (squarefree/UFD) form** that does not yet match mathlib's eventual
reduction-theoretic API: cf. `x_integral_of_odd_prime_torsion_general` →
**BORDERLINE-needs-human** ("a genuine, non-trivially-composable proof step of the Nagell–Lutz theorem").
This decl is the *direct UFD analog* of that one (it even calls the UFD analog
`x_isInteger_of_odd_prime_torsion_squarefree`), so it inherits the same verdict.

---

### Composition check (Phase 4) — can ≤3 mathlib calls give it?

NO. The wrapper itself is a 2-call composition, but **both calls are project lemmas**, and the inner
content is irreducibly elliptic-specific:
- `x_isInteger_of_odd_prime_torsion_squarefree` requires the **division-polynomial torsion bridge**
  (`p·P = 0 ⇒ ψ_p(x,y) = 0`, odd-`p` reduction `ψ_p = preΨ_p`, leading-coeff `= (p:R)`) — none of which
  exists as a mathlib consequence; the project had to fork and extend mathlib's `DivisionPolynomial` API.
- `isInteger_of_root_squarefree_leading_coeff` is a bespoke combination of mathlib's `den_dvd_of_is_root`
  with the **project** denominator lemma `den_no_simple_prime_factor_of_on_curve`
  (`PIDDenominators.lean`) — the latter is the substantive elliptic input and is NOT in mathlib.
- `y_isInteger_of_x_isInteger_on_curve` is a small monic-root argument (composable from mathlib's
  `isInteger_of_is_root_of_monic`) — but it is the *only* genuinely composable piece, and it alone does
  not give the theorem.

So this is NOT a "mathlib primitives compose to it in ≤3 calls" situation. It depends on a project-built
elliptic torsion/denominator API that mathlib lacks. (Hence it is **not** NO-composable-from-mathlib.)

---

## Five-bucket verdict

### **BORDERLINE-needs-human**

**Why not the other buckets:**
- **NO-mathlib-has-it** — rejected: exhaustive search (Phases 2c, 4–7 of the table) shows mathlib has
  neither Nagell–Lutz nor any torsion ↦ `IsInteger` result; the recent UFD/class-number-1 generalization
  is a 2025 arXiv paper, not in mathlib.
- **NO-composable-from-mathlib** — rejected: the proof rests on a **project-specific** division-polynomial
  torsion bridge and curve-denominator lemma (`den_no_simple_prime_factor_of_on_curve`,
  `x_isInteger_of_odd_prime_torsion_squarefree`) that mathlib does not provide; ≤3 mathlib calls do not
  reconstruct it.
- **YES-add-as-is** — rejected: the `Squarefree (p : R)` hypothesis is a **non-standard project device**,
  not the literature/mathlib-canonical good-reduction (`p ∤ Δ`) hypothesis; shipping this exact statement
  to mathlib would import a bespoke formulation a reviewer would push back on.
- **YES-but-generalise-first** — rejected as the *primary* verdict (though adjacent): the canonical
  generalization (reduction-theoretic Nagell–Lutz over a Dedekind/DVR base) is **not a mechanical weakening**
  — it requires a different proof and substantial missing mathlib infrastructure (elliptic-curve reduction
  maps + formal-group torsion; cost EXPENSIVE per `lutz_nagell_integrality_pid.md`). Because reaching the
  mathlib-target form is a research/infrastructure decision, not an auto-applicable parameter loosening,
  this needs a human call — matching every sibling "genuine NL proof step" on this track.
- **BORDERLINE-needs-human** — SELECTED: a genuine, non-trivially-composable intermediate of a
  person-named theorem (Nagell–Lutz), correct and useful **within the project** (it powers
  `lutz_nagell_integrality_pid` via `PIDMain.integrality_of_odd_prime_factor`), but stated in a
  project-bespoke squarefree/UFD form whose mathlib-canonical counterpart is reduction-theoretic and
  blocked on missing infrastructure. The bucket is consistent with its direct ℚ-analog
  `x_integral_of_odd_prime_torsion_general` (also BORDERLINE-needs-human).

**Rationale (≤20 words):** Genuine non-composable Nagell–Lutz proof step; mathlib lacks it, but bespoke
squarefree/UFD hypothesis isn't the canonical reduction-theoretic form — human call.

## Next step

If/when this track is upstreamed: do **not** PR this statement verbatim. Treat it as the per-prime,
squarefree-case instance of the reduction-theoretic Nagell–Lutz target recorded in
`lutz_nagell_integrality_pid.md` (`torsion_isInteger_of_goodReduction` over `[IsDedekindDomain R]`). The
prerequisite is mathlib first acquiring elliptic-curve reduction maps + formal-group torsion; then state
the good-reduction integrality theorem and recover the squarefree-prime UFD form as a corollary. In the
meantime keep this lemma in the project unchanged — it is correct and load-bearing. A reasonable human
action is `/generalise LutzNagell.PID.prime_order_integrality_squarefree` to tension the squarefree
hypothesis against the `p ∤ Δ` / good-reduction standard before any mathlib work.
