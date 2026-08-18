# /mathlibable report — `LutzNagell.PID.lutz_nagell_integrality_pid`

### Baseline (Phase 0)
- lake build:               not run (local build stale per task brief; reasoning from source as instructed)
- decl `LutzNagell.PID.lutz_nagell_integrality_pid`:  ✓ resolved at `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDMain.lean:142`
- qualified name:           `LutzNagell.PID.lutz_nagell_integrality_pid` (namespaces `LutzNagell` → `PID`, opened lines 35–36, closed 475/573) — VERIFIED
- kind:                     theorem
- has sorry:                no
- module docstring summary: Lutz–Nagell theorem generalized from ℤ/ℚ to a PID `R` of characteristic zero with fraction field `K` (and a number-field corollary for class-number-1 rings of integers).

---

### Statement (Phase 1)

`LutzNagell.PID.lutz_nagell_integrality_pid` is a theorem stating a PID-level generalization of the
**Nagell–Lutz theorem**:

Let `R` be a principal ideal domain of characteristic zero with fraction field `K`, and let `W` be a
general Weierstrass curve with coefficients in `R`. For a nonzero finite-order (torsion) point
`(x, y)` on the base-changed curve `W_K` over `K`, suppose that for every prime `p` dividing the
additive order of the point, the image of `p` in `R` is squarefree (an "unramified-like" condition).
Then either (a) the coordinates are integral, `x, y ∈ R` (in the `IsLocalization.IsInteger` sense), or
(b) the point has order exactly `2` and the denominator `den_R(x)` divides `4`.

Variables / typeclasses (Lean side):
- `R : Type*` with `[CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [CharZero R]` — the PID of char 0.
- `K : Type*` with `[Field K] [DecidableEq K] [Algebra R K] [IsFractionRing R K]` — fraction field.
- `W : WeierstrassCurve R` — a general (not short) Weierstrass curve over `R`.
- `curveK R K W := W.map (algebraMap R K)` — base change to `K` (project `abbrev`, `PIDCurve.lean:27`).

Hypotheses (Lean side):
- `hpt : (curveK R K W).toAffine.Nonsingular x y` — `(x,y)` is a nonsingular affine point.
- `htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt)` — the point is torsion (finite additive order).
- `hsf_all : ∀ p : ℕ, p.Prime → p ∣ addOrderOf (…) → Squarefree (p : R)` — every prime dividing the
  order has squarefree image in `R` ("unramified-like").

Conclusion (math): `(x,y)` is integral, OR it is a 2-torsion point with `den(x) ∣ 4`.

Conclusion (Lean):
`((IsLocalization.IsInteger R x) ∧ IsLocalization.IsInteger R y) ∨ (addOrderOf (…) = 2 ∧ (IsFractionRing.den R x : R) ∣ (4 : R))`.

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: It is a theorem named after people (Nagell–Lutz) and is the headline "with unramified hypothesis"
result of the file's `## Main results`. Named theorems are essentially guaranteed to sit in/near the
literature, and this one does (Silverman AEC VIII.7.1; recent arXiv generalizations).

(Literature width is EXHAUSTIVE regardless.)

### One-line check (Phase 2b)
n/a — kind is `theorem`, not a `def`/`abbrev`/`structure`. (Body is a ~35-line case-split proof.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "Nagell-Lutz theorem elliptic curve torsion integer coordinates statement" | yes | over ℚ: torsion pt of `y²=x³+ax²+bx+c` (ℤ coeffs) has `x,y∈ℤ`; `y=0` or `y²∣D` | Wikipedia, Silverman–Tate; classical form is over ℤ only |
| 2 | WebSearch (general form) | "Nagell-Lutz generalization number field ring of integers torsion integrality" | yes | generalizes to number fields / 𝒪_K; recent work: imaginary quadratic, class number 1 | arXiv 2509.07524 (Sep 2025) — exact PID-direction generalization |
| 3 | WebSearch (named-after / aliases) | "Nagell-Lutz Dedekind/PID squarefree torsion unramified" | partial | "by rescaling one may assume divisors squarefree"; extended to arbitrary number fields | no source states a PID+squarefree-image *hypothesis*; squarefreeness is a normalization, not a hypothesis |
| 4 | ChatGPT MCP | (asked: standard generality, PID vs reduction-theoretic, sharp conclusion) | n/a | — | MCP DOWN — Codex `exec` failed on both gpt-5.4 and gpt-5.4-mini (matches task warning); compensated via Silverman + arXiv + Wikipedia |
| 5 | Local references | `.mathlib-quality/references/` for "nagell" | n/a | (no references dir) | directory absent — recorded n/a |
| 6 | nLab | "Nagell-Lutz theorem" | n/a | 404 — page does not exist | not a categorical concept; nLab has no entry |
| 7 | nCatLab | (categorical?) | n/a | — | not a categorical concept — Diophantine/arithmetic statement |
| 8 | Stacks Project | elliptic curve torsion integrality | n/a | not covered | Stacks is scheme-theoretic foundations; no Nagell–Lutz / torsion-integrality |
| 9 | MathOverflow / MSE | (surfaced via WebSearch #1–3) | yes | confirms classical ℤ form + number-field extensions | Harvard "Nagell-Lutz, quickly" (Alpoge); REU notes (Galperin) |
| 10 | recent arXiv (≤5 yr) | "Nagell-Lutz imaginary quadratic class number one" | yes | **Thm 1 (arXiv 2509.07524, 2025):** torsion `(x,y)` ⇒ `x,y∈ℤ[√D]` for the 9 class-number-1 imaginary quadratic fields; relies essentially on **class number 1 (PID)** | This is the *same* generalization direction; published 2025 → research frontier |

Protocol pass check: WebSearch ran 3 queries at distinct generality levels (specific/general/named-aliases) ✓;
ChatGPT MCP attempted twice and recorded down ✓; local refs n/a w/ reason ✓; nLab checked (404) ✓;
Stacks/nCatLab/MathOverflow/arXiv each checked or n/a w/ reason ✓.

### Literature summary (Phase 3)

Concept identified as: **Nagell–Lutz theorem** (integrality of torsion points on elliptic curves), a.k.a.
"Lutz–Nagell".
Sources agree on the standard *classical* form: yes — over ℤ/ℚ.
Sources on the *generalization*: the modern reference proof (Silverman, *Arithmetic of Elliptic Curves*,
**Thm VIII.7.1**) is **reduction-theoretic / formal-group**: at each prime the kernel of reduction is
torsion-free above the residue characteristic, so a torsion point is integral at every good-reduction
prime whose residue characteristic doesn't divide the order. This is a **local statement at each prime**
and needs **no global PID hypothesis**. The "rescale so divisors are squarefree" remark in elementary
treatments is a *normalization*, not a hypothesis on which primes may divide the order.

Most general standard form: the reduction/formal-group statement over a Dedekind domain (or one prime at a
time over a DVR / local field) — integrality holds prime-by-prime via `E₁(K) = ker(reduction)` being
uniquely divisible by integers prime to the residue char.

Generality dimensions where the literature varies:
- base ring: classical ℤ → 𝒪_K (number fields) → Dedekind domain / DVR (reduction approach); the project sits at **PID**, strictly between ℤ and the reduction-theoretic Dedekind/local form.
- hypothesis on the order: classical (none, char 0) vs. project's "squarefree image of each prime divisor". The standard reduction form replaces this with the *local* condition "residue char ∤ order at each prime", which the global squarefree hypothesis is a sufficient global surrogate for.
- conclusion: classical sharp form is over ℤ (`x,y∈ℤ`, with the `4x,8y` refinement in the general-coeff ℚ case); the project's "`x,y∈R` OR order-2 with `den(x)∣4`" mirrors the ℚ general-coefficient refinement, lifted to `R`.

Disagreement with the literature: the **"PID + per-prime squarefree image" packaging is project-specific**,
not a recognized standard hypothesis. The standard treatment avoids a global PID via reduction at each prime.

---

### Generality analysis — `LutzNagell.PID.lutz_nagell_integrality_pid`

Literature-standard form (from Phase 3): reduction/formal-group statement — over a Dedekind domain (or DVR
per prime), a torsion point is integral at each prime of good reduction whose residue characteristic does
not divide the order; no global PID needed (Silverman VIII.7.1).

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `[IsPrincipalIdealRing R]` | PID | Dedekind domain / per-prime DVR | yes (in principle) | Reduction approach localizes at each prime; PID is a global surrogate the standard proof avoids. But the *current* proof (denominator/EDS arguments) uses unique factorization essentially → weakening to Dedekind needs new ideas. |
| 2 | `[CharZero R]` | char 0 | char 0 (or residue char ∤ order) | partial | char-0 is convenient; standard form needs only residue char ∤ order at each relevant prime. Weakening needs the local formulation. |
| 3 | `hsf_all : Squarefree (p : R)` for all `p ∣ ord` | global squarefree-image hypothesis | local "residue char ∤ order" at each prime | yes | This is the non-standard packaging. The clean form folds it into per-prime reduction. Removing/recasting it = the main generalization. |
| 4 | `W : WeierstrassCurve R` (integral model) | integral Weierstrass model | minimal/good-reduction model at each prime | NO (here) | needing an integral model is intrinsic to "integral coordinates"; fine. |
| 5 | conclusion `den(x) ∣ 4` order-2 branch | `R`-level den divides 4 | matches the general-coeff refinement | NO | this is the correct sharp `R`-analogue; keep. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD**
Number of weakening opportunities found: 3 (rows 1–3; global PID + char0 + the bespoke squarefree hypothesis
are all subsumed by the reduction-theoretic per-prime statement).
Proposed restatement (target — the standard reduction/formal-group form): integrality of torsion at each
prime `𝔭` of good reduction with residue characteristic not dividing the order, over a Dedekind domain (or
stated locally over a DVR / `Valued` field), via `E₁(K) = ker(reduction)` being torsion-free / uniquely
`n`-divisible for `n` prime to the residue characteristic. Over a PID this then assembles to the global
statement; over ℚ it recovers classical Nagell–Lutz.
Cost of restatement: **EXPENSIVE** — the current proof is a global denominator / elliptic-divisibility-
sequence argument; the reduction-theoretic form needs formal-group / reduction-map infrastructure mathlib
does not yet have. (EXPENSIVE does not downgrade the verdict.)

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|---|----------|----------|------------------------|----------------------------------|
| 1 | "let R be a foo" → typeclasses? | no | already typeclass-based (`IsPrincipalIdealRing`, `IsFractionRing`) | — |
| 2 | sequences/metric → filters/topological? | partial | the standard proof is `𝔭`-adic; a `Valued`/`WithVal` or reduction-map formulation is the topological-arithmetic idiom mathlib is moving toward for local fields | composes with mathlib's valuation / local-field / formal-group API (once it exists) |
| 3 | construct → universal property? | no | — | — |
| 4 | set+closure → bundled substructure? | no | — | — |
| 5 | vector-space/field-specific → weaker typeclass? | yes | base ring PID → Dedekind / DVR (see 4b) | full Dedekind-domain & local-field torsion API |
| 6 | 1-categorical → higher-categorical? | no | arithmetic statement; no categorification | — |
| 7 | concrete index (ℕ,ℤ,ℝ) → general algebraic structure? | yes | the whole point: ℤ → PID is done; PID → Dedekind/local is the remaining idiom step | unifies with number-field & local-field developments |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** — the reduction-map / formal-group (per-prime, Dedekind/DVR) formulation.
- Proposed mathlib-idiomatic restatement: state integrality of torsion via the reduction map at each prime
  of good reduction (residue char ∤ order), over a Dedekind domain; PID/number-field versions become
  corollaries. (Signature would be substantially different — keyed on a prime / valuation, not a global PID.)
- Cost: **EXPENSIVE** (needs reduction-of-elliptic-curves + formal-group torsion infrastructure not yet in mathlib).
- Mathlib downstream this enables: torsion-injection into the reduction `Ẽ(k_𝔭)` (the standard tool for
  bounding torsion), good-reduction/Néron-model adjacency, the number-field and local-field corollaries
  uniformly, and the classical ℚ Nagell–Lutz as a one-line specialization.
- Real mathematical improvement: it removes a global PID/class-number-1 crutch that the standard theory does
  not need, replacing it with the genuinely correct per-prime hypothesis — eliminating a real redundancy.

---

### Mathlib search-status: `LutzNagell.PID.lutz_nagell_integrality_pid`

[A] Lean-Finder       — (tool not available in this env)            n/a: not exposed here
[B] Loogle            — (tool not available in this env)            n/a: not exposed; substituted with source grep [D]
[C] LeanSearch        — (tool not available in this env)            n/a: not exposed; substituted with WebSearch + source grep
[D] Grep mathlib src  "nagell", "lutz" over all `Mathlib/`         no hits (only unrelated Galois names: AbelRuffini etc.)
[D] Grep mathlib src  "IsOfFinAddOrder"/"addOrderOf" in `EllipticCurve/`  **no hits** — no torsion-order result on EC points
[D] Grep mathlib src  "torsion" in `EllipticCurve/`               hits are all `torsionPolynomial` / division polynomials, NOT torsion-point integrality
[E] Name pattern      `WeierstrassCurve`/`EllipticCurve` + integrality of points  no integrality-of-torsion decl exists

Searched for both:
  - the user's current form (PID + squarefree-prime, general Weierstrass over `K`) — absent.
  - the literature-standard reduction form (torsion integral at good-reduction primes) — also absent;
    mathlib has the `AddCommGroup` on `W.Point` (`Affine/Point.lean:770`) and division/torsion *polynomials*,
    but no reduction map for elliptic curves and no torsion-integrality theorem.

Concluded: **not in mathlib** (mathlib source exhausted for both the user's form and the standard reduction
form). Mathlib has only the group structure and the division-polynomial machinery — the building blocks for a
*future* reduction-theoretic proof, but no statement of Nagell–Lutz in any form.

---

### Call sites — `LutzNagell.PID.lutz_nagell_integrality_pid`

Internal use count: **2** (excluding the declaring lines; both outside the proof of the decl itself)
External-to-file callers: 0 distinct other files (both uses are within `PIDMain.lean`, but in *other*
declarations — a genuine API consumer pattern, not self-reference).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `PIDMain.lean:380` | `rcases lutz_nagell_integrality_pid W hns' (h2P_eq ▸ htor.nsmul) hsf_2P with …` — **recursive** use on the doubled point `2•P` inside `kappa_sq_dvd_four_Psi3_of_torsion` (the discriminant-divisibility derivation) |
| `PIDMain.lean:509` | `PID.lutz_nagell_integrality_pid W hpt htor hsf_all` — the number-field corollary `NumberField.lutz_nagell_number_field` is *literally this theorem* re-exported |

Inline-derivation grep (re-derived elsewhere without using the decl?): (none) — the result is reused, not duplicated.

Signal: K=2 internal uses, no inline re-derivation; one of them is the headline number-field theorem and one
is a recursive call in the discriminant proof. Real API → YES-* leaning.

---

### Composition check (Phase 6)

Can `lutz_nagell_integrality_pid` be derived from mathlib in ≤3 chained calls?

Attempt 1: any mathlib primitive(s) yielding torsion ⇒ integral on EC points.
  - Mathlib decls used: none exist (Phase 5: no torsion-integrality, no reduction map).
  - Result: **fails** — there is nothing in mathlib to chain.

Attempt 2: assemble from the project's own lemmas (`integrality_of_odd_prime_factor`,
  `integrality_of_four_dvd_order`, `den_dvd_of_order_two`, `prime_order_integrality_squarefree`, …).
  - These are all **project-internal**, spanning `PIDPrimeOrder`, `PIDIntegralMultiple`, `PIDDenominators` —
    a multi-file development, not mathlib primitives. Not a composition in the skill's sense.

Conclusion: **NOT-COMPOSABLE** (from mathlib). It is the apex of an original ~5-file development.

---

## Verdict: `LutzNagell.PID.lutz_nagell_integrality_pid`

**Category:** YES-but-generalise-first

**Evidence:**
- Literature search (Phase 3): named theorem (Nagell–Lutz); standard generalization is reduction-theoretic
  (Silverman VIII.7.1), needing **no global PID**; the PID + per-prime-squarefree packaging is project-specific.
  Recent arXiv 2509.07524 (2025) confirms the PID/class-number-1 direction is research frontier.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** (3 weakenings: PID→Dedekind/DVR,
  char0, the bespoke squarefree hypothesis → per-prime residue-char condition). Phase 4c: modern reduction-map
  idiom available, a real organisational improvement.
- Mathlib search (Phase 5): **not in mathlib** — no Nagell–Lutz, no torsion-integrality, no reduction map for EC.
- Composition check (Phase 6): **NOT-COMPOSABLE** — apex of a multi-file project development.

**Rationale:**

Mathlib genuinely lacks this: there is no integrality-of-torsion result for elliptic curves anywhere in
`Mathlib/AlgebraicGeometry/EllipticCurve/` (only the `AddCommGroup` on points and division/torsion
*polynomials*), and "Nagell"/"Lutz" appear nowhere. So this is a real gap, not a duplicate — it is not
`NO-mathlib-has-it`, and being the apex of an original ~5-file development it is not `NO-composable`.

It is nevertheless **not** `YES-add-as-is`, because Phase 4b found the current form strictly narrower than the
literature-standard form and Phase 4c found a genuine modernisation. The standard reference (Silverman AEC
VIII.7.1) proves torsion-integrality **prime-by-prime via reduction / formal groups**, which needs only a DVR
at each prime and **no global PID**; the "`R` is a PID and every prime dividing the order has squarefree
image" packaging is a global surrogate the standard theory avoids. The correct mathlib target is the
reduction-theoretic statement (integral at each good-reduction prime whose residue characteristic does not
divide the order, over a Dedekind domain), from which the PID, number-field (class-number-1), and classical-ℚ
versions all fall out as corollaries. Per the skill's gate, a STRICTLY-NARROWER Phase-4b verdict forces
YES-but-generalise-first, not YES-add-as-is.

Reason for the generalisation:
  - **LITERATURE-WEAKENING:** Phase 4b — user's form (global PID + per-prime squarefree image) is strictly
    narrower than the reduction-theoretic Dedekind/DVR form.
  - **MODERN-IDIOM (Bourbaki 2.0):** Phase 4c — the reduction-map / formal-group formulation is the
    contemporary mathlib idiom and removes the global-PID redundancy.

Proposed restatement (target shape; proof does NOT survive — needs new infrastructure):
```lean
-- Stated at a single prime via reduction; assemble globally over a Dedekind domain.
-- Requires: reduction of elliptic curves + formal-group torsion (NOT yet in mathlib).
theorem WeierstrassCurve.torsion_isInteger_of_goodReduction
    {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [IsFractionRing R K]
    (W : WeierstrassCurve R) {x y : K} (hpt : (W.map (algebraMap R K)).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt))
    (hgood : ∀ 𝔭, /- good reduction & residue char ∤ addOrderOf at 𝔭 -/ True) :
    IsLocalization.IsInteger R x ∧ IsLocalization.IsInteger R y := by
  sorry
```
Estimated cost of regeneralisation: **EXPENSIVE** — mathlib has no reduction map for elliptic curves and no
formal-group torsion theory; this is substantial new infrastructure. (EXPENSIVE does not downgrade the verdict;
mathlib's value is the right form. Cost may inform *sequencing* — ship the PID form to the project now, target
the reduction form for the eventual mathlib PR — but is not itself the reason for the bucket.)

Mathlib downstream this enables (MODERN-IDIOM):
  - torsion-injection `E(K)_tor ↪ Ẽ(k_𝔭)` at good primes — the standard tool for *bounding* torsion subgroups.
  - uniform PID / number-field (class-number-1) / local-field corollaries, and classical ℚ Nagell–Lutz as a
    one-line specialization.
  - composability with a future Néron-model / good-reduction API.
  - proofs blocked by the current global form (anything that is genuinely local at one prime) become available.

Next action: this is a genuine contribution but **not yet in its mathlib-canonical form**. Run
`/generalise LutzNagell.PID.lutz_nagell_integrality_pid` to tension against both the literature-standard
reduction form (Phase 3) and the modern reduction-map idiom (Phase 4c) before any mathlib PR. In the
meantime the PID form is correct and useful **within the project** (it already powers the discriminant
theorem and the number-field corollary) — keep it; the generalisation is a mathlib-upstreaming concern, not
a project defect. Given the EXPENSIVE cost (missing reduction infrastructure), realistically the mathlib path
is: first upstream elliptic-curve reduction + formal-group torsion, then state the reduction-theoretic
Nagell–Lutz, then recover this PID statement as a corollary.

---

## Next step

Run `/generalise LutzNagell.PID.lutz_nagell_integrality_pid` — tension the PID + squarefree-prime form against
the reduction-theoretic Dedekind/DVR standard form before opening any mathlib PR. Keep the PID form in the
project (it powers `lutz_nagell_pid_discriminant_of_torsion` and `NumberField.lutz_nagell_number_field`); the
generalisation is the upstreaming target, gated on mathlib first acquiring elliptic-curve reduction + formal-
group torsion infrastructure.
