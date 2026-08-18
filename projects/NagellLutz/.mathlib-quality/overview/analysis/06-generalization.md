# Step 6 — Generalization Analysis: NagellLutz

Scope: find results stated too specifically that could be generalised. Primary axis for
this project is the **`General*` (ℤ/ℚ) track vs the `PID*` track**: the two tracks prove the
*same theorems* at different generality, and on closer reading the `PID*` track is itself
*mislabelled* — it is really a **UFD** development carrying unused `IsPrincipalIdealRing` +
`CharZero` hypotheses. Secondary axis: division-polynomial / EDS results — these are already
over a general `CommRing R` (copied from mathlib) and are **not** over-specialised; only a
couple of micro-observations there.

No local build available; reasoning is from statements + `omit` clauses (verified by grep) +
literature. Each item: Current / proof-only-uses / Literature / Mathlib / Action / Difficulty.

Difficulty tally: **13 items** — Low **5**, Med **5**, High **3**.

---

## A. The headline finding (read this first)

There are **two parallel proofs of Nagell–Lutz in the repo**:

| concept | `General*` track (over `WeierstrassCurve ℤ`, points in ℚ) | `PID*` track (over `WeierstrassCurve R`, `R` a domain, points in `K = Frac R`) |
|---|---|---|
| base-change curve | `GeneralCurve.curveQ` | `PIDCurve.curveK` |
| denominators | `GeneralDenominators.den_ne_prime_of_on_general_curve` | `PIDDenominators.den_no_simple_prime_factor_of_on_curve` |
| prime-order integrality | `GeneralPrimeOrder.{prime_order_integrality_general, integrality_of_order_four_general, bounded_den_of_order_two_general}` | `PIDPrimeOrder.{prime_order_integrality_squarefree, integrality_of_order_four_squarefree, den_dvd_of_order_two}` |
| descent on `n•P` | `GeneralIntegralMultiple.integral_of_nsmul_integral_general` | `PIDIntegralMultiple.isInteger_of_nsmul_isInteger` |
| main integrality | `GeneralMain.lutz_nagell_integrality_general` | `PIDMain.lutz_nagell_integrality_pid` |
| discriminant | `GeneralDiscriminant.lutz_nagell_discriminant_general` | `PIDMain.lutz_nagell_pid_discriminant_of_torsion` |

The inventory docstrings say it outright: PIDCurve "Generalizes `GeneralCurve.lean` from ℤ/ℚ to
an arbitrary PID"; PIDPrimeOrder "Generalization of `GeneralPrimeOrder.lean` from ℤ/ℚ to a UFD";
PIDIntegralMultiple "Generalizes `GeneralIntegralMultiple.lean` from ℤ/ℚ to a UFD".

**So the entire `General*` track is a strict special case (`R := ℤ`, `K := ℚ`) of the `PID*`
track** — and in the one place they differ in *strength*, the `General*` track is **weaker**
(its order-2 branch only gives `4x, 8y ∈ ℤ`, whereas the PID branch gives the sharp
`den x ∣ 4`). The `General*` track is essentially **duplicated, weaker code**.

This produces the two top-priority items (#1, #2), then the observation that the `PID*` track is
over-hypothesised (#3–#6), then the rest.

---

## 1. `General*` Nagell–Lutz is a redundant ℤ/ℚ instance of the `PID*` track — retire it

- **Current:** Six files (`GeneralCurve`, `GeneralDenominators`, `GeneralPrimeOrder`,
  `GeneralIntegralMultiple`, `GeneralMain`, `GeneralDiscriminant`) re-prove, over
  `W : WeierstrassCurve ℤ` / points in ℚ, the same statements the `PID*` files prove over a
  domain `R` with `K = Frac R`. The public entry points are
  `LutzNagellTheorem.lutz_nagell` (short curve, `Main.lean`) and `lutz_nagell_general`.
- **proof-only-uses:** Each `*_general` lemma's proof is structurally identical to its `PID*`
  twin with `ℤ`/`ℚ` hard-wired (`x.den` vs `IsFractionRing.den R x`, `(· : ℤ → ℚ)` vs
  `algebraMap R K`, `Rat.num/den/reduced` vs `IsFractionRing.num_den_reduced`). Nothing in the
  proofs uses a property of ℤ beyond "domain + UFD + fraction field" — exactly what the `PID*`
  track already abstracts.
- **Literature:** Silverman (*AEC* VIII) / "Nagell–Lutz, quickly" (Alpoge–Granville, the project's
  stated reference) phrase the theorem over a Dedekind / general base; the ℤ statement is a
  corollary, not a separate theorem. The 2025 arXiv note "Nagell-Lutz Theorem for Imaginary
  Quadratic Fields with Class Number One" treats exactly the `𝓞 K`-PID case the `PID*` track
  already covers.
- **Mathlib:** n/a — internal consolidation. mathlib never keeps a ℤ-only twin alongside a
  general-base proof.
- **Action:** **Derive the `General*` public API as one-line corollaries of the `PID*` track at
  `R := ℤ`, `K := ℚ`** (using `Rat.isFractionRing`/`Int.instUniqueFactorizationMonoid`), then
  delete the bodies of the six `General*` files. Concretely:
  `lutz_nagell_integrality_general` ⇐ `lutz_nagell_integrality_pid` (+ translate `IsInteger ℤ ·`
  ↔ `∃ x₀ : ℤ, (x₀:ℚ)=·` via `Int`'s `IsIntegrallyClosed`/`IsFractionRing` glue);
  `lutz_nagell_discriminant_general` ⇐ `lutz_nagell_pid_discriminant_of_torsion`. Keep `Main.lean`'s
  short-curve façade. This removes ~5 of the project's biggest proofs (incl. the ~94-line
  `den_ne_prime_of_on_general_curve`, which is just `den_no_simple_prime_factor_of_on_curve`
  specialised, and the 48-line `kappa_sq_dvd_four_Psi3`).
- **Difficulty:** **High** — not mathematically hard, but it is a structural refactor touching the
  project's public surface (the `∃ x₀ : ℤ` ↔ `IsInteger ℤ` bridge needs a small adapter layer,
  and `Main.lean` re-exports must be repointed). High *value*: it roughly halves the Lutz–Nagell
  proof code. **Recommend a dev ticket, not an autonomous `/generalise`.**

## 2. The order-2 branch: `General` is weaker than `PID` — unify on the sharp `den ∣ 4`

- **Current:** `bounded_den_of_order_two_general` concludes `(∃ n, (n:ℚ)=4*x) ∧ (∃ m, (m:ℚ)=8*y)`
  (i.e. `4x, 8y ∈ ℤ`). The PID twin `den_dvd_of_order_two` concludes `den R x ∣ 4` — strictly
  sharper and basis-independent (and feeds `lutz_nagell_integrality_pid`'s clean
  `addOrderOf P = 2 ∧ den R x ∣ 4` disjunct).
- **proof-only-uses:** identical `Ψ₂Sq`-leading-coeff-`= 4` + rational-root denominator bound; the
  `General` version then *manually* unpacks `den ∣ 4` into the `4x, 8y` witnesses, losing
  information.
- **Literature:** the standard statement is "the denominator of `x` divides 4" (Silverman); `8y ∈ ℤ`
  is a downstream convenience, not the theorem.
- **Mathlib:** n/a.
- **Action:** subsumed by #1 — once `General` is a corollary of `PID`, state the ℤ order-2 branch
  as `den ∣ 4` (or `4 ∣ x.den` via `IsFractionRing.den ℤ`) and derive `4x, 8y ∈ ℤ` only where a
  caller actually wants them.
- **Difficulty:** **Med** (folded into #1; on its own it is a statement change to a public lemma →
  `state:review`).

## 3. `PIDMain`: drop `IsPrincipalIdealRing R` entirely — it is an **unused** hypothesis

- **Current:** `PIDMain.lean` opens `variable {R} [CommRing R] [IsDomain R]
  [IsPrincipalIdealRing R] [CharZero R]` and names everything `*_pid` / `NumberField.*` with the
  side-condition `IsPrincipalIdealRing (𝓞 K)` ("class number 1").
- **proof-only-uses:** grep shows **every** computational lemma in the file carries
  `omit [IsPrincipalIdealRing R]` (lines 46, 56, 68, 178, 187, 197, 220, 239, …), and the two
  theorems that *don't* omit it (`lutz_nagell_integrality_pid`,
  `lutz_nagell_pid_discriminant_of_torsion`) only call **UFD-level** imports
  (`prime_order_integrality_squarefree`, `integrality_of_order_four_squarefree`,
  `den_dvd_of_order_two` from `PIDPrimeOrder`, which is `[UniqueFactorizationMonoid R]`). **No
  proof in the file uses that `R` is a PID.** The "PID" name is folklore: PID ⇒ class number 1
  ⇒ the squarefree hypotheses can be met, but the *theorem* never needs principality.
- **Literature:** the integrality half of Nagell–Lutz needs only that `R` is **integrally closed
  with unique factorization of the relevant denominators** — i.e. a UFD (a Dedekind domain of
  class number 1 is a PID is a UFD; the proof uses the UFD/integrally-closed face). The PID
  framing is the *imaginary-quadratic-class-number-1* application, which is a corollary.
- **Mathlib:** mathlib's `isInteger_of_is_root_of_monic` (the engine under every integrality
  lemma) is stated for `[IsIntegrallyClosed R] [IsFractionRing R K]` — *weaker* than UFD. The
  denominator-descent lemmas (`den_no_simple_prime_factor_of_on_curve`) genuinely need prime
  factorisation, so **UFD** is the honest floor for the file as written.
- **Action:** change `PIDMain`'s variable block to
  `[CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]` (matching its three support files),
  delete `[IsPrincipalIdealRing R]`, and rename the namespace `LutzNagell.PID → LutzNagell.UFD`
  (or keep `PID` but document it covers all UFDs). The `NumberField.*` corollaries still
  instantiate at `𝓞 K` with `IsPrincipalIdealRing (𝓞 K)` (since `PID ⇒ UFD` for `𝓞 K`), so the
  public number-field API is unchanged.
- **Difficulty:** **Med** — pure hypothesis-weakening + rename; mechanically safe (the instances
  are strictly fewer), but it is a statement change on public decls → `lane:generalise`,
  `state:review`. Worth doing because it makes the whole track honestly UFD-level and removes the
  false impression that principality is used.

## 4. `CharZero R` in `PIDMain` is replaced by explicit `Squarefree (p : R)` — drop it too

- **Current:** `PIDMain` carries `[CharZero R]` in its variable block, yet
  `lutz_nagell_integrality_pid` *also* takes `hsf_all : ∀ p, p.Prime → p ∣ addOrderOf P →
  Squarefree (p : R)`, and the order-2 helper uses `den_dvd_of_order_two`'s explicit
  `(4 : R) ≠ 0`.
- **proof-only-uses:** the lemmas `omit [CharZero R]` on lines 46, 56, 68, 178, 187, 197, 220,
  239, …; the genuine arithmetic needs are exactly the `Squarefree (p : R)` hypotheses and
  `(4 : R) ≠ 0`/`(2 : R)` squarefree — all passed explicitly. `CharZero` is used (if at all) only
  to *discharge* `Squarefree (2 : R)`/`(4:R) ≠ 0` for the caller's convenience.
- **Literature:** Nagell–Lutz in char 0 is the classical statement, but the *mechanism* is purely
  about primes dividing the torsion order being non-units-to-first-power; char-0 is sufficient,
  not necessary (the squarefree hypotheses are the real content — cf. the failure of clean
  integrality at primes of bad/additive reduction, handled here by the squarefree side-condition).
- **Mathlib:** n/a.
- **Action:** drop `[CharZero R]` from the block (every theorem already takes the squarefree
  hypotheses it needs). For the `NumberField.*` corollaries, supply `Squarefree (p : 𝓞 K)` from
  `CharZero (𝓞 K)` at the call site (a number field has char 0), so the public number-field
  statements keep their current convenient form.
- **Difficulty:** **Low–Med** — `omit`s already prove it's unused inside the file; the only work is
  threading squarefreeness in the `NumberField` re-exports. Statement change → `state:review`.

## 5. `den_powerful_of_on_curve` / `den_powerful_number_field`: already UFD-general, just mis-housed

- **Current:** `PIDMain.den_powerful_of_on_curve` ("every prime dividing `den x` divides it ≥
  twice") sits in the PID file under the PID variable block, but `omit [CharZero R]
  [DecidableEq K]` and its only real dependency is `den_no_simple_prime_factor_of_on_curve`
  (UFD).
- **proof-only-uses:** UFD only (it is the contrapositive packaging of the PIDDenominators result).
- **Literature:** "denominators of points on a Weierstrass curve are powerful (supported at the
  primes of bad reduction to ≥ 2nd power)" — Silverman; holds over any UFD/Dedekind base.
- **Mathlib:** n/a.
- **Action:** move `den_powerful_of_on_curve` next to its dependency in `PIDDenominators.lean`
  (UFD block) and re-export. Subsumed by #3's rename, but worth flagging as the cleanest standalone
  UFD result in the file.
- **Difficulty:** **Low** (a move + the #3 hypothesis change).

## 6. `den_not_prime_of_on_curve` / `den_no_simple_prime_factor_of_on_curve`: UFD is right; note the Dedekind ceiling

- **Current:** stated over `[UniqueFactorizationMonoid R]` (correct, since the proof factors
  `den` and does prime-by-prime descent).
- **proof-only-uses:** prime factorisation of `den x`, `Prime.dvd_or_dvd`, `IsRelPrime` of reduced
  num/den — all UFD-level. **Cannot** drop to a general integrally-closed domain (the descent
  needs unique factorisation of the denominator).
- **Literature:** over a **Dedekind** domain the same statement holds via the
  valuation/`v(x) < 0 ⇒ v(x) ≤ -2` argument (no global UFD needed) — that is the maximally-general
  number-field form, and the right target if the project ever wants class number > 1.
- **Mathlib:** Dedekind-domain valuation API exists (`IsDedekindDomain.HeightOneSpectrum`,
  `ValuationRing`), so a Dedekind reproof is feasible but is a genuinely different proof.
- **Action:** **keep UFD as-is** for now (the descent proof is UFD-shaped). Record as a *future*
  generalisation: re-derive via height-one valuations to reach arbitrary Dedekind / number-field
  base (class number > 1), which is the literature ceiling. Not an auto-`/generalise`.
- **Difficulty:** **High** (Dedekind reproof = new math, dev ticket) / the "leave as UFD" decision
  is **Low**.

---

## B. Division-polynomial / EDS results — base-ring generality audit

These files (`DivisionPolynomial`, `DivisionPolynomialDegree`, `DivisionPolynomialOmega`,
`EllipticDivisibilitySequence`, `EllipticDivisibilitySequenceOriginal`) are largely **copied from
mathlib** and are already over a general `CommRing R` with `(W : WeierstrassCurve R)`. **They are
not over-specialised** — this is the good news and it means the EDS/division-poly layer is already
at literature generality (Stange's EDS theory is over any commutative ring). Only micro-items:

## 7. Degree/leading-coeff lemmas: hypotheses are already minimal (`(n:R) ≠ 0`, `NoZeroDivisors`) — no action

- **Current:** `natDegree_preΨ`, `leadingCoeff_preΨ`, `natDegree_ΨSq`, `leadingCoeff_Φ`, etc. are
  stated over `CommRing R` with exactly the nonvanishing side-conditions they need
  (`(n : R) ≠ 0`; `[NoZeroDivisors R]` for the `ΨSq` degree=`|n|²−1`; `[Nontrivial R]` for the
  monic `Φ`).
- **proof-only-uses:** matches the hypotheses (`compute_degree`, `natDegree_eq_of_le_of_coeff_ne_zero`).
- **Literature/Mathlib:** this *is* the mathlib pattern (these mirror
  `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`).
- **Action:** **none** — already general. Listed only to record it was checked and is fine.
- **Difficulty:** n/a.

## 8. `ψ₂_sq` / `C_Ψ₂Sq` / the `*_ne_zero` family: general `CommRing` — no action

- **Current:** all over `CommRing R`; `*_ne_zero` results add `[Nontrivial R]`/`[NoZeroDivisors R]`
  exactly where needed.
- **Action:** **none** — at correct generality.
- **Difficulty:** n/a.

## 9. EDS core (`preNormEDS`, `normEDS`, `rel₄`, `IsEllSequence`, …): general `CommRing R` — no action

- **Current:** 161 decls, all over `CommRing R` (a handful of `NoZeroDivisors`/`IsDomain` where
  cancellation is needed, e.g. `addMulSub_mem_nonZeroDivisors`).
- **Literature:** Stange's elliptic nets / Ward's EDS are defined over arbitrary commutative rings;
  this matches.
- **Action:** **none.** (`EllipticDivisibilitySequenceOriginal.lean` appears to be a near-duplicate
  of `EllipticDivisibilitySequence.lean` — that is a *dedup* concern for the consolidation pass, not
  a generalisation one; flagged here only so Step-7/dedup sees it.)
- **Difficulty:** n/a.

---

## C. Field / fraction-field layer

## 10. `EvalBridge.lean`: over a general `Field F` — already maximal for what it does

- **Current:** `variable {F} [Field F] (W : WeierstrassCurve F)`; bridges coordinate-ring `mk`
  congruences to `evalEval`/`eval` at an on-curve point.
- **proof-only-uses:** `AdjoinRoot.evalEval_mk`, `evalEval_pow/C` — field only because the points
  live in a field.
- **Literature/Mathlib:** appropriate; coordinate-ring evaluation is a field-level operation here.
- **Action:** **none** — already general over all fields. (It is *imported* by both tracks, so it is
  correctly factored.)
- **Difficulty:** n/a.

## 11. `ZSMul.zsmul_eq_smulEval`: bridge lemmas over `CommRing R`, main result over a field — fine

- **Current:** `variable {R S} [CommRing R] [CommRing S] (W : WeierstrassCurve R)
  (f : R →+* S)`; `polyEval`/`evalEval_ψ`/… are over `CommRing`; the deliverable
  `zsmul_eq_smulEval` is over a field (it must be — it divides by `ψₙ`).
- **proof-only-uses:** the universal-ring → specialisation machinery (general); division by `ψₙ`
  forces a field for the final statement.
- **Literature/Mathlib:** the `n • P = ⟦(φₙ, ωₙ, ψₙ)⟧` formula is inherently field-level (Jacobian
  coords up to scaling); mathlib's division-polynomial work is similarly field-bound at the point
  level.
- **Action:** **none** — generality is already correct (ring where possible, field only at the
  divide).
- **Difficulty:** n/a.

## 12. `Universal.lean` (`algebraMap_poly_injective`, `algebraMap_injective'`, `some_eq_some_iff`): general — and mathlib-bound

- **Current:** the coordinate-ring injectivity + affine-point-equality helpers are over a general
  `CommRing R` / general field; the docstring flags them as "mathlib-missing".
- **proof-only-uses:** general.
- **Literature/Mathlib:** these are genuine mathlib *gaps* (`Affine.CoordinateRing.algebraMap`
  injectivity, `Point.some` ext) — already at full generality, and are **mathlib-PR candidates**
  (a Step-`mathlibable` concern, noted here because their generality is exactly right for upstreaming).
- **Action:** **none** for generalisation; flag for `/mathlibable`.
- **Difficulty:** n/a.

---

## 13. `y_integral_of_x_integral_on_general_curve` vs `y_isInteger_of_x_isInteger_on_curve` — same lemma, two generalities

- **Current:** `GeneralPrimeOrder.y_integral_of_x_integral_on_general_curve` (ℤ/ℚ) and
  `PIDPrimeOrder.y_isInteger_of_x_isInteger_on_curve` (UFD `R`/`K`) are the **same** lemma ("x
  integral ⇒ y integral on the Weierstrass equation"), the former a special case of the latter.
- **proof-only-uses:** both build the monic quadratic `Y² + (a₁x₀+a₃)Y − (…)` and apply
  `isInteger_of_is_root_of_monic`; the UFD version is the general one. Notably this lemma needs
  only `[IsIntegrallyClosed R] [IsFractionRing R K]` (mathlib's actual hypothesis), so it could be
  stated **below UFD**.
- **Literature/Mathlib:** `isInteger_of_is_root_of_monic` is `[IsIntegrallyClosed R]`.
- **Action:** delete the ℤ/ℚ copy as part of #1; *optionally* relax the surviving UFD copy to
  `[IsIntegrallyClosed R]` (it does not touch denominators, so it does not need UFD) — a small
  honest weakening that lets this one lemma serve a class-number > 1 future.
- **Difficulty:** **Low** (the delete is part of #1; the integrally-closed relaxation is a 1-line
  hypothesis swap on one lemma).

---

## Summary table

| # | Result(s) | Current | Target | Difficulty |
|---|---|---|---|---|
| 1 | whole `General*` track | ℤ/ℚ, duplicated | corollaries of `PID*` at ℤ/ℚ; delete bodies | **High** |
| 2 | `bounded_den_of_order_two_general` | `4x,8y∈ℤ` (weak) | `den x ∣ 4` (sharp, via PID) | **Med** |
| 3 | `PIDMain` block | `IsPrincipalIdealRing R` (unused) | drop it → UFD | **Med** |
| 4 | `PIDMain` block | `CharZero R` (unused, `omit`ed) | drop it; pass `Squarefree` | **Low–Med** |
| 5 | `den_powerful_of_on_curve` | in PID file | UFD; rehouse in PIDDenominators | **Low** |
| 6 | `den_no_simple_prime_factor_of_on_curve` | UFD (correct) | keep UFD; Dedekind = future | **High** (future) / Low (decision) |
| 7–12 | division-poly / EDS / EvalBridge / ZSMul / Universal | already `CommRing`/`Field`-general | none | n/a |
| 13 | `y_integral…` duplicate | ℤ/ℚ + UFD copies | delete ℤ/ℚ; relax UFD→`IsIntegrallyClosed` | **Low** |

**Top 5 (by value):** #1 (retire the redundant `General*` track — halves the Lutz–Nagell code),
#3 (`PIDMain` is secretly UFD, not PID — drop the unused `IsPrincipalIdealRing`), #2 (sharpen the
ℤ order-2 branch via PID's `den ∣ 4`), #4 (drop unused `CharZero`), #13 (kill the duplicated
`y`-integrality lemma; relax to `IsIntegrallyClosed`).

**Auto-`/generalise`-safe (small, mechanical):** #4, #5, #13 (hypothesis drops / a move /
`omit`-proven-unused). **Need a dev ticket (structural / new math):** #1, #2, #3 (public-surface
refactor), #6-Dedekind. The single highest-leverage action is **#1**: once `General*` is corollaries
of the (correctly-UFD-renamed, per #3) track, items #2, #4, #13 fall out for free.
