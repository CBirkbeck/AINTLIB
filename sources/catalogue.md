# AINTLIB Source Catalogue (Phase 0)

Generated from `_scan.tsv` (local repos, pulled to latest), `discovery.tsv` (GitHub/web
search), and `mathlib-nt-prs.json` (open `t-number-theory` PRs). **Awaiting user sign-off.**

Legend: ✦ = ships its own blueprint. Chapters use the §5 names.

---

## Table 1 — Confirmed sources (local + given externals)

| Source | Kind | Remote @ commit | Lean | BP | Proposed chapter |
|---|---|---|---|---|---|
| Adic spaces | local | CBirkbeck/Adic-Spaces @ fb55cd8 | 4.29 | | PAdicAdic |
| chebotarev-density | local | CBirkbeck/chebotarev-density @ 9ddb80d | 4.31 | ✦ | ClassFieldTheory |
| flt-regular-bernoulli | local | CBirkbeck/flt-regular-bernoulli @ 888f2259 | 4.30 | ✦ | FLT |
| LeanModularForms | local | CBirkbeck/LeanModularForms @ 0fc82eb | 4.30 | ✦ | ModularForms |
| LeanModularForms-hecke | local (worktree of LeanModularForms) | CBirkbeck/LeanModularForms @ 3c0ac6c | 4.30 | ✦ | ModularForms (Hecke) |
| FLT (local) | local | ImperialCollegeLondon/FLT @ 9deae05 | 4.9 | ✦ | FLT |
| flt-regular | local | leanprover-community/flt-regular @ 6ade127 | 4.31 | ✦ | FLT |
| Hasse-Weil | local | CBirkbeck/Hasse-Weil @ 03003e7 | 4.29 | | EllipticArithGeom |
| WeilConjectures | local | CBirkbeck/WeilConjectures @ b8464ee | 4.28 | | EllipticArithGeom |
| EulerProducts | local | MichaelStollBayreuth/EulerProducts @ 7376f1a | 4.24 | | Analytic |
| DirichletNonvanishing | local | CBirkbeck/DirichletNonvanishing @ fb3e6ac | 4.13 | ✦ | Analytic |
| LocalClassFieldTheory | local | CBirkbeck/LocalClassFieldTheory @ e7d457c | 4.7 | ✦ | ClassFieldTheory + PAdicAdic |
| Nagel--Lutz | local | CBirkbeck/LutzNagell @ c58fbfa | 4.29 | | EllipticArithGeom |
| NewtonPolys | local | CBirkbeck/NewtonPoly @ a6d9970 | 4.28 | | DiophantineTranscendence |
| power_reside_symbols | local | CBirkbeck/power_residue_symbols @ 0b573a4 | 4.7 | | ClassFieldTheory/Elementary |
| GLn_F_q | local | CBirkbeck/GLn_F_q @ 3fc5ad9 | 4.8 | | Algebraic |
| ModFormDims | local | CBirkbeck/ModFormDims @ 10bab48 | 4.13 | | ModularForms |
| PrimeNumberTheoremAnd | external | AlexKontorovich/PrimeNumberTheoremAnd | latest | ✦ | Analytic |
| FLT (Imperial, upstream) | external | ImperialCollegeLondon/FLT (cloned as FLT-imperial) | latest | ✦ | FLT |

Three local repos had uncommitted changes and were left un-pulled (HEAD recorded): **flt-regular-bernoulli, FLT, power_reside_symbols** — your local work is untouched.

---

## Table 2 — Candidate sources (discovered; need your decision)

Credible, substantive projects found by search. R = my recommendation.

| Repo | ★ | What it is | Chapter | R |
|---|---|---|---|---|
| kbuzzard/ClassFieldTheory | 14 | Buzzard's 2025 Clay school CFT formalisation | ClassFieldTheory | **include** |
| riccardobrasca/KummerCriterion | 2 | Kummer's criterion for regularity (ties Bernoulli ↔ regular) | FLT | **include** |
| lean-forward/class-group-and-mordell-equation | 3 | class-group computations + integral points on Mordell curves | EllipticArithGeom/Algebraic | **include** |
| ImperialCollegeLondon/diophantine | 9 | solving Diophantine equations | DiophantineTranscendence | **include** |
| teorth/pfr | 214 | Polynomial Freiman–Ruzsa | AdditiveCombinatorial | **include** |
| google-deepmind/formal-conjectures | 1006 | formal statements of many NT conjectures | frontier/conjectures appendix | **include** |
| grthomson/silverman-tate | 1 | Silverman–Tate *Rational Points on Elliptic Curves* | EllipticArithGeom | maybe |
| KisaraBlue/ec-tate-lean | 3 | Tate's algorithm for elliptic curves on mathlib | EllipticArithGeom | maybe |
| b-mehta/PrimeCert | 10 | formal prime certificates | Elementary | maybe |
| pechersky/gouvea | 0 | Gouvêa's *p-adic Numbers* textbook | PAdicAdic | maybe |
| AxiomMath/ramanujan-tau-misses-primes | 9 | ABC ⟹ Ramanujan τ misses almost all primes | ModularForms | maybe |
| Eloitor/four-squares-modular-forms | 2 | four-squares theorem via modular forms | ModularForms | maybe |
| dobronx1325/Daboussi_Pnt | 1 | Daboussi's elementary proof of PNT | Analytic | maybe |
| mmasdeu/lean-nt | 0 | Masdeu — misc NT results | various | maybe |
| riccardobrasca/cyclotomic | 0 | cyclotomic fields (likely ⊂ mathlib now) | Algebraic | maybe |
| laughinggas/p-adic-L-functions | 6 | p-adic L-functions (**Lean 3**) | PAdicAdic | note (Lean 3) |
| Vierkantor/mersenne-primes | 1 | Mersenne primes ↔ even perfect numbers | Elementary | maybe |

Excluded as noise/crank or pure learning exercises (RNT/"Reflective Number Theory", "RH-was-a-pseudo-problem", unverified millennium-problem claims, intro-course repos). Full list stays in `discovery.tsv`.

---

## Table 3 — Other local folders to triage

| Folder | Remote | Note | R |
|---|---|---|---|
| WeilConverse | CBirkbeck/WeilConverse (4.11) ✦ | **Weil converse theorem** (L-function ⟹ modularity) | **include** → ModularForms/Analytic |
| formal-conjectures / …NEW | CBirkbeck fork / google-deepmind upstream | NT conjecture statements | include upstream (= Table 2) |
| AACConjecture | riccardobrasca/AACConjecture (4.27) | a specific conjecture (needs a look) | **your call** |
| FLTNEW | ImperialCollegeLondon/FLT (4.24) ✦ | newer local copy of Imperial FLT | fold into FLT-imperial |
| FLTme | CBirkbeck/FLT (4.9) ✦ | personal FLT fork | fold/skip |
| FltRegulartest | CBirkbeck/FltRegulartest (4.10) ✦ | flt-regular test variant | fold/skip |
| ETH_FLT | CBirkbeck/ETH_FLT (no toolchain) | stale/empty | skip |
| ModularForms_Lean4 | CBirkbeck/ModularForms_Lean4 (4.5) | superseded by LeanModularForms | skip (note as lineage) |
| ModularFormsLean3 | CBirkbeck/ModularForms (Lean 3) | Lean 3 | skip |
| UEA_primes | CBirkbeck/UEA_primes (no toolchain) | teaching repo | skip |

---

## Table 4 — Forthcoming in mathlib (58 open `t-number-theory` PRs), by chapter

- **Elementary:** #26158 int divisors, #35805 infinite divisors, #36495 divisor-sum refactor, #28676 totient as ArithmeticFunction, #40170 radical divides power, #39903 almost-primes, #40246 Farey sequences, #25739 Legendre sqrt-of-residue, #34507/#39404 AKS primality, #37299 Chebyshev primorial bound, #40037 three-gap (Steinhaus).
- **Analytic:** #20008/#27702/#27707 Selberg sieve, #40316 ζ′(0), #20671 σₖ(n)=O(nᵏ⁺¹), #37585 Robin/Lagarias RH-equivalents, #31187 L-series of a modular form.
- **Algebraic / CFT:** #9444 𝓞 K instances, #26913 number-field & cyclotomic lemmas, #36347/#36387 quadratic number fields, #36843 Hilbert theory (unramified compositum), #37031 inertia field of cyclotomic, #33992 Galois generated by inertia, #40126 ramification–inertia refactor, #19616 absolute Galois group fix, #40331 MulChar.
- **p-adic / adic:** #21950 completion of ℚ at a finite place = ℚ_p, #23772/#23791 Amice transform, #26885/#26886/#27163/#26827 ValuativeRel, #27972/#28328 valuation refactors, #32692 multivariate power series.
- **Modular forms:** #36963 SL₂ action + Serre derivative, #38813 E₄/E₆ generate the graded ring, #39000 Sturm bound.
- **Elliptic / arith. geom.:** #13057/#13155/#25989/#25990 elliptic divisibility sequences & nets, #13782 ZSMul via division polynomials, #36989 Height/EllipticCurve, #39744 Northcott property, #38050 Newton polygons.
- **Transcendence:** #33050/#35735/#35743/#35744 Gelfond–Schneider.

---

## Decisions requested

1. **Table 2 "include" set** (Buzzard CFT, KummerCriterion, class-group-and-mordell, Imperial diophantine, pfr, formal-conjectures) — OK to add all? Any "maybe" you want promoted/dropped?
2. **WeilConverse** — include? (It has a blueprint and fills the "converse theorem" story.)
3. **AACConjecture** — include, or skip?
4. **FLT variants** (FLTNEW/FLTme/FltRegulartest/ETH_FLT) — agree to fold into the canonical FLT/flt-regular entries?
