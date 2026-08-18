# /mathlibable report — `LutzNagell.PID.x_isInteger_of_nsmul_x_isInteger`

> This decl is the **UFD-general** (PID-track) x-coordinate integral-descent step. It is the
> declaration the sibling reports
> (`x_integral_of_nsmul_x_integral_general.md`, `integral_of_nsmul_integral_general.md`)
> explicitly defer to as "the real upstreaming unit" — they are its ℤ/ℚ shadows.
> Verdict therefore differs from theirs: it is the *content holder*, already at (near) the
> mathlib-natural generality.

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task brief — reasoned from source + the pinned mathlib tree)
- decl `LutzNagell.PID.x_isInteger_of_nsmul_x_isInteger`:
                            ✓ resolved at `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDIntegralMultiple.lean:65` (theorem head; conclusion `IsLocalization.IsInteger R x` on line 71; `:72` in the task brief points into the body)
- kind:                     theorem
- has sorry:                no
- true qualified name VERIFIED: `LutzNagell.PID.x_isInteger_of_nsmul_x_isInteger` — file opens `namespace LutzNagell` (line 15) then `namespace PID` (line 16); matches the task brief's parsed name.
- module docstring summary: "Integral multiple implies integral point (over UFDs)" — if `n • P` has integral affine coordinates on a Weierstrass curve over `K = Frac(R)`, then `P` already has integral affine coordinates; explicitly a "Generalization of `GeneralIntegralMultiple.lean` from `ℤ/ℚ` to a UFD `R`".

---

### Statement (Phase 1)

`x_isInteger_of_nsmul_x_isInteger` is a **theorem** stating:

> Let `R` be a UFD with fraction field `K = Frac(R)`, and let `W` be a Weierstrass curve over `R`,
> with `curveK R K W` its base-change to `K`. Let `P = (x, y)` be a nonsingular affine point on
> `curveK R K W`, and `n ≠ 0` (both in ℤ and in `R`) a multiplier such that `n • P = P' = (x', y')`
> is also a nonsingular affine point. If the x-coordinate `x'` of `n • P` is integral — given
> explicitly by `c : R` with `algebraMap R K c = x'` — then the x-coordinate `x` of `P` is integral
> (`IsLocalization.IsInteger R x`).

Mathematically this is the **x-coordinate integral-descent step of the Nagell–Lutz theorem**, in
UFD generality. The multiplication-by-`n` formula gives `x(n • P) = Φₙ(x)/ΨSqₙ(x)`, hence
`x' · ΨSqₙ(x) = Φₙ(x)`, so `x` is a root of the polynomial `Φₙ − C c · ΨSqₙ ∈ R[X]`. That polynomial
is **monic** (because `deg Φₙ = n² > n² − 1 = deg ΨSqₙ ≥ deg(C c · ΨSqₙ)`), so a fraction-field root
of it lies in `R` — the integral / rational-root theorem.

Variables / typeclasses (Lean side):
- `{R} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]` — the base ring (a UFD).
- `{K} [Field K] [DecidableEq K] [Algebra R K] [IsFractionRing R K]` — the fraction field.
- `(W : WeierstrassCurve R)` — the curve (section variable, explicit).
- `{x y : K}` — affine coordinates of `P`, a priori only in `K`.
- `{n : ℤ}` — the multiplier (the ℤ-action on the point group).
- `{x' y' : K}` — affine coordinates of `P' = n • P`.
- `{c : R}` — the integral witness for `x'`.

Hypotheses (Lean side):
- `(hns : (curveK R K W).toAffine.Nonsingular x y)` — `P` nonsingular.
- `(hn : n ≠ 0)` and `(hn_R : (n : R) ≠ 0)` — nonzero multiplier (both forms; over ℤ the second is `exact_mod_cast` of the first, but over a general `R` of positive characteristic the ℤ-nonzeroness need not transfer, so both are genuinely needed — see Phase 4 row 4).
- `(hns' : (curveK R K W).toAffine.Nonsingular x' y')` — `P'` nonsingular.
- `(hnP : n • (Affine.Point.some _ _ hns) = Affine.Point.some _ _ hns')` — `n • P = P'`.
- `(hc : algebraMap R K c = x')` — `x'` is integral, with explicit witness `c`.

Conclusion (math): `x ∈ R` (i.e. `x` is in the image of `algebraMap R K`).
Conclusion (Lean): `IsLocalization.IsInteger R x`.

Proof shape (3 substantive lines, body lines 72–77):
1. `hcoord := x_coord_nsmul_eq W …` — the multiplication-by-`n` x-coordinate identity `x' · ΨSqₙ(x) = Φₙ(x)` (the ~21-line Jacobian-bridge lemma, same file lines 39–62).
2. `hroot : aeval x (W.Φ n − C c * W.ΨSq n) = 0` — pushes `hcoord` through `curveK`/`map_Φ`/`map_ΨSq`/`aeval_def`/`eval₂_eq_eval_map` and closes by `linear_combination -hcoord`.
3. `exact isInteger_of_is_root_of_monic (monic_Φ_sub_smul_ΨSq W hn_R c) hroot` — the **mathlib** integral-root theorem applied to the monic polynomial (monicity is the same-file `monic_Φ_sub_smul_ΨSq`, lines 26–35).

---

### Size classification (Phase 2a)

Verdict: **BIG (borderline)** — it is a structural, load-bearing step of a **person-named theorem**
(Nagell–Lutz). On its own it is a `theorem` (not a new structure), but by the skill's "theorem named
after a person" criterion the named result's load-bearing lemmas are treated as BIG. It carries the
genuinely-novel mathematics of the track (the EC-group-law ↔ division-polynomial bridge), unlike its
ℤ/ℚ shadows.

(Literature width is EXHAUSTIVE regardless of BIG/SMALL.)

### One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure` → one-line check is **n/a**. Body is ≈3 substantive
lines of real content (coordinate identity → root fact → integral-root theorem), not a one-liner.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "if n*P integral then P integral" elliptic curve division polynomial monic numerator Nagell-Lutz proof | yes  | `x(nP) = φₙ/ψₙ²`; `Φₙ − x'·ΨSqₙ` monic in x; root-of-monic ⇒ integral | Silverman AEC VIII; Washington; Alpoge "Nagell-Lutz, quickly" (Harvard); MIT 18.782 Lec #24; arXiv:1108.3051 — all use the monic-numerator descent |
|  2 | WebSearch (general / theorem)    | elliptic curve multiplication x-coordinate phi_n psi_n^2 division polynomial integrally closed integral point descent | yes  | `[n]P = (φₙ/ψₙ², ωₙ/ψₙ³)`; argument needs only that base is integrally closed | Wikipedia "EC point multiplication"; the descent runs over any **integrally closed** base; arXiv:1108.3051 (explicit div-poly valuations) |
|  3 | WebSearch (named-after / aliases / generalisation) | Nagell-Lutz theorem generalization number field ring of integers Dedekind domain imaginary quadratic | yes  | same descent with base = ring of integers `𝒪_K` (a Dedekind, hence integrally closed, domain) | arXiv:2509.07524 (2025) "Nagell–Lutz for Imaginary Quadratic Fields"; Wikipedia: "generalizes to arbitrary number fields and more general cubic equations"; p-adic notes (Anqi Li) — confirms ℤ/ℚ is a specialisation, the natural base is integrally closed |
|  4 | ChatGPT MCP                      | (intended) "At what ring generality is the x(nP)-integral ⇒ x(P)-integral descent standardly stated — UFD, Dedekind, or integrally closed? Is UFD the natural ceiling or can it be IsIntegrallyClosed?" | n/a  | —                                | MCP server down per task brief. Substituted by rows 1–3, 9, 10 + the mathlib primitive analysis (Phase 5): the descent's only ring-theoretic need is "root of monic ⇒ in ring", whose mathlib-maximal form is `IsIntegrallyClosed` (`algebraMap_eq_of_integral`), with UFD as a specialisation. |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/` and `refs/NagellLutz/`                         | n/a  | (no references dir)               | `.mathlib-quality/references/` absent; `refs/` symlink absent. Recorded n/a. |
|  6 | nLab                             | "Nagell-Lutz theorem" / "division polynomial" / "elliptic curve torsion"                                | n/a  | —                                | nLab has no Nagell–Lutz / x-descent page; the statement is arithmetic, not categorical. n/a. |
|  7 | nCatLab (if categorical)         | —                                                                                                      | n/a  | —                                | Not a categorical concept. |
|  8 | Stacks Project (if alg geom)     | "elliptic curve torsion integral point" / "division polynomial"                                        | n/a  | —                                | Stacks has the scheme-theory of elliptic curves but not the arithmetic of rational torsion / Nagell–Lutz / division-polynomial integrality. n/a. |
|  9 | MathOverflow / Math.StackExchange| Nagell-Lutz nP integral implies P integral division polynomial generality; "x(nP) integral ⇒ x(P) integral" | yes  | confirms the monic-numerator route; threads note the argument needs only an integrally-closed / DVR base | MO/MSE Nagell–Lutz threads reproduce the bounded-denominator + monic-numerator argument; treated as an internal step (named result = Nagell–Lutz itself) |
| 10 | recent arXiv (last 5 years)      | Nagell-Lutz imaginary quadratic / number-field generalization; valuations of division polynomials      | yes  | NL generalised to number fields (integrally closed bases) | arXiv:2509.07524 (2025); arXiv:1108.3051 — the result is actively generalised beyond ℤ/ℚ to integrally-closed bases; ℤ/ℚ is a specialisation, not the ceiling |

Protocol pass: WebSearch ran 3 distinct queries at different generality levels (specific x-descent /
general φₙ-ψₙ² multiplication form / named-after-and-generalisation) ✓; ChatGPT MCP attempted but
server down, documented with a substitute that resolves the same generality question via the mathlib
primitive ✓; local refs checked (absent → n/a) ✓; nLab ✓; Stacks / nCatLab / MO / arXiv each checked
or n/a-with-reason ✓.

### Literature summary (Phase 3)

Concept identified as: the **x-coordinate integral-descent step of Nagell–Lutz** — "if `x(n • P)` is
integral then `x(P)` is integral" — via the multiplication-by-`n` x-coordinate formula
`x([n]P) = Φₙ(x)/ΨSqₙ(x)` (mathlib names `Φ`/`ΨSq`), with `Φₙ` monic and `deg Φₙ > deg ΨSqₙ`, reducing
x-integrality to the integral-root theorem for monic polynomials.

Sources agree on the standard form: **yes**. Every treatment (Silverman AEC VIII; Washington; the MIT
18.782 lecture; Alpoge's "Nagell-Lutz, quickly"; Wikipedia; the EDS / explicit-valuation literature
arXiv:1108.3051, arXiv:0802.2651) uses the same division-polynomial denominator route. The standalone
*named* result is the **Nagell–Lutz theorem**; the x-descent is packaged as a step inside it (Silverman
routes the full NL through formal groups / p-adic valuations; the division-polynomial presentation is
the Washington/"quickly" one, which is what the project formalises).

Most general standard form: the argument needs only that the base ring is **integrally closed in its
fraction field** (so that a fraction-field element which is a root of a monic polynomial over the ring
lies in the ring). Classically stated over ℤ/ℚ; actively generalised in the literature to rings of
integers of number fields and DVRs (all integrally closed). The project proves the **UFD** form, which
is one typeclass-notch below `IsIntegrallyClosed` and is the level at which mathlib's integral-root
primitive `isInteger_of_is_root_of_monic` is stated.

Generality dimensions where the literature varies:
  - base ring: ℤ (classical) → ring of integers `𝒪_K` / Dedekind → general integrally closed domain.
    Most general standard = **integrally closed domain**; the project realises **UFD** (a sub-case).
  - integrality predicate: "`∈ ℤ`" → "in the image of `algebraMap R K`" = `IsLocalization.IsInteger R`
    (the project already uses the latter, mathlib-idiomatic form).

Disagreement with the literature: none. The Lean statement is the standard x-descent; the only
generality gap is UFD vs. the integrally-closed ceiling.

---

### Generality analysis — `x_isInteger_of_nsmul_x_isInteger`

Literature-standard form (Phase 3): the x-descent over an **integrally closed** base `R` with fraction
field `K`, integrality = `IsLocalization.IsInteger R`. The project is at **UFD**, one notch narrower.

| # | Parameter / hypothesis            | Current Lean form                                  | Literature-standard / mathlib-maximal form           | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|----------------------------------------------------|------------------------------------------------------|---------------------|----------------------------------|
| 1 | base ring of curve `W`            | `[CommRing R][IsDomain R][UniqueFactorizationMonoid R]` | `[CommRing R][IsDomain R][IsIntegrallyClosed R]`     | **YES (one notch)** | The whole proof except the final step needs only `CommRing`+`IsDomain` (division polys `Φ`/`ΨSq`, degrees, `curveK`, the coordinate identity, monicity). The **only** use of UFD is the last call `isInteger_of_is_root_of_monic` — whose mathlib-maximal form is `IsIntegrallyClosed.algebraMap_eq_of_integral` (`IntegrallyClosed.lean:243`). Swap UFD → `IsIntegrallyClosed`, replace the final call by `algebraMap_eq_of_integral` applied to the `IsIntegral` witness of the monic root. CHEAP. |
| 2 | coordinate field                  | `[Field K][Algebra R K][IsFractionRing R K]`       | same                                                 | NO (already maximal)| Uses only `IsFractionRing R K`; `K = Frac R` is exactly the right abstraction. `[DecidableEq K]` is a mild classical-decidability artefact (could likely be `omit`/`Classical`-derived). |
| 3 | integrality predicate             | `IsLocalization.IsInteger R x` (concl.); `c : R, algebraMap R K c = x'` (hyp.) | `IsLocalization.IsInteger R`                       | NO (already idiomatic, but see note) | The conclusion is already mathlib's `IsInteger`. The **hypothesis** is phrased as an explicit witness `(c : R)(hc : algebraMap R K c = x')` rather than `IsLocalization.IsInteger R x'`; the two are interchangeable (`IsInteger` unfolds to exactly `∃ c, algebraMap R K c = x'`). For mathlib, taking `hx' : IsInteger R x'` and `obtain`-ing the witness is the symmetric, idiomatic form (the bundling sibling `isInteger_of_nsmul_isInteger` already does this `obtain`). |
| 4 | `n ≠ 0`                           | `(hn : n ≠ 0)` AND `(hn_R : (n : R) ≠ 0)`          | both                                                 | NO (essential)      | Both are genuinely needed: `hn` for the point/`smul` reasoning, `hn_R` for `natDegree_ΨSq` / monicity. Over a general `R` they are independent (positive characteristic). Correct as-is. |
| 5 | model generality                  | general Weierstrass `a₁..a₆`                        | general                                              | NO (already general)| Correct — full Weierstrass model, not short. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD — by a single typeclass notch** (UFD instead
of the literature/idiomatic-maximal `IsIntegrallyClosed`). This is a *much* milder gap than its ℤ/ℚ
siblings (which were 3 notches narrower); the project has already done the hard generalisation
(ℤ → UFD, ℚ → `Frac R`, `∃ cast` → `IsLocalization.IsInteger`).

Number of weakening opportunities found: **1 substantive** (row 1: UFD → `IsIntegrallyClosed`) + 1
cosmetic (row 3: hypothesis `c : R, algebraMap R K c = x'` → `IsInteger R x'`).

Proposed restatement (the integrally-closed form):

```lean
theorem x_isInteger_of_nsmul_x_isInteger
    {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve R)
    {x y : K} (hns : (curveK R K W).toAffine.Nonsingular x y)
    {n : ℤ} (hn : n ≠ 0) (hn_R : (n : R) ≠ 0)
    {x' y' : K} (hns' : (curveK R K W).toAffine.Nonsingular x' y')
    (hnP : n • (Affine.Point.some _ _ hns) = Affine.Point.some _ _ hns')
    (hx' : IsLocalization.IsInteger R x') :
    IsLocalization.IsInteger R x
```

Cost of restatement: **CHEAP** — only the final line changes. `monic_Φ_sub_smul_ΨSq` already needs
only `CommRing`+`IsDomain` (it `omit`s UFD — see PIDIntegralMultiple.lean:24). The terminal
`isInteger_of_is_root_of_monic hmonic hroot` becomes:
`IsIntegrallyClosed.algebraMap_eq_of_integral (R := R) ⟨_, hmonic, hroot⟩` (a monic root is integral),
giving `IsInteger R x`. `[DecidableEq K]` can be dropped. (Note: EXPENSIVE considerations do not arise;
and per the skill, cost is not the verdict driver — the verdict is driven by the existence of the real
weakening.)

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                 | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                      | no       | already typeclass-driven (`Nonsingular`, `IsFractionRing`, `IsLocalization.IsInteger`) | — |
|  2 | sequences/metric → filters/topological?                                                                  | no       | purely algebraic; no topology/limits | — |
|  3 | construct an object → universal-property class?                                                          | no       | it is a Prop, not a construction | — |
|  4 | set-with-closure-predicate → bundled substructure?                                                       | no       | n/a | — |
|  5 | vector-space/field-specific → weaken via typeclass hierarchy?                                            | **YES (mild)** | `UniqueFactorizationMonoid R` → `IsIntegrallyClosed R` (row 1 above); hypothesis witness → `IsInteger R x'` (row 3) | full `IsIntegrallyClosed` API; applies over **all** integrally closed bases (Dedekind / `𝒪_K` / DVR / `k[t]`), not just UFDs — directly the arXiv:2509.07524 number-field-`𝒪_K` territory, some of which are not UFDs |
|  6 | 1-categorical → higher-categorical?                                                                      | no       | n/a | — |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive/monoid?                                                       | no       | the multiplier `n` is correctly `ℤ` (the ℤ-action on the point group); the base ring is already abstracted (row 5) | — |
|  8 | concrete-object proof betrays an abstract form (named identifier vanishes after first unfolding)?         | partial  | the ℤ/ℚ siblings ARE this case (their bodies delegate entirely to this UFD lemma — the named ℤ/ℚ objects vanish immediately). For *this* lemma the abstract form it would collapse to is the `IsIntegrallyClosed` one in row 5 — the UFD typeclass is the only thing the body "specialises". |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes — mild** (coincides with the row-1 literature weakening): state over
`IsIntegrallyClosed R` rather than `UniqueFactorizationMonoid R`, and take the x'-integrality
hypothesis as `IsInteger R x'`.
  - Proposed mathlib-idiomatic restatement: the `IsIntegrallyClosed` signature above.
  - Cost: **CHEAP** (only the final proof line; the rest of the development is already `CommRing`+`IsDomain`).
  - Mathlib downstream this enables: the descent then applies to **every** integrally closed base —
    rings of integers `𝒪_K` of number fields (including the non-UFD ones, where the class group is
    nontrivial — exactly the arXiv:2509.07524 setting), DVRs, `k[t]` (function-field EC / EDS) — not
    only the UFD sub-case. Composes with mathlib's `IsIntegrallyClosed` / `IsFractionRing` /
    `IsLocalization.IsInteger` API.
  - Real mathematical improvement (not "looks cooler"): the natural ceiling of the Nagell–Lutz descent
    is integral-closedness (a fraction-field root of a monic is in the ring — that is *literally*
    `IsIntegrallyClosed`), and the literature generalises NL precisely to integrally-closed `𝒪_K` of
    nontrivial class group, which UFD excludes. The UFD hypothesis is an artefact of which mathlib
    integral-root lemma was reached for, not a mathematical need.

---

### Diamond / defeq risk — `x_isInteger_of_nsmul_x_isInteger`

n/a — declaration kind is `theorem` (Phase 4.5 skipped; theorems introduce no definitional equalities
or typeclass-search paths).

---

### Mathlib search-status: `x_isInteger_of_nsmul_x_isInteger`

[A] Lean-Finder       — (index MCP unavailable in this environment)                                   n/a: substituted by [D]/[E] grep on the pinned mathlib tree
[B] Loogle            `WeierstrassCurve.ΨSq`/`Φ` ↔ `Affine.Point` smul; `IsInteger _ (… • …)`         no hits — mathlib never relates `n • P` (group law) to `Φ`/`ΨSq`
[C] LeanSearch        "if x-coordinate of n times a point on an elliptic curve is integral then the point's x is integral" no hits
[D] Grep mathlib src  `Nagell`, `Lutz`, `x_isInteger_of_nsmul`, `nsmul.*[Ii]nteger`, `[Ii]nteger.*nsmul` in `Mathlib/`  no relevant hits (only "Lutz" = author Patrick Lutz, AbelRuffini header)
[E] Name pattern      `isInteger_of_nsmul`, `x_isInteger_of`, division-poly smul formula              no hits in mathlib

Detailed grep evidence (this run, over the pinned `.lake/packages/mathlib`):
- `grep -rli "nagell\|lutz" Mathlib/` → the only "Lutz" hits are author **Patrick Lutz** (FieldTheory
  copyright headers, e.g. `AbelRuffini.lean:4`); "Nagell" matches nothing. **Nagell–Lutz is not in mathlib.**
- `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/{Basic,Degree}.lean` **do** define
  `ΨSq` (`Basic.lean:246`), `Φ` (`Basic.lean:361`), `ψ`, `preΨ`, and the degree/leading-coeff API
  `natDegree_ΨSq` (`Degree.lean:361`), `natDegree_Φ`, `leadingCoeff_Φ` (`Degree.lean:39–42`). But
  `Basic.lean` relates them to the **coordinate ring only** (`Affine.CoordinateRing.mk_φ`,
  `mk_Ψ_sq`, `mk_ψ` — lines 350/454/498); there is **no** statement connecting the `Affine.Point`
  group law's `n • P` to `Φ`/`ΨSq`. A grep for `nsmul`/`zsmul` near points in those files returns
  nothing relevant. So mathlib lacks the bridge `x(n • P) · ΨSqₙ(x) = Φₙ(x)`.
- The only mathlib building block actually used at the end: `isInteger_of_is_root_of_monic`
  (`Mathlib/RingTheory/Polynomial/RationalRoot.lean:115`, stated over a **UFD** `A` with
  `IsFractionRing A K`), of which the strictly-more-general `IsIntegrallyClosed.algebraMap_eq_of_integral`
  (`IntegrallyClosed.lean:243`) is the parent.

Searched for both: the project's UFD form AND the literature-maximal `IsIntegrallyClosed` form. **Neither
is in mathlib.** Mathlib has the division polynomials, their degrees, and the integral-root theorem, but
not the smul→division-polynomial bridge nor any Nagell–Lutz descent.

Concluded: **not in mathlib** (all methods exhausted, both the UFD form and the integrally-closed form).

---

### Call sites — `x_isInteger_of_nsmul_x_isInteger` (Phase 6.0)

Internal use count: **K = 2** (within the project, NOT counting the declaring file's own decl head).
External-to-file callers: 1 distinct file (`GeneralIntegralMultiple.lean`); plus 1 same-file caller.

| Caller file:line                         | Usage pattern (one-line excerpt)                                                  |
|------------------------------------------|------------------------------------------------------------------------------------|
| PIDIntegralMultiple.lean:88 (same file)  | `obtain ⟨x₀, hx₀⟩ := x_isInteger_of_nsmul_x_isInteger W hns hn hn_R hns' hnP hc`  |
| GeneralIntegralMultiple.lean:73          | `isInteger_int_iff.mp <| PID.x_isInteger_of_nsmul_x_isInteger W hns hn (by exact_mod_cast hn) hns' hnP (by simpa … using hc)` |

So it has **real consumers**: the same-file bundling lemma `isInteger_of_nsmul_isInteger` (the x∧y
packaged form), and the ℤ/ℚ shadow `x_integral_of_nsmul_x_integral_general` (which is itself a thin
specialisation of this). Unlike its ℤ/ℚ shadow (K = 0, a dead wrapper), **this UFD lemma is a live API
node** — it is the thing the shadows delegate to.

Inline-derivation grep (was the equivalent re-derived elsewhere without using this decl?):
  - No. The ℤ/ℚ track does **not** re-derive the x-descent; it calls this lemma. The only "parallel" is
    the **PrimeOrder** track (`PIDPrimeOrder.lean`), which derives x-integrality for prime-order torsion
    by a *different* route (squarefree leading coefficient + denominator bound), not by re-deriving this
    `n • P` descent. So no redundant inline re-derivation of *this* statement exists.

Composability signal (per the call-sites table): **K = 2 internal uses, no inline re-derivation, and a
downstream consumer in another file** → real API node, consumers depend on it → leans **YES**.

---

### Composition check (Phase 6)

Can `x_isInteger_of_nsmul_x_isInteger` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: `isInteger_of_is_root_of_monic <monic> <root>` (mathlib).
  - Mathlib decls used: `isInteger_of_is_root_of_monic` (`RationalRoot.lean:115`).
  - Result: **fails as a standalone ≤3-mathlib-call composition.** The call needs two inputs mathlib
    does not supply:
      (a) **monicity** of `Φₙ − C c · ΨSqₙ` — a degree argument (project lemma `monic_Φ_sub_smul_ΨSq`,
          built on mathlib's `natDegree_Φ`/`leadingCoeff_Φ`/`natDegree_ΨSq` + `Monic.sub_of_left`, but
          itself a multi-step proof, not a mathlib one-liner); and
      (b) `aeval x (Φₙ − C c · ΨSqₙ) = 0` — which comes from the **coordinate identity**
          `x' · ΨSqₙ(x) = Φₙ(x)` = `x_coord_nsmul_eq`, a ~21-line proof going through Jacobian
          coordinates (`X_eq_of_equiv`, `zsmul_eq_smulEval`, `Jacobian.Point.toAffineAddEquiv`,
          `evalEval_φ_eq_eval_Φ`, `evalEval_Ψ_sq_eq_eval_ΨSq`). **Mathlib has none of this** — it has
          the division polynomials and the point group law as *separate* objects with no bridge.
  - Notes: this is a genuine multi-lemma development, not a 1–3 mathlib-call composition.

Attempt 2 (different angle — does mathlib's `IsIntegrallyClosed` API shortcut it?): no — the missing
piece is the same coordinate identity (b); the integral-closedness only changes which terminal lemma
closes the final root-of-monic step.

Conclusion: **NOT-COMPOSABLE from mathlib** in ≤3 calls. The substantive content (the
smul→`Φ`/`ΨSq` coordinate identity) is missing from mathlib; only the terminal integral-root step is a
mathlib one-liner.

(Note: this is *not* the ℤ/ℚ-shadow situation. The shadows are 1-call specialisations **of this
lemma**; this lemma is the genuinely-novel content holder and is not composable from mathlib primitives.)

---

## Verdict: `LutzNagell.PID.x_isInteger_of_nsmul_x_isInteger`

**Category:** YES-but-generalise-first

**Evidence:**
- Literature search (Phase 3): standard x-coordinate integral-descent step of Nagell–Lutz (Silverman
  AEC VIII; Washington; Alpoge; Wikipedia; arXiv:1108.3051). Stated over ℤ/ℚ classically; the natural
  ceiling is an **integrally closed** base, to which the literature actively generalises NL
  (arXiv:2509.07524 — rings of integers of number fields, including non-UFD class groups).
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD by one typeclass notch** — the
  project's `UniqueFactorizationMonoid R` should be `IsIntegrallyClosed R` (Phase 4b row 1 / Phase 4c
  row 5). CHEAP restatement (only the terminal `isInteger_of_is_root_of_monic` call changes to
  `IsIntegrallyClosed.algebraMap_eq_of_integral`; the rest is already `CommRing`+`IsDomain`).
- Mathlib search (Phase 5): **not in mathlib** in either the UFD or the integrally-closed form. The
  smul→division-polynomial bridge `x(n • P) · ΨSqₙ(x) = Φₙ(x)` is conspicuously absent; only the
  building blocks (`Φ`/`ΨSq`, their degrees, `isInteger_of_is_root_of_monic`) are present.
- Composition check (Phase 6): **NOT-COMPOSABLE from mathlib** — the missing piece is the ~21-line
  coordinate identity `x_coord_nsmul_eq`, not a 1–3 call composition.

**Rationale (1–2 paragraphs):**

This declaration is the genuine, missing-from-mathlib content of the Nagell–Lutz x-descent — and,
unlike its `General*` ℤ/ℚ shadows, it is already stated at (very nearly) the mathlib-natural generality:
a UFD `R` with `K = Frac R`, integrality as `IsLocalization.IsInteger R`, a general Weierstrass model.
The hard generalisation (ℤ → UFD, ℚ → fraction field, `∃ cast` → `IsInteger`) is already done and
sorry-free; this is the lemma the ℤ/ℚ siblings delegate to (the sibling reports
`x_integral_of_nsmul_x_integral_general.md` and `integral_of_nsmul_integral_general.md` both name *this*
decl as the real upstreaming unit). Mathlib lacks it entirely: it has the division polynomials `Φ`/`ΨSq`
and the `Affine.Point` group law as separate objects, but **not the bridge** `x(n • P) · ΨSqₙ(x) = Φₙ(x)`
that this descent rests on, so the result is not composable from mathlib primitives.

The verdict is `YES-but-generalise-first` rather than `YES-add-as-is` for one concrete, gate-relevant
reason: Phase 4b found the form **strictly narrower than standard** by a single typeclass notch. The
Nagell–Lutz descent's only ring-theoretic need is "a fraction-field root of a monic polynomial over the
ring lies in the ring" — which is *literally* `IsIntegrallyClosed`, the mathlib-maximal form of the
terminal step (`IsIntegrallyClosed.algebraMap_eq_of_integral`, of which the project's
`isInteger_of_is_root_of_monic` is the UFD specialisation). The literature generalises NL precisely to
integrally-closed rings of integers `𝓞_K` of *nontrivial class group* (arXiv:2509.07524), which UFD
excludes — so the weakening is a real mathematical improvement, not cosmetics, and it is CHEAP (the
whole development except the last line is already `CommRing`+`IsDomain`). The skill's gate therefore
forbids YES-add-as-is and selects YES-but-generalise-first. (Cost is not the driver here; the driver is
the genuine UFD → `IsIntegrallyClosed` weakening to the literature/idiomatic ceiling.)

**Reason for the generalisation:**
  - LITERATURE-WEAKENING: Phase 4b row 1 found the UFD form strictly narrower than the integrally-closed
    standard form (the literature states and generalises Nagell–Lutz to integrally-closed `𝓞_K`).
  - MODERN-IDIOM (Bourbaki 2.0): Phase 4c row 5 — replace `UniqueFactorizationMonoid R` by the weaker
    `IsIntegrallyClosed R` (the natural ceiling of root-of-monic ⇒ integer) and take the x'-hypothesis
    as `IsInteger R x'`.

**Proposed restatement** (integrally-closed form; CHEAP — only the terminal step changes):

```lean
theorem x_isInteger_of_nsmul_x_isInteger
    {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve R)
    {x y : K} (hns : (curveK R K W).toAffine.Nonsingular x y)
    {n : ℤ} (hn : n ≠ 0) (hn_R : (n : R) ≠ 0)
    {x' y' : K} (hns' : (curveK R K W).toAffine.Nonsingular x' y')
    (hnP : n • (Affine.Point.some _ _ hns) = Affine.Point.some _ _ hns')
    (hx' : IsLocalization.IsInteger R x') :
    IsLocalization.IsInteger R x := by
  obtain ⟨c, hc⟩ := hx'
  -- coordinate identity + monicity unchanged (both need only CommRing+IsDomain):
  have hroot : aeval x (W.Φ n - C c * W.ΨSq n) = 0 := …  -- as now (x_coord_nsmul_eq + linear_combination)
  exact IsIntegrallyClosed.algebraMap_eq_of_integral ⟨_, monic_Φ_sub_smul_ΨSq W hn_R c, hroot⟩
```

Estimated cost of regeneralisation: **CHEAP**. `monic_Φ_sub_smul_ΨSq` already `omit`s
`UniqueFactorizationMonoid R` (PIDIntegralMultiple.lean:24); `x_coord_nsmul_eq` needs only
`CommRing`+`IsDomain` for the curve. The only edits: drop `[UniqueFactorizationMonoid R]` →
`[IsIntegrallyClosed R]`, drop `[DecidableEq K]` (likely), take `hx'` as `IsInteger R x'`, and replace
the terminal `isInteger_of_is_root_of_monic` by `IsIntegrallyClosed.algebraMap_eq_of_integral` on the
`IsIntegral` witness `⟨_, hmonic, hroot⟩`. EXPENSIVE considerations do not arise.

Mathlib downstream this enables (MODERN-IDIOM):
  - Applies over **every** integrally closed base, not just UFDs: rings of integers `𝓞_K` of number
    fields *including those with nontrivial class group* (the arXiv:2509.07524 Nagell–Lutz-for-`𝓞_K`
    territory — not all `𝓞_K` are UFDs), DVRs, and `k[t]` (function-field elliptic curves / EDS). The ℚ
    result is the `R := ℤ` instance.
  - The supporting smul↔division-polynomial bridge `x_coord_nsmul_eq` is itself net-new mathlib API: the
    canonical link between `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial` and the
    `Affine.Point` group law, currently absent. Torsion / height / EDS results would build on it.
  - Composes with mathlib's `IsIntegrallyClosed` / `IsFractionRing` / `IsLocalization.IsInteger` API.

Proposed mathlib location: `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Point.lean`
(new) for the smul-formula bridge `x_coord_nsmul_eq`, with the descent lemma either there or in a
`.../NagellLutz.lean`.

PR grouping: ship this x-descent **together with its prerequisites** as one coherent contribution — the
smul-formula bridge `x_coord_nsmul_eq`, the monic-polynomial lemma `monic_Φ_sub_smul_ΨSq`, and (for the
full point form) the y-step `y_isInteger_of_x_isInteger_on_curve` + the packaged
`isInteger_of_nsmul_isInteger`. The `General*` ℤ/ℚ twins are **not** separate contributions — they are
the `R := ℤ` specialisations and must not be upstreamed (their reports already say so). This is exactly
the bundle the `integral_of_nsmul_integral_general.md` report proposed; *this* x-only lemma is one of
its named members.

Pre-PR checklist before opening:
  - [ ] `/generalise LutzNagell.PID.x_isInteger_of_nsmul_x_isInteger` — confirm the UFD →
        `IsIntegrallyClosed` weakening goes through cleanly (terminal step swap), check whether
        `[DecidableEq K]` can be dropped, and confirm no *further* weakening is cheap.
  - [ ] `/cleanup` the PID-track files (full audit + diff gates) before the mathlib PR.
  - [ ] Pick a mathlib reviewer from recent `Mathlib/AlgebraicGeometry/EllipticCurve/` commits (the
        `DivisionPolynomial` authors).

Next action: run `/generalise LutzNagell.PID.x_isInteger_of_nsmul_x_isInteger` to perform the
UFD → `IsIntegrallyClosed` weakening (CHEAP — only the terminal integral-root step), then upstream the
integrally-closed form **together with the missing `x(n • P) · ΨSqₙ(x) = Φₙ(x)` division-polynomial
bridge** as a single PR. Do **not** upstream the `General*` ℤ/ℚ shadows.

---

## Next step

Run `/generalise LutzNagell.PID.x_isInteger_of_nsmul_x_isInteger` (weaken `UniqueFactorizationMonoid R`
→ `IsIntegrallyClosed R`; only the terminal `isInteger_of_is_root_of_monic` → `algebraMap_eq_of_integral`
line changes), then upstream the **integrally-closed** form plus the genuinely-missing smul↔division-
polynomial bridge `x_coord_nsmul_eq` — not the ℤ/ℚ specialisations. This is the real content holder of
the track; its `General*` siblings are thin shadows that delegate to it.
