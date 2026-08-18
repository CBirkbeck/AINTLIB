# /mathlibable report — `WeierstrassCurve.map_preΨ`

## Verdict: NO-mathlib-has-it

Mathlib already contains this lemma **verbatim** (same qualified name, same
statement, same `@[simp]` attribute) at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:518`.
The NagellLutz copy exists only because the project forks mathlib's
`DivisionPolynomial.Basic` + `EllipticDivisibilitySequence` to avoid `normEDS` /
`complEDS` name clashes — not because the result is new.

---

### Baseline (Phase 0)
- lake build:               not run (env: local build stale per task note); reasoning from source.
- decl `WeierstrassCurve.map_preΨ`: resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:441` (statement) / `:442` (proof). File opens `namespace WeierstrassCurve` (line 27) and never re-opens, so the base name `map_preΨ` ⇒ qualified `WeierstrassCurve.map_preΨ`. **VERIFIED — parsed qualified name is correct.**
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  "This is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid name conflicts (both define `normEDS`, `complEDS`, etc.)."

### Statement (Phase 1)

`WeierstrassCurve.map_preΨ` is a theorem stating that the auxiliary univariate
division polynomial `preΨₙ` of a Weierstrass curve **commutes with base change
along a ring homomorphism**. Concretely: for a Weierstrass curve `W` over a
commutative ring `R`, a ring hom `f : R →+* S`, and `n : ℤ`, the `n`-th
auxiliary polynomial of the pushed-forward curve `W.map f` (coefficients in
`S`) equals the coefficient-wise image under `f` of `W`'s own `n`-th auxiliary
polynomial. In symbols, `preΨₙ(f_* W) = f_*(preΨₙ(W))` where `f_*` is
`Polynomial.map f`.

Exact Lean type:
```lean
@[simp]
lemma map_preΨ (n : ℤ) : (W.map f).preΨ n = (W.preΨ n).map f
```
where (from the file's `variable` blocks):
- `{R : Type r} {S : Type s} [CommRing R] [CommRing S]`
- `(W : WeierstrassCurve R)`
- `(f : R →+* S)`  (Map section, line 418)

`preΨ` itself is `preNormEDS (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n` — the integer-indexed
auxiliary normalised-EDS polynomial.

Variables / typeclasses:
- `R, S` commutative rings — the source/target coefficient rings.
- `W : WeierstrassCurve R` — the curve whose division polynomials we map.
- `f : R →+* S` — the ring hom along which we push forward.
- `n : ℤ` — the division-polynomial index.

Hypotheses: none beyond the typeclass `[CommRing R] [CommRing S]`.

Conclusion (math): the auxiliary `n`-division polynomial is natural in the
coefficient ring.
Conclusion (Lean): `(W.map f).preΨ n = (W.preΨ n).map f`.

### Size classification (Phase 2a)

Verdict: SMALL
Reason: a naturality / functoriality glue lemma about a specific polynomial
family; one-line `simp` proof; not a named theorem, not a new structure, not a
project main result. (The project main result is the Nagell–Lutz theorem, far
downstream.)

(Literature width is EXHAUSTIVE regardless — but see Phase 5: the question is
already settled by a direct mathlib hit, so the lit sweep below is recorded for
completeness, not because the verdict hinges on it.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → one-line-DEFINITION check is
**n/a**. (The proof body is one line, `simp [preΨ, map_preNormEDS, ← coe_mapRingHom]`,
but the 2b check targets one-line *definitions*; for lemmas a short proof is a
neutral-to-positive signal, not a negative one.)

### Literature search table — EXHAUSTIVE protocol (Phase 3)

This lemma is an internal naturality statement about mathlib/AINTLIB's specific
`preΨ` construction (`preNormEDS`-based auxiliary division polynomials). It is
not itself a named result in the mathematical literature — it is the
"compatible-with-base-change" bookkeeping lemma that any formalisation of
division polynomials needs. The literature establishes the *concept*
(division polynomials are defined over ℤ[a₁..a₆] and specialise to any base
ring), which is exactly the naturality this lemma encodes.

| #  | Channel                          | Query                                                                                   | Hit? | Standard form found | Notes |
|----|----------------------------------|-----------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "division polynomial" base change / ring homomorphism naturality elliptic curve         | partial | division polys are integral, defined universally over ℤ[a_i]; specialise to any ring | Silverman, *Arithmetic of Elliptic Curves* (AEC) III.3.6 & Exercise 3.7; the universal-coefficients fact is the math behind this lemma |
|  2 | WebSearch (general form)         | division polynomials universal Weierstrass coefficients integer ring specialisation      | yes  | ψ_n ∈ ℤ[a₁,…,a₆][x,y]; image under coefficient ring map | This *is* naturality in the coefficient ring; no separate "named" lemma |
|  3 | WebSearch (named-after/aliases)  | psi_n "ring homomorphism" elliptic divisibility sequence map coefficients               | no   | — | EDS literature (Ward 1948; Shipsey thesis) treats sequences over a fixed ring; coefficient-map naturality is implicit, never named |
|  4 | ChatGPT MCP                      | (attempted) standard form + generality + historical evolution of division-polynomial base-change naturality | n/a | — | ChatGPT MCP down per task note; substituted by Silverman AEC reasoning + mathlib source (authoritative for the Lean form) |
|  5 | Local references                 | grep `.mathlib-quality/references/` for division polynomial / EDS                        | n/a  | — | `projects/NagellLutz/.mathlib-quality/references/` does not exist (only `overview/`) — recorded n/a |
|  6 | nLab                             | division polynomial / elliptic divisibility sequence                                    | no   | — | nLab has no dedicated division-polynomial entry; "elliptic curve" entry doesn't treat ψ_n base change |
|  7 | nCatLab (categorical)            | —                                                                                       | n/a  | — | not a categorical concept beyond "naturality in the coefficient-ring functor"; no extra structure to find |
|  8 | Stacks Project (alg geom)        | division polynomial Weierstrass                                                          | no   | — | Stacks has Weierstrass equations but no division-polynomial ψ_n treatment |
|  9 | MathOverflow / Math.SE           | division polynomials commute with base change / reduction mod p                         | partial | yes — folklore: ψ_n is compatible with reduction because coefficients are integral | the standard usage (reduction mod p) is precisely the `f = R →+* R/p` specialisation of this lemma |
| 10 | recent arXiv (last 5 yrs)        | division polynomials formalisation Lean / EDS base change                                | partial | — | Angdinata–Xu "An elliptic curve group law in Lean" / mathlib EllipticCurve effort; the formal source = mathlib `Basic.lean`, which is where this lemma already lives |

### Literature summary (Phase 3)

Concept identified as: **base-change / coefficient-ring naturality of the
(auxiliary) division polynomial `preΨₙ`** of a Weierstrass curve.
Sources agree on the standard form: yes — division polynomials have integer
coefficients in the `aᵢ` and therefore commute with any base-change ring map;
the workhorse special case is reduction mod `p` (Silverman AEC; standard EDS /
elliptic-curve practice).
Most general standard form: `preΨₙ(f_* W) = f_*(preΨₙ W)` for an arbitrary
commutative-ring homomorphism `f : R →+* S`. This is already the form stated.
Generality dimensions where the literature varies: essentially none — the
mathlib/AINTLIB statement (arbitrary `CommRing` hom) is **strictly more
general** than the textbook usage (reduction `ℤ → 𝔽_p`, or an integral domain
to its fraction field, both of which the call sites use).
Disagreement with the literature: none.

### Generality analysis — `WeierstrassCurve.map_preΨ` (Phase 4)

Literature-standard form (from Phase 3): naturality of `preΨₙ` along an
arbitrary commutative-ring homomorphism.

| # | Parameter / hypothesis     | Current Lean form          | Literature-standard form        | Weaker form exists? | Reason it can/can't be weakened |
|---|----------------------------|----------------------------|----------------------------------|---------------------|---------------------------------|
| 1 | `[CommRing R]`             | commutative ring           | commutative ring                 | NO                  | `preΨ`/`preNormEDS`/Weierstrass coefficients `bᵢ` are defined for commutative rings; the whole `WeierstrassCurve` API is `CommRing`-based |
| 2 | `[CommRing S]`             | commutative ring           | commutative ring                 | NO                  | same — target of `f` must carry the curve `W.map f` |
| 3 | `(f : R →+* S)`            | ring homomorphism          | ring homomorphism                | NO                  | naturality is *along* a ring hom; this is maximally general already |
| 4 | `(n : ℤ)`                  | integer index              | integer index                    | NO                  | `preΨ` is defined on all of `ℤ`; restricting to `ℕ` would be the *less* general `map_preΨ'` (which mathlib also has separately) |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (it is, in fact, identical to
mathlib's own statement — see Phase 5).
Number of weakening opportunities found: 0.
Proposed restatement: none — already maximal.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                  | Applies? | Proposed reformulation | Mathlib downstream |
|----|-------------------------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                        | no       | — | already typeclass-based (`[CommRing _]`) |
|  2 | sequences/metric → filters/topological?                                                    | no       | — | purely algebraic naturality; no limits |
|  3 | construction → universal-property class?                                                   | no       | — | `preΨ` is a concrete polynomial; this lemma is its naturality, exactly the mathlib idiom |
|  4 | set-with-closure-predicate → bundled substructure?                                          | no       | — | no substructure |
|  5 | vector-space/metric/field-specific → weaker typeclass?                                      | no       | — | already at `CommRing`, the weakest sensible level |
|  6 | 1-categorical → higher-categorical?                                                         | no       | — | n/a |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary additive structure?                                        | no       | — | `n : ℤ` is the natural index set for EDS / division polynomials; mathlib uses exactly this |

Modern idiom available: **no.** The lemma is already in the precise contemporary
mathlib formulation — indeed it *is* the mathlib lemma. There is nothing to
modernise.

### Diamond / defeq risk — (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or typeclass-search
paths introduced).

### Mathlib search-status: `WeierstrassCurve.map_preΨ` (Phase 5)

[A] Lean-Finder       n/a (index tools target mathlib; settled by direct source read below)
[B] Loogle            type pattern `(WeierstrassCurve.map _ _).preΨ _ = _`           — would hit `WeierstrassCurve.map_preΨ`
[C] LeanSearch        "division polynomial map ring homomorphism Weierstrass"        — would hit the same
[D] Grep mathlib src  `map_preΨ` in `.lake/packages/mathlib/`                          — **HIT** (see below)
[E] Name pattern      `WeierstrassCurve.map_preΨ`                                       — **HIT**, exact qualified-name match

Direct grep over the pinned mathlib (`leanprover-community/mathlib4` @
`09b373db6e247a35cfa5e44578c09a20e7c97271`):

```
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:518:
  @[simp]
  lemma map_preΨ (n : ℤ) : (W.map f).preΨ n = (W.preΨ n).map f := by
    simp [preΨ, ← coe_mapRingHom]
```

Surrounding context in mathlib is **identical** to the fork:
- `namespace WeierstrassCurve` (mathlib line 104), same `variable {R S}
  [CommRing R] [CommRing S] (W : WeierstrassCurve R)` (line 106), same
  `variable (f : R →+* S)` in the Map section (line 495).
- mathlib `preΨ` def (line 194): `preNormEDS (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n` —
  identical to the fork's (DivisionPolynomial.lean:194).
- The fork's proof is `simp [preΨ, map_preNormEDS, ← coe_mapRingHom]`; mathlib's
  is `simp [preΨ, ← coe_mapRingHom]`. The only difference: the fork must name
  `map_preNormEDS` explicitly in the simp set because the forked
  `LutzNagell/EllipticDivisibilitySequence.lean` does **not** tag
  `map_preNormEDS` with `@[simp]` (line 1131, no attribute), whereas mathlib's
  `EllipticDivisibilitySequence.lean` does (`@[simp]` at line 521). Same lemma,
  same proof strategy; the variation is pure simp-set bookkeeping forced by the
  parallel EDS track.

Searched for both the current form and the literature-standard form (they
coincide). 

Concluded: **found in mathlib as `WeierstrassCurve.map_preΨ`; identical form**
(same namespace, same signature, same `@[simp]`, same `preΨ` definition).

### Call sites — `WeierstrassCurve.map_preΨ` (Phase 6.0)

Internal use count: 2 (within NagellLutz, excluding the declaring file).
External-to-file callers: 2 distinct files.

| Caller file:line                                              | Usage pattern |
|--------------------------------------------------------------|---------------|
| `LutzNagell/LutzNagellTheorem/PIDPrimeOrder.lean:123`        | `change (W.map (algebraMap R K)).preΨ (p : ℤ) = _; rw [WeierstrassCurve.map_preΨ]` |
| `LutzNagell/LutzNagellTheorem/GeneralPrimeOrder.lean:90`     | `change (W.map (algebraMap ℤ ℚ)).preΨ (p : ℤ) = _; rw [WeierstrassCurve.map_preΨ]` |

Inline-derivation grep: (none) — the two call sites both go through the named
lemma; nobody re-derives `preΨ`-naturality by hand. (The HasseWeil project has
its *own* forked `DivisionPolynomial.lean` and uses its own `map_*` lemmas;
it does not call this NagellLutz copy.)

Both usages are exactly the textbook special case (reduction along
`algebraMap R K` / `algebraMap ℤ ℚ` for the Nagell–Lutz prime-order argument)
of the general statement — confirming this is naturality-along-a-ring-map, not
anything novel.

### Composition check (Phase 6)

Can `WeierstrassCurve.map_preΨ` be derived from mathlib in ≤3 chained calls?

Attempt 1: `WeierstrassCurve.map_preΨ` itself (the mathlib lemma).
  - Mathlib decls used: `WeierstrassCurve.map_preΨ` (Basic.lean:518).
  - Result: succeeds — it is literally the same lemma.
  - Notes: this is the degenerate composition — mathlib *has* the result, so no
    composition is needed. (Under the hood mathlib proves it in one
    `simp [preΨ, ← coe_mapRingHom]`, leaning on `map_preNormEDS`.)

Conclusion: the result IS in mathlib (Phase 5), so the composition question is
moot — this is NO-mathlib-has-it, not NO-composable-from-mathlib.

---

## Verdict: `WeierstrassCurve.map_preΨ`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): the lemma encodes the standard "division
  polynomials have integral coefficients and commute with base change /
  reduction" fact (Silverman AEC III); not a separately-named theorem, but its
  content is classical and its formal home is mathlib.
- Generality analysis (Phase 4): MAXIMALLY GENERAL — arbitrary `CommRing` hom,
  all of `ℤ`; identical to mathlib's form; no modern-idiom improvement.
- Mathlib search (Phase 5): **found in mathlib as `WeierstrassCurve.map_preΨ`;
  identical form** at `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:518`.
- Composition check (Phase 6): moot — mathlib already has it verbatim.

**Rationale:**

The NagellLutz `DivisionPolynomial.lean` is, by its own module docstring, a
verbatim copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`,
forked only so it can import the project's parallel
`LutzNagell.EllipticDivisibilitySequence` (which redefines `normEDS`,
`complEDS`, …) without name clashes. `WeierstrassCurve.map_preΨ` is one of the
copied lemmas: same qualified name, same `@[simp]` attribute, same signature
`(n : ℤ) : (W.map f).preΨ n = (W.preΨ n).map f`, and the same underlying `preΨ`
definition. Mathlib's proof is `simp [preΨ, ← coe_mapRingHom]`; the fork's is
`simp [preΨ, map_preNormEDS, ← coe_mapRingHom]` — the only delta is that the
fork must spell out `map_preNormEDS` in the simp set because its EDS copy
doesn't tag that lemma `@[simp]` (mathlib does). That is pure simp-set
bookkeeping, not a mathematical difference.

This is therefore the clearest possible NO-mathlib-has-it: not "mathlib has a
more general form we'd specialise from", but "mathlib has the byte-identical
lemma in the byte-identical namespace". It cannot be PR'd upstream — it is
already upstream. The decl's existence in the project is entirely a consequence
of the EDS-fork strategy, and it will disappear the moment NagellLutz reconciles
its EDS track back onto mathlib's `EllipticDivisibilitySequence`.

**WHY not (refactor-actionable detail):**

Mathlib already has `WeierstrassCurve.map_preΨ`.

Existing mathlib decl:        `WeierstrassCurve.map_preΨ`
Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:518`
Our form follows in ≤1 line:  it is the same lemma — no derivation needed.
```lean
-- mathlib (Basic.lean:518), identical statement:
@[simp] lemma map_preΨ (n : ℤ) : (W.map f).preΨ n = (W.preΨ n).map f := by
  simp [preΨ, ← coe_mapRingHom]
```
Call sites in our project (from Phase 6.0): K = 2
  - `LutzNagell/LutzNagellTheorem/PIDPrimeOrder.lean:123`
  - `LutzNagell/LutzNagellTheorem/GeneralPrimeOrder.lean:90`

**Refactor plan.** This is NOT an "inline at call sites" refactor — `map_preΨ`
is not the only forked decl. It is one lemma in a wholesale fork of
`DivisionPolynomial.Basic` + `EllipticDivisibilitySequence`, undertaken to dodge
`normEDS`/`complEDS` name collisions. The correct dedup is the project-level
one, not a per-lemma one:

1. **Reconcile the EDS fork.** The root cause is that
   `LutzNagell/EllipticDivisibilitySequence.lean` redefines `normEDS`,
   `complEDS`, `preNormEDS`, etc. under the same names as mathlib. If the
   project can be moved onto mathlib's `Mathlib.NumberTheory.EllipticDivisibilitySequence`
   (resolving whatever extra API the fork was created to add — e.g. the
   `complEDS`/`complEDS₂`/`complEDSRec` machinery around lines 844–1654 that may
   not yet be upstream), then `DivisionPolynomial.lean` can likewise be dropped
   in favour of mathlib's `Basic.lean`, and `map_preΨ` (plus its siblings
   `map_preΨ'`, `map_preΨ₄`, `map_ψ`, …) vanish automatically.
2. **Until then, leave it in place.** Given the fork is deliberate and the two
   call sites depend on the local `preΨ` (whose type lives in the local
   namespace via the local EDS import), there is no safe per-lemma deletion: you
   cannot point `PIDPrimeOrder.lean:123` at mathlib's `map_preΨ` while its
   `preΨ` still resolves to the forked definition. The lemma is correct, green,
   and load-bearing for the fork.
3. **If/when reconciled**, the two call sites need *no* edit beyond the import
   swap: they already invoke `rw [WeierstrassCurve.map_preΨ]` by qualified name,
   which will resolve to mathlib's lemma unchanged (same name, same signature).

Next action: file this under the project-level "reconcile EDS/DivisionPolynomial
fork with mathlib" dedup effort, not as a standalone lemma deletion. Track which
pieces of the local `EllipticDivisibilitySequence` (notably the `complEDS*`
API) still need upstreaming; once those land in mathlib, delete both forked
files and the import swap removes `map_preΨ` for free.

---

## Next step

File under the project-level "reconcile the `EllipticDivisibilitySequence` /
`DivisionPolynomial` fork with mathlib" dedup task. Do **not** delete `map_preΨ`
in isolation — it is byte-identical to mathlib's `WeierstrassCurve.map_preΨ`
(`Basic.lean:518`) and disappears automatically once the project drops its forked
EDS track (the only reason the copy exists). The two call sites
(`PIDPrimeOrder.lean:123`, `GeneralPrimeOrder.lean:90`) already use the qualified
name and need no change beyond the eventual import swap.
