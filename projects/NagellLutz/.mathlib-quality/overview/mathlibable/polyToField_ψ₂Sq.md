# /mathlibable report — `WeierstrassCurve.Universal.polyToField_ψ₂Sq`

### Baseline (Phase 0)
- lake build:               ✓ toolchain resolves (Lean 4.32.0-rc1); local oleans stale per task note, but the decl elaborates from source and its dependencies are all present in mathlib + project.
- decl `WeierstrassCurve.Universal.polyToField_ψ₂Sq`: ✓ resolved at `projects/NagellLutz/LutzNagell/ZSMul.lean:154`
- kind:                      lemma (theorem)
- has sorry:                 no
- module docstring summary:  ZSMul.lean proves `zsmul_eq_smulEval` — the formula `n • P = (φₙ : ωₙ, ψₙ²)` in Jacobian coordinates via division polynomials and the *universal pointed Weierstrass curve* scaffold.

**Exact source statement + proof:**
```lean
lemma polyToField_ψ₂Sq : polyToField (C curve.Ψ₂Sq) = ψᵤ 2 ^ 2 := by
  rw [← map_pow, ψ_two, ψ₂_sq, map_add, map_mul, polyToField_polynomial, mul_zero, add_zero]
```

**Duplication note (as the task flagged).** This lemma exists *byte-identically* in two
forked project tracks:
- `projects/NagellLutz/LutzNagell/ZSMul.lean:154` (the target)
- `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:233`

Each project carries its *own* complete copy of the `Universal` scaffold
(`projects/NagellLutz/LutzNagell/Universal.lean` and
`projects/HasseWeil/HasseWeil/Auxiliary/Universal.lean`) — they are independent
duplicates, not a shared import. This is exactly the "duplicated General*/PID*
tracks" the task warned about.

---

### Statement (Phase 1)

`polyToField_ψ₂Sq` states the following:

Let `curve` be the **universal pointed Weierstrass curve** — the Weierstrass curve
over the multivariate polynomial ring `ℤ[a₁,a₂,a₃,a₄,a₆]` whose coordinate ring is
`Universal.Ring = curve.CoordinateRing = (ℤ[aᵢ][X][Y]) / ⟨W-polynomial⟩`, with
`Universal.Field := Frac(Universal.Ring)`. Let
`polyToField : Poly →+* Universal.Field` be the canonical ring map
`(algebraMap Universal.Ring Universal.Field) ∘ (AdjoinRoot.mk ⟨W-polynomial⟩)`
(so it sends the Weierstrass polynomial to `0`), and let
`ψᵤ n := polyToField (curve.ψ n)` be the image of the `n`-th division polynomial.

Then the image of the univariate polynomial `Ψ₂Sq = 4X³ + b₂X² + 2b₄X + b₆`
(coerced into `Poly` via `C`) equals the square of the universal 2-division
polynomial: `polyToField (C Ψ₂Sq) = (ψᵤ 2)²`.

Variables / typeclasses involved (Lean side):
- none free — `curve`, `polyToField`, `Universal.Field`, `ψᵤ` are all *fixed
  project-global constants* of the universal-curve construction.

Hypotheses (Lean side): none.

Conclusion (math): in the fraction field of the universal coordinate ring, the
image of `Ψ₂Sq` coincides with the square of the image of `ψ₂` — i.e. the
classical congruence `ψ₂² ≡ Ψ₂Sq (mod W-relation)`, pushed into `Frac`.

Conclusion (Lean): `polyToField (C curve.Ψ₂Sq) = ψᵤ 2 ^ 2` (an equality in `Universal.Field`).

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper rewrite lemma — it transports a known polynomial congruence through
the project's `polyToField` map. Not a named theorem, not a new structure, not a
`## Main results` entry. (Literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: 1 substantive line (a single `rw` chain).
One-liner verdict: n/a — kind is `lemma`, not a `def`. (One-liner check targets
`def`/`abbrev`/`structure` bodies; for a proof lemma the relevant signal is the
composition check in Phase 6, which is decisive here.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                              | Hit? | Standard form found                              | Notes |
|----|----------------------------------|----------------------------------------------------------------------------------------------------|------|--------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | division polynomial ψ₂ squared "4x³+b₂x²+2b₄x+b₆"                                                   | yes  | `ψ₂ = 2y+a₁x+a₃`; `ψ₂² → 4x³+b₂x²+2b₄x+b₆` after `Y=2y+a₁x+a₃` | the substitution *is* the Weierstrass relation; standard in Silverman/Washington |
|  2 | WebSearch (general / coordinate-ring form) | "coordinate ring" elliptic curve division polynomial image ψ₂ squared quotient Weierstrass relation | yes  | "in R[W], ψ₂² is congruent to Ψ₂Sq := 4X³+b₂X²+2b₄X+b₆" | top hit is the mathlib docs page for `DivisionPolynomial.Basic` itself |
|  3 | WebSearch (named-after / aliases)| "two-torsion polynomial" / `twoTorsionPolynomial` ψ₂ Weierstrass                                    | yes  | `Ψ₂Sq = twoTorsionPolynomial.toPoly` (mathlib `Ψ₂Sq_eq`) | the polynomial is the classical 2-torsion polynomial; congruence is folklore |
|  4 | ChatGPT MCP                      | "Is `polyToField(Ψ₂Sq)=ψᵤ(2)²` a named theorem, or routine from `ψ₂²=Ψ₂Sq+4f` with `f↦0`? Is the Frac-level version new vs the coordinate-ring `mk(ψ₂)²=mk(Ψ₂Sq)`?" | n/a  | MCP DOWN (Codex exec failed, as task warned) | fallback: answered from source + mathlib (channels 1-2 + Phase 5/6) — the congruence is folklore, and the Frac version is the coordinate-ring identity localized |
|  5 | Local references                 | grep `.mathlib-quality/references/`                                                                 | n/a  | directory absent                                 | no NagellLutz references dir; recorded n/a |
|  6 | nLab                             | "division polynomial" / "elliptic divisibility sequence"                                            | n/a  | nLab has no division-polynomial page at this granularity | concept is classical-AG, not categorical; the ψ₂²≡Ψ₂Sq congruence is below nLab's resolution |
|  7 | nCatLab (categorical)            | —                                                                                                  | n/a  | not a categorical concept                        | a polynomial congruence in a quotient ring; nothing higher-categorical |
|  8 | Stacks Project (alg geom)        | division polynomial / two-torsion                                                                   | n/a  | Stacks has no elliptic-curve division-polynomial chapter | this level of explicit Weierstrass computation is out of Stacks' scope |
|  9 | MathOverflow / Math.SE           | ψ₂ squared equals 4x³+b₂x²+2b₄x+b₆ generality                                                       | yes  | confirmed via the `Y=2y+a₁x+a₃` completion-of-square; standard exercise | no disagreement; treated as routine |
| 10 | recent arXiv (last 5 yr)         | "A recurrence relation for elliptic divisibility sequences" (2102.07573); ITP-2023 group-law proof  | yes  | division-polynomial congruences treated as routine lemmas, never named | confirms it is infrastructure, not a headline result |

The protocol passes: WebSearch ran 3+ queries at distinct generality (specific
`ψ₂²` form, coordinate-ring/quotient form, two-torsion-polynomial alias); ChatGPT
MCP was attempted and is down (documented, with source-based fallback); local refs
checked (absent); nLab/nCatLab/Stacks each looked at and recorded `n/a` with reason;
MathOverflow + arXiv hit.

### Literature summary (Phase 3)

Concept identified as: the **classical 2-division-polynomial congruence**
`ψ₂² ≡ Ψ₂Sq (mod W-relation)`, where `Ψ₂Sq = 4X³ + b₂X² + 2b₄X + b₆` is the
**two-torsion polynomial**. Equivalently: after the substitution `Y ↦ 2y+a₁x+a₃`
the Weierstrass equation becomes `Y² = 4x³+b₂x²+2b₄x+b₆`, and `ψ₂ = 2y+a₁x+a₃`,
so `ψ₂²` reduces to the RHS on the curve.
Sources agree on the standard form: yes.
Most general standard form: over any commutative ring `R`, in the coordinate ring
`R[W]` (or any `R`-algebra where the Weierstrass relation holds),
`(image of ψ₂)² = (image of Ψ₂Sq)`.
Generality dimensions where the literature varies:
  - base: from a field (Silverman) to an arbitrary commutative ring (mathlib's
    `DivisionPolynomial.Basic`). The most general is "any comm-ring `R`".
  - target algebra: the polynomial identity is `ψ₂² = C Ψ₂Sq + 4·f` (an *equation
    in the polynomial ring*, before any quotient — mathlib's `ψ₂_sq`/`C_Ψ₂Sq`);
    the congruence form lives in `R[W]` (mathlib's `mk_ψ₂_sq`); the project lemma
    lives one further step out, in `Frac(R[W])`.
Disagreement with the literature: none. The project's `polyToField (C Ψ₂Sq) = (ψᵤ 2)²`
is exactly the literature congruence transported into the universal fraction field.

---

### Generality analysis — `WeierstrassCurve.Universal.polyToField_ψ₂Sq`

Literature-standard form (from Phase 3): over any comm-ring `R`, the *polynomial*
identity `W.ψ₂ ^ 2 = C W.Ψ₂Sq + 4 * W.toAffine.polynomial` (mathlib `ψ₂_sq`), whose
quotient image gives `mk(ψ₂)² = mk(Ψ₂Sq)` in `R[W]` (mathlib `mk_ψ₂_sq`).

| # | Parameter / hypothesis            | Current Lean form                              | Literature-standard form                  | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|------------------------------------------------|-------------------------------------------|---------------------|----------------------------------|
| 1 | base ring                         | the *specific* `MvPolynomial Coeff ℤ` (universal aᵢ) | arbitrary comm-ring `R`                   | yes (already is, upstream) | the *general* statement is mathlib's `ψ₂_sq` over any `R`; this lemma is the **specialisation** to the universal base, then localised |
| 2 | target algebra                    | `Universal.Field = Frac(curve.CoordinateRing)` (project-private) | the polynomial ring (most general), or `R[W]` | the general forms already exist | mathlib's `ψ₂_sq` (poly ring) and `mk_ψ₂_sq` (`R[W]`) are *strictly more general* — they hold before localisation and over any base |
| 3 | the map                           | `polyToField` (project-private `Poly →+* Universal.Field`) | any ring hom killing the W-relation       | n/a — map is project-only | the statement is phrased through a construction (`polyToField`, `ψᵤ`) that does **not exist in mathlib** |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** — it is the universal-base,
`Frac`-localised *specialisation* of the general polynomial identity that mathlib
already states (`ψ₂_sq`) and that mathlib already pushes into the coordinate ring
(`mk_ψ₂_sq`).
Number of weakening opportunities: the general forms already exist upstream; the
lemma is downstream of them.
Proposed restatement: **none toward mathlib** — the right "general form" is mathlib's
existing `ψ₂_sq` / `mk_ψ₂_sq`, not a re-stated `polyToField_ψ₂Sq`. Generalising this
particular lemma would just reproduce `mk_ψ₂_sq` (which is there) or re-derive it in
`Frac` (which is a 1-step localisation, not a new theorem).
Cost of "restatement" toward the general form: n/a — the general form is already in
mathlib; this lemma is a consumer of it.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                          | Applies? | Proposed reformulation | Mathlib downstream |
|----|---------------------------------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | "let X be a foo" → typeclass/instance?                                                             | no       | already a bare equality through fixed constants | — |
|  2 | sequences/metric → filters/topology?                                                               | no       | purely algebraic identity | — |
|  3 | construct an object → universal-property class?                                                    | no       | the "universal curve" *is* a construction, but mathlib already has the universal coordinate-ring identity `mk_ψ₂_sq`; the project's `Frac`-wrapper adds no universal property | — |
|  4 | set-with-closure-predicate → bundled substructure?                                                 | no       | not a substructure question | — |
|  5 | vector-space/field-specific → weaken to module/ring?                                                | yes (already upstream) | the ring-general form is mathlib's `ψ₂_sq`/`mk_ψ₂_sq` over any comm-ring | mathlib already has this; the project lemma needlessly works in a *field* (`Frac`) when the identity is a ring identity |
|  6 | 1-categorical → higher-categorical?                                                                 | no       | n/a | — |
|  7 | concrete index (ℤ/ℝ) → arbitrary monoid/group?                                                     | no       | the index `2` is essential (it's the 2-division polynomial); not a generalisable index | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (no *new* mathlib-idiomatic restatement is warranted).
One-line reason: the genuinely idiomatic, ring-general formulation already exists in
mathlib as `ψ₂_sq` (polynomial ring) and `Affine.CoordinateRing.mk_ψ₂_sq` (`R[W]`).
The project lemma is the *less* general, `Frac`-localised, project-scaffold version —
the modernisation move is to *use* mathlib's identity, not to ship a new one.

---

### Diamond / defeq risk — (Phase 4.5)

n/a — declaration kind is `lemma` (a proof, not a `def`/`class`/`instance`); it
introduces no definitional equalities or typeclass-search paths.

---

### Mathlib search-status: `WeierstrassCurve.Universal.polyToField_ψ₂Sq`

[A] Lean-Finder       "image of ψ₂ squared equals Ψ₂Sq in coordinate ring" — covered by [C]/[D] below
[B] Loogle            `?f (C _) = _ ^ 2` style for division polynomials — no hit on a `polyToField`-shaped lemma (the map is project-only); the *building block* `ψ₂_sq` found via [D]
[C] LeanSearch / docs "ψ₂ squared congruent to Ψ₂Sq coordinate ring elliptic curve" → **mathlib docs page `DivisionPolynomial.Basic`** is the literal top web hit → `ψ₂_sq`, `C_Ψ₂Sq`, `mk_ψ₂_sq`
[D] Grep mathlib src  `Ψ₂Sq`, `ψ₂_sq`, `mk_ψ₂_sq`, `ψ_two`, `Universal.Field/polyToField` →
      - `ψ₂_sq : W.ψ₂ ^ 2 = C W.Ψ₂Sq + 4 * W.toAffine.polynomial`  (`DivisionPolynomial/Basic.lean:125`)
      - `C_Ψ₂Sq : C W.Ψ₂Sq = W.ψ₂ ^ 2 - 4 * W.toAffine.polynomial`  (`Basic.lean:120`)
      - `Affine.CoordinateRing.mk_ψ₂_sq : mk W W.ψ₂ ^ 2 = mk W (C W.Ψ₂Sq)`  (`Basic.lean:128`)
      - `ψ_two : W.ψ 2 = W.ψ₂`  (`Basic.lean:415`)
      - `Universal.Field` / `polyToField` / `curve` (the universal pointed scaffold) → **0 hits in mathlib**
[E] Name pattern      `polyToField_ψ₂Sq`, `polyToField`, `ψᵤ`, `Universal.Ring/Field` in mathlib → **0 hits** (project-only names)

Searched for both:
  - the user's current form (`polyToField (C Ψ₂Sq) = ψᵤ 2 ^ 2`): **not in mathlib** — phrased through the project-private `polyToField`/`ψᵤ`/`Universal.Field` scaffold, none of which exist in mathlib.
  - the literature-standard form (`ψ₂² ≡ Ψ₂Sq` in poly ring / `R[W]`): **IN mathlib** as `ψ₂_sq` + `mk_ψ₂_sq` + `C_Ψ₂Sq`, over an arbitrary comm-ring, strictly more general.

Concluded: **found the building blocks** (`ψ₂_sq`, `mk_ψ₂_sq`, `ψ_two`, `C_Ψ₂Sq`);
the exact `polyToField`-stated form is not in mathlib *because the `Universal.Field`
scaffold is project-only*, but the form is a ≤3-call composition of those blocks with
the project's own `polyToField_polynomial`.

---

### Call sites — `WeierstrassCurve.Universal.polyToField_ψ₂Sq`

Internal use count: **1** (within NagellLutz, excluding the declaring file's own line)
External-to-file callers: 1 distinct file (within NagellLutz).

| Caller file:line                 | Usage pattern (one-line excerpt) |
|----------------------------------|-----------------------------------|
| `projects/NagellLutz/LutzNagell/ZSMul.lean:267` | `simp only [… , polyToField_ψ₂Sq, map_sub, map_add, map_mul, map_pow, map_ofNat, polyToField_polynomial]` (inside the `Universal.Affine` `addX`/`slopeOne` computation, ~line 260–270) |

(For completeness — the *other project's* independent duplicate has the symmetric
single call site: `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:338`,
same `simp only` shape. That is a separate copy in a forked track, not a call into
NagellLutz's lemma.)

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?):
  - (none found, beyond the cross-project duplicate already noted)

Signal (per the Phase-6.0.1 table): **K = 1 internal use only** → leans toward
NO-composable / inline. The lemma is a one-off `simp` ingredient feeding a single
downstream `addX`-coordinate computation; it is not a broadly-reused API surface.

---

### Composition check (Phase 6)

Can `polyToField_ψ₂Sq` be derived from mathlib (+ the project's own `polyToField`
map lemmas) in ≤3 chained calls?

Attempt 1 (the actual proof, read off the source):
```lean
example : polyToField (C curve.Ψ₂Sq) = ψᵤ 2 ^ 2 := by
  rw [← map_pow, ψ_two, ψ₂_sq, map_add, map_mul, polyToField_polynomial, mul_zero, add_zero]
```
  - Mathlib decls used: `ψ_two` (`W.ψ 2 = W.ψ₂`), `ψ₂_sq`
    (`W.ψ₂ ^ 2 = C W.Ψ₂Sq + 4 * W.toAffine.polynomial`), and the generic `map_*`
    ring-hom lemmas (`map_pow`, `map_add`, `map_mul`).
  - Project glue used: `polyToField_polynomial` (`polyToField curve.polynomial = 0`)
    — the *defining* property of the project's quotient map, one line itself
    (`rw [polyToField_apply, AdjoinRoot.mk_self, map_zero]`).
  - Result: **succeeds** — three substantive rewrites (`ψ_two`, `ψ₂_sq`,
    `polyToField_polynomial`) plus `map_*` homomorphism distribution and
    `mul_zero/add_zero` cleanup. The mathematical content is *entirely* mathlib's
    `ψ₂_sq`; the wrapper only transports it across `polyToField`.

Conclusion: **COMPOSABLE** — the lemma is mathlib's `ψ₂_sq` pushed through the
project-private `polyToField` map (killing the W-relation via `polyToField_polynomial`),
i.e. a ≤3-call composition. No new mathematics. The equivalent at the coordinate-ring
level, `mk_ψ₂_sq`, is *already in mathlib*; this is its localisation into `Frac`.

---

## Verdict: `WeierstrassCurve.Universal.polyToField_ψ₂Sq`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the identity is the classical 2-division-polynomial
  congruence `ψ₂² ≡ Ψ₂Sq` (= two-torsion polynomial); folklore, never a named
  theorem; mathlib's own docs page was the top hit.
- Generality analysis (Phase 4): STRICTLY NARROWER THAN STANDARD — the
  ring-general identity already lives upstream (`ψ₂_sq`, `mk_ψ₂_sq`); this is its
  universal-base, `Frac`-localised specialisation. Modern-idiom: no new form
  warranted (the idiomatic form *is* mathlib's existing one).
- Mathlib search (Phase 5): building blocks present — `ψ₂_sq` (Basic.lean:125),
  `Affine.CoordinateRing.mk_ψ₂_sq` (Basic.lean:128), `ψ_two` (Basic.lean:415),
  `C_Ψ₂Sq` (Basic.lean:120). The `polyToField`/`ψᵤ`/`Universal.Field` scaffold is
  project-only (0 mathlib hits), so the exact stated form is not — and cannot be —
  in mathlib.
- Composition check (Phase 6): COMPOSABLE — the source proof itself is a ≤3-call
  composition (`ψ_two` → `ψ₂_sq` → `polyToField_polynomial`, plus `map_*` cleanup).

**Rationale:**

The lemma carries **no new mathematical content for mathlib**. Its statement is the
classical congruence `ψ₂² ≡ Ψ₂Sq (mod the Weierstrass relation)` — equivalently, the
two-torsion-polynomial identity `ψ₂ = 2y+a₁x+a₃ ⇒ ψ₂² = 4x³+b₂x²+2b₄x+b₆` on the
curve — which mathlib *already* states in full ring-generality as
`WeierstrassCurve.ψ₂_sq` (the polynomial-ring identity) and pushes into the
coordinate ring as `WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq`. The project's
`polyToField_ψ₂Sq` is precisely `mk_ψ₂_sq` transported one further step, along the
localisation `R[W] → Frac(R[W])`, and re-expressed through the project-private map
`polyToField` and abbreviation `ψᵤ`. Its proof is a three-rewrite composition
(`ψ_two`, mathlib's `ψ₂_sq`, then the project's own defining `polyToField_polynomial`)
with routine `map_*` homomorphism bookkeeping.

Crucially, the entire `Universal` scaffold the lemma is phrased in — `polyToField :
Poly →+* Universal.Field`, `Universal.Field := Frac(curve.CoordinateRing)`, `ψᵤ`,
`curve` — **does not exist in mathlib** (0 hits across all five search methods); it is
a bespoke per-project construction (and is itself *independently duplicated* between
NagellLutz and HasseWeil). A lemma stated entirely in project-private vocabulary
cannot be lifted to mathlib as-is, and there is nothing to lift: the general,
mathlib-idiomatic form is already upstream. So this is not a mathlib addition; it is a
local glue step that should be obtained inline from mathlib's `ψ₂_sq` whenever the
universal-field image is needed.

**WHY not (refactor-actionable detail):**
Mathlib has the building blocks; `polyToField_ψ₂Sq` is a ≤3-mathlib-call composition
through the project's own `polyToField` map. The blocks are
`WeierstrassCurve.ψ₂_sq` and the supporting `ψ_two`, `C_Ψ₂Sq`, `mk_ψ₂_sq`.

Mathlib building blocks:
- `WeierstrassCurve.ψ₂_sq` — `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:125`
- `WeierstrassCurve.ψ_two` — `…/DivisionPolynomial/Basic.lean:415`
- `WeierstrassCurve.C_Ψ₂Sq` — `…/DivisionPolynomial/Basic.lean:120`
- `WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq` — `…/DivisionPolynomial/Basic.lean:128`
- (project-local, the only non-mathlib ingredient) `Universal.polyToField_polynomial`
  — `projects/NagellLutz/LutzNagell/Universal.lean` (`polyToField curve.polynomial = 0`)

Composition sketch (≤3 substantive rewrites — this *is* the existing proof body):
```lean
example : polyToField (C curve.Ψ₂Sq) = ψᵤ 2 ^ 2 := by
  rw [← map_pow, ψ_two, ψ₂_sq, map_add, map_mul, polyToField_polynomial, mul_zero, add_zero]
```

Call sites in our project (from Phase 6.0): **K = 1** (NagellLutz `ZSMul.lean:267`;
the HasseWeil duplicate has its own single site `DivisionPolynomial.lean:338`).

Refactor plan:
- This is a **project-internal helper**, not a mathlib candidate. It is correctly a
  small private lemma; do **not** propose it for upstream.
- Its single NagellLutz call site (`ZSMul.lean:267`, inside the `Universal.Affine`
  `addX`/`slopeOne` `simp only`) can either keep using the named helper (fine — it
  is one cheap rewrite feeding one consumer) or inline the composition above. Either
  way no mathlib PR results.
- The *real* dedup opportunity (orthogonal to mathlibability, and a cleanup-ticket
  matter, not a mathlib one): NagellLutz and HasseWeil carry **independent identical
  copies** of this lemma *and* of the whole `Universal` scaffold. Per AINTLIB's
  "reuse, don't duplicate" rule, the shared `Universal` construction (and this lemma
  with it) belongs in a `Common/` module imported by both projects. That is a
  cross-project consolidation/cleanup task — file it as a cleanup issue, not a mathlib
  contribution.

Next action: keep `polyToField_ψ₂Sq` as a project-local helper (obtained inline from
mathlib's `ψ₂_sq` + the project's `polyToField_polynomial`); do **not** open a mathlib
PR. Separately, consider a cleanup ticket to de-duplicate the `Universal` scaffold
(this lemma included) between NagellLutz and HasseWeil into `Common/`.

---

## Next step

Keep `polyToField_ψ₂Sq` as a project-local glue lemma — it is mathlib's `ψ₂_sq`
transported through the project-private `polyToField` map (a ≤3-call composition), and
the ring-general identity is already upstream (`ψ₂_sq`, `mk_ψ₂_sq`). No mathlib PR.
Optionally file a cross-project cleanup ticket to share the duplicated `Universal`
scaffold (and this lemma) via `Common/`.
