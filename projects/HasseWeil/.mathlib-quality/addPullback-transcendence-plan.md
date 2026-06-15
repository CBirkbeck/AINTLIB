# Multi-session plan: closing AdditionPullback transcendence sorries

**Goal:** Close the three sorries in `HasseWeil/AdditionPullback.lean`
(`addPullback_x_ne_const`, `addPullback_x_quadratic_over_F`,
`minpoly_not_const_degree_two`) via the `ordAtInfty` bridge (Path B).

These sorries block the real pullback of `1 − π`, which in turn blocks
closing the `Frobenius.lean:128` sorry in the unconditional Hasse bound.

**Status:** Plan draft; no sorries closed yet. Updated 2026-04-21.

---

## Why Path B (ordAtInfty) over Path A (polynomial manipulation)

Path A (derive a polynomial identity in `F[x_gen, y_gen, α*x, α*y]` modulo
Weierstrass and force a basis-level contradiction) is the textbook
approach but requires ~200–300 lines of `linear_combination` + case
analysis (char = 2 vs char ≠ 2).

Path B leverages worker-I's `ordAtInfty : C.FunctionField → WithTop ℤ`
in `HasseWeil/Curves/Infinity.lean`. Key identities:
- `ord_∞(c : F) = 0` for `c ≠ 0`
- `ord_∞(x_gen) = -2` (worker-I's `ordAtInfty_coordX`)
- `ord_∞(y_gen) = -3` (worker-I's `ordAtInfty_coordY`)
- `ord_∞(f · g) = ord_∞(f) + ord_∞(g)` (worker-I's `ordAtInfty_mul`)

Proof sketch (secant case, generic): `addX = ℓ² + a₁ℓ − a₂ − x_gen − α*x`
where `ℓ = (y_gen − α*y) / (x_gen − α*x)`.
- `ord_∞(α*x) = α.degree · (−2)` (**degree scaling** — lemma to prove)
- `ord_∞(α*y) = α.degree · (−3)` (ditto)
- `ord_∞(x_gen − α*x) = min(−2, −2·α.degree) = −2·α.degree` (for `α.degree ≥ 1`)
- `ord_∞(y_gen − α*y) = −3·α.degree`
- `ord_∞(ℓ) = −3·α.degree − (−2·α.degree) = −α.degree`
- `ord_∞(ℓ²) = −2·α.degree`
- `ord_∞(addX)` is dominated by `ord_∞(ℓ²) = −2·α.degree` for `α.degree ≥ 2`,
  hence `addX` has a pole, hence `addX ∉ F`.
- For `α.degree = 1`: potential cancellation between `ℓ²`, `x_gen`, `α*x`;
  separate analysis (likely forces `α = ±id`, ruled out by AddNonInverse).
- For `α.degree = 0`: `α` is the zero isogeny; handled separately.

---

## Session-level milestones

### Session 1 — Foundational bridge + basic orders (THIS SESSION)

**Deliverable:**
- `HasseWeil/Curves/OrdAtInfty_WToAffine.lean` (new) bridging `W.toAffine`
  (our `Affine F` type from mathlib) to `SmoothPlaneCurve F`.
- Basic order lemmas for our setup:
  - `W_smooth W : SmoothPlaneCurve F` wrapping `W.toAffine`.
  - `ordAtInfty_x_gen W : (W_smooth W).ordAtInfty (x_gen W) = -2`
  - `ordAtInfty_y_gen W : (W_smooth W).ordAtInfty (y_gen W) = -3`
  - `ordAtInfty_algebraMap_F_const (c : F) (hc : c ≠ 0) :
      (W_smooth W).ordAtInfty (algebraMap F KE c) = 0`

**Target:** ~100 lines, axiom-clean, sorry-free.

**Hard parts:** identifying `coordX` of the SmoothPlaneCurve with `x_gen` of our
`MulByIntPullback`-flavour setup (both are `algebraMap (Polynomial F) KE X` by
definition but through different paths). Use `rfl`/`simp` or elementary rewriting.

---

### Session 2 — Degree scaling lemma — REVISED SCOPE

**Original deliverable:**
- `ordAtInfty_pullback_of_isogeny` — general degree scaling.

**Revised (after session 2 audit):** The general scaling
`ord_∞(α.pullback f) = deg_i(α) · ord_∞(f)` — **note**: it's inseparable
degree not total degree — requires ramification theory (separable/
inseparable decomposition, behaviour at the point at infinity) that is
not yet in this project. Formalizing it is itself a multi-session task.

**Revised session-2 deliverables (partial):**
- `ordAtInfty_y_gen` ✅ (session 2a, landed in commit `50dc487`)
- `ordAtInfty_algebraMap_F_nonzero` — deferred (heartbeat timeout during
  `Algebra (FractionRing F[X]) KE` resolution — tractable but fiddly)
- `ordAtInfty_pullback_of_mulByInt` — direct computation for `α = [n]`
  using division-polynomial formulas. ~150 lines, achievable.
- General case deferred.

**Reframing for session 3:** rather than general α, the closure of
`addPullback_x_ne_const` may require EITHER:
* `ord_∞(α.pullback)` only for `α = id` and `α = -id` (the edge cases),
  OR
* a direct polynomial-identity argument (Path A) that doesn't need the
  degree scaling.

**Hard assessment:** The Path B approach is more delicate than originally
envisaged because isogenies between elliptic curves are NOT automatically
unramified at infinity — the Frobenius isogeny has ramification e = p at
infinity. So the formula is actually `ord_∞(α.pullback f) = e_∞(α) ·
ord_∞(f)` where `e_∞(α)` is the ramification index at infinity, which
for an elliptic curve equals the inseparable degree of α.

---

### Session 3 — Close `addPullback_x_ne_const`

**Deliverable:**
- Close `addPullback_x_ne_const` via the order computation:
  - Case `α.degree ≥ 2`: `ord_∞(addX) = -2·α.degree < 0`, contradicting
    `ord_∞(c : F) = 0`.
  - Case `α.degree = 1`: structural case analysis.
  - Case `α.degree = 0`: α = 0, then `id + α = id`, `addX = 2·x_gen + ...`,
    still nonconstant; direct argument.
  - Case `α = ±id`: excluded by AddNonInverse or direct argument.
  - Case `α = -id`: AddNonInverse rules out secant case; doubling case:
    `addX = tangent-expr` that simplifies (e.g., via `2y + ax + a' = 0`) —
    requires separate treatment.

**Target:** ~100 lines, axiom-clean.

---

### Session 4 — Close `addPullback_x_quadratic_over_F` + `minpoly_not_const_degree_two`

**Deliverable:** Close the remaining two sorries using the transcendence
established in session 3 + minpoly theory (mathlib).

**Target:** ~150 lines combined.

---

## Risk assessment

| Risk | Severity | Mitigation |
|------|----------|------------|
| Type mismatch between `W.toAffine` and `SmoothPlaneCurve` forms | Low | Direct `rfl`/`simp`; both use `abbrev` |
| Degree-scaling lemma requires deep ramification theory | **High** | Fallback: prove only for `mulByInt W n`, then work case-by-case per α structure |
| Base-field constant lemma needs new infra | Medium | Worker-I's algebraMap handling should suffice; may need a small lemma |
| Combined char 2 + `α = ±id` edge cases | Medium | Document but defer if scope blows up |

---

## Interim output (if effort stalls)

Even without closing the sorries, delivering sessions 1 + 2 is valuable:
the `ordAtInfty` bridge gives Stream A a clean infrastructure layer for
reasoning about orders of function-field elements in our setup, which
unblocks other tickets downstream (T-II-3-009, T-II-4-007/008, several
others).

---

## References

- `HasseWeil/Curves/Infinity.lean` (worker-I): `ordAtInfty`,
  `ordAtInfty_coordX`, `ordAtInfty_coordY`, `ordAtInfty_mul`.
- `HasseWeil/MulByIntPullback.lean` (our setup): `x_gen`, `y_gen`,
  `W_KE`, generic_equation, `mulByInt_x_transcendental`.
- `HasseWeil/AdditionPullback.lean`: the three sorries to close.
- Silverman, *The Arithmetic of Elliptic Curves*, II.1 / IV.1 for ord at
  infinity discussion.
