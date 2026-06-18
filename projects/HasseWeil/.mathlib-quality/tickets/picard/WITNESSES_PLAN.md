# Witnesses Plan: Closing the 3 Hard Pieces for Unconditional B-4-003

**Created**: 2026-04-29
**Goal**: Discharge the 3 remaining open prerequisites of
`AddHomProperty_of_picZero_witnesses`, making the universal Silverman III.4.8
(B-4-003) **unconditional** — no parametrization, no axiomatic shortcuts,
zero new sorries.

## Context

The witness-parametric universal theorem
`AddHomProperty_of_picZero_witnesses` (T-PIC-E-001, DONE) takes 4 hypotheses:

```lean
(h_van_W₁  : ∀ D ∈ projPrincipalSubgroup ⟨W₁⟩, projectiveDivisorSum W₁ D = 0)
(h_van_W₂  : ∀ D ∈ projPrincipalSubgroup ⟨W₂⟩, projectiveDivisorSum W₂ D = 0)
(h_pres    : ∀ D ∈ projPrincipalSubgroup ⟨W₁⟩,
               pushforwardProjectiveDivisor φ cd D ∈ projPrincipalSubgroup ⟨W₂⟩)
(h_inj_W₁  : ∀ D, picZeroOfPoint W₁ (picZeroSumOfWitness W₁ h_van_W₁ D) = D)
```

These correspond exactly to:

| Witness     | Ticket     | Mathematical content                                |
|-------------|------------|-----------------------------------------------------|
| `h_van_W*`  | T-PIC-A-002 | Σ-vanishes on principal divisors (Silverman III.3.5) |
| `h_pres`    | T-PIC-C-003 | Pushforward of `div(g)` is `div(N(g))` (Silverman II.3.7) |
| `h_inj_W₁`  | T-PIC-F-001 | `κ ∘ σ̄ = id` (existence in Silverman III.3.4(a))    |

All three need to be discharged for unconditional B-4-003.

## Strategic decisions

### (D1) **Avoid Riemann–Roch and Cayley–Bacharach.**

Both are research-level theorems missing from mathlib and the project has
explicitly opted out. Our routes use:

- **Group-law-based** decomposition for A-002 (line + vertical + factorization).
- **Norm-divisor correspondence** for C-003 (worker-I's `NormValuation` is ~80% of the bridge).
- **Inductive existence** for F-001a (independent of worker-K).
- **Worker-K dependency only for F-001b** (uniqueness — there is no R-R-free workaround that avoids T-III-3-003 itself).

### (D2) **Don't disturb other workers.**

- Worker-K owns `Curves/IntegralClosure.lean`, `EC/PicE.lean`,
  `Curves/ProjectiveDivisor.lean` (`degZero` work for T-II-3-009),
  and the T-III-3-003 file (when created).
- Worker-I owns `Curves/NormValuation.lean` (read-only for us; we
  consume its API).
- We add new code to: `Curves/PicZero.lean`,
  `Curves/PicZeroPushforward.lean`, `EC/IsogenyAG/HomProperty.lean`, and
  one **new** file `Curves/PicZeroLineCase.lean` (for the geometric line
  intersection infrastructure of A-002a).

### (D3) **B-4-003 unconditional does NOT depend on worker-K.**

**Critical insight (2026-04-29 during planning)**: re-reading
`AddHomProperty_of_picZero_witnesses`, the only F-direction witness
required is `h_inj_W₁ : κ ∘ σ̄ = id` (one direction of the bijection).
This uses:
- F-001a (existence): for any D ∈ Div⁰, ∃ P with D ~ (P) − (O)
- B-003 (DONE): σ̄ ∘ κ at divisor level
- A-002 (h_van): σ respects ~

**Worker-K's T-III-3-003** provides the *converse* uniqueness `(P) ~ (Q)
⟹ P = Q`, which is the OTHER direction of the bijection (T-PIC-F-002,
"σ̄ is a bijection"). For B-4-003 we don't need σ̄ to be a bijection — we
only need `κ ∘ σ̄ = id` — and that follows from existence + the
already-shipped divisor-level identity.

So **all 3 hard pieces (A-002, C-003, F-001a) are independent of
worker-K**. T-PIC-F-001b is now reclassified as "needed only for the
σ̄-iso-package T-PIC-F-002, not for B-4-003."

### (D4) **`[IsAlgClosed F]` regression avoided via Galois descent (Phase G).**

The 3 hard pieces (A-002, C-003, F-001) inherit `[IsAlgClosed F]` from
the F-rational `SmoothPoint` framework — over non-alg-closed F,
`projectiveDivisorOf` doesn't even land in `Div⁰` (worker-K's T-II-3-009
makes this explicit). Avoiding the regression at the witness level would
require rewriting `Divisor` to use scheme-theoretic closed points
(massive refactor, ~1000+ LOC).

**Solution: Galois descent.** Prove the witnesses + B-4-003 over
F̄ = `AlgebraicClosure F`, then **descend** to arbitrary F via the
inclusion `E(F) ↪ E(F̄)` and the naturality of the point map under
base-change. This adds ~210 LOC of descent infrastructure (Phase G,
G-001..G-006) and gives B-4-003 unconditionally over arbitrary F.

**Why this matters**: the project's actual target is Hasse over F_q. The
Frobenius isogeny is defined over F_q, and Hasse uses its hom property
on E(F_q), not E(F̄_q). So descent is **on the critical path** for the
project's eventual application — not just a nice-to-have.

---

## Recent shipped (2026-04-29)

`HasseWeil/Curves/PoleOrderParity.lean` (~80 LOC, axiom-clean):
- `coordRingImage_ordAtInfty_ne_neg_one`: parity obstruction. For
  nonzero `u : C.CoordinateRing`, `ord_∞(algMap u) ≠ -1`. Proved via
  basis decomposition + parity (even from p, odd ≥ 3 from q).
- `funcField_image_ordAtInfty_ne_neg_one`: function-field version.
- `point_minus_O_principal_eq_zero_of_coord` (intermediate): if
  `(P) - (O) = projectiveDivisorOf f` AND `f ∈ image of CR`, then
  `P = 0`. The CR-image hypothesis is the only non-mechanical step left.

See `T-PIC-AF-UNIFIED.md` for the full unified A-002/F-001 plan with
the shipped parity infrastructure plus 4 outstanding pieces totaling
~470 LOC.

## REVIEWER CORRECTIONS (2026-04-29)

External reviewer flagged two major issues with the original plan:

### (R1) T-PIC-A-002's "factor every f as vertical + line forms" plan is BROKEN.

The claim "`y - g(x)` for `g ∈ F(x)` is a line form whose divisor is `(P) + (Q) + (R) - 3·(O)`" is **only true for `g(x) = mx + b` (affine linear)**. For arbitrary rational `g ∈ F(x)`, the curve `y = g(x)` is not a line: after clearing denominators it's a higher-degree plane curve, and proving the sum of intersection points with E vanishes is essentially Cayley–Bacharach again.

**Replacement strategy**: skip the function-field factorization entirely. Use only TRUE line and vertical-line principal divisors:

1. `line_principal`: `div(L_{P,Q}) = (P) + (Q) + (-(P+Q)) - 3·(O)` for the chord/tangent line through P, Q.
2. `vertical_principal`: `div(V_P) = (P) + (-P) - 2·(O)`.
3. `chord_principal` (Miller relation, derived from 1+2): `(P) + (Q) - (P+Q) - (O) ~ 0`.
4. `degree_zero_divisor_reduce` (combinatorial induction using Miller): for any `D ∈ Div⁰`,
   `D ~ (σ(D)) - (O)`.
5. `point_minus_O_principal_eq_zero` (special weak uniqueness): if `(P) - (O)` is principal then `P = 0`. Provable via pole-order argument with existing `ordAtInfty` API. **Much weaker than full Silverman III.3.3.**

From these, derive both:
- `h_van` (T-PIC-A-002): if `D` principal, then `D ~ 0`, but reduction gives `D ~ (σ(D)) - (O)`, so `(σ(D)) - (O)` is principal, so by (5) `σ(D) = O`. Hence `σ(D) = 0` (additive identity).
- `h_inj` (T-PIC-F-001c): the Picard class of `D` equals that of `(σ(D)) - (O)` directly from (4), giving `picZeroOfPoint W (σbar D) = D`.

**This MERGES T-PIC-A-002 and T-PIC-F-001 into a single unified package.** No separate "line case" + "factorization" split; no separate "F-001a existence" + "F-001b uniqueness" split. The package is approximately:

| Sub-ticket | LOC est. |
|---|---|
| `line_principal` (chord/tangent divisor) | ~200 |
| `vertical_principal` (DONE as `projectiveDivisorSum_vertical_line`) | shipped |
| `chord_principal` (Miller relation) | ~30 (derived) |
| `degree_zero_divisor_reduce` (combinatorial induction) | ~120 |
| `point_minus_O_principal_eq_zero` (pole-order) | ~80 |
| `principal_sum_zero` (h_van assembly) | ~30 |
| `picZeroOfPoint_sigma_eq` (h_inj assembly) | ~30 |
| **Total** | **~490 LOC** |

(Down from ~620 LOC for the broken plan.)

### (R2) Phase G injectivity should be by flatness + scalar-extension equivalence, NOT by AdjoinRoot kernel analysis.

Construction:
1. Build `coordRingScalarExtEquiv : L ⊗_F C.CR ≃ₐ[L] (C.baseChange L).CR` — the natural iso identifying base-change with scalar extension (~150-200 LOC).
2. Conjugation lemma: under this iso, `cd.baseChangeAlgHom = (equiv).comp (1_L ⊗ cd.toAlgHom).comp (equiv⁻¹)`.
3. Injectivity: `Module.Flat.lTensor_preserves_injective_linearMap` (mathlib) — flatness preserves injectivity. L is F-flat (free F-module via basis). cd.toAlgHom injective. So `1_L ⊗ cd.toAlgHom` injective, hence `cd.baseChangeAlgHom` injective.

This is much cleaner and uses real mathlib infrastructure rather than reinventing minpoly arguments.

### (R3) Audit items from reviewer

- **Finiteness**: `Isogeny.AG` doesn't currently store/derive finiteness of the function-field extension. The Pic⁰ pushforward and norm witnesses (T-PIC-C-003) need this. Audit before pushing more LOC into C-003 — may need an auxiliary structure field or a separate "finite pullback extension" theorem.
- **`pullback_ordAtInfty_nonneg` for base-changed isogeny** (Phase G missing subtask): needs ord-at-infinity compatibility under scalar extension. Not automatic from coordinate-ring base-change.
- **Norm-divisor proof must cover the point at infinity**, not only affine maximal ideals. Isogenies preserve `O`, so the valuation above `O` is especially important.
- **Don't block Hasse on universal B-4-003**: the existing `WithHom` bundle covers all isogenies actually used in Hasse (id, compose, frobenius, mulByInt). Universal B-4-003 is the right long-term theorem but should not gate the Hasse endgame.

---

## Piece 1: T-PIC-A-002 — σ vanishes on principal divisors

**Status**: PARTIAL — multiplicativity + vertical-line case shipped.
**Total estimate**: ~500 LOC across 4 sub-tickets.

### Strategy

Avoid Cayley-Bacharach by using the K(E)*-multiplicative structure plus a
finite generating set:

> Every nonzero `f ∈ K(E)*` factors (modulo units of `K̄`) as a product of
> "line forms" (`y - g(x)`-type) and "vertical forms" (`x - a`-type),
> intersected with E.

The factorization comes from the fact that `K(E) = F(x)[y]/(W(x,y))` with
`[K(E):F(x)] = 2`. Every `f ∈ K(E)*` can be written as
`f = (a(x) + b(x)·y) / (c(x) + d(x)·y)` for `a,b,c,d ∈ F(x)`. Then:

- **Numerator/denominator are linear-in-y line forms** (or constants in y).
- For `b ≠ 0`: `(a + b·y)/b = (y + a/b) = (y - g(x))` where `g = -a/b ∈ F(x)`.
- After clearing denominators in `g`, this becomes a polynomial line form
  times a vertical-line factor.

So the multiplicative generators are:
- (i) `x - α` for `α ∈ F` (vertical lines) — **DONE**.
- (ii) `y - g(x)` for `g ∈ F(x)` (line forms) — needs sub-ticket A-002a.

And the **factorization argument** that every `f` reduces to (i)+(ii) — needs
sub-ticket A-002c.

### Sub-tickets

| ID | Title | Lines | File | Depends on |
|---|---|---|---|---|
| **T-PIC-A-002a** | General line case: σ(div(y - g(x))·E) = 0 | ~200 | PicZeroLineCase.lean (NEW) | A-001, A-002b |
| **T-PIC-A-002b** | Vertical-line case: σ(div(x - α)·E) = 0 | (DONE) | PicZero.lean | A-001 |
| **T-PIC-A-002c** | Factorization: every f ∈ K(E)* is a product of (i)+(ii)+units | ~200 | PicZero.lean | T-III-3-002 (DONE) |
| **T-PIC-A-002d** | Final assembly via multiplicativity | ~50 | PicZero.lean | A-002a, A-002c |

### Risks

- **A-002a** (line case) requires the **chord/tangent group law identity**
  `P + Q + R = O ⇔ P, Q, R collinear` at the divisor level. The mathlib
  `WeierstrassCurve.Affine.Point` add definition encodes this. We need to
  bridge it to a divisor identity:
  `div(line through P, Q, R)·E = (P) + (Q) + (R) - 3·(O)` plus
  `P + Q + R = O ⟹ Σ in E group = O`.
  — Estimated 200 LOC; the chord/tangent unfolding is fiddly but standard.

- **A-002c** (factorization) is the **algebraic structure** part. K(E) =
  F(x)[y]/W where W is monic of degree 2 in y (Silverman III.1.3). Every
  `f ∈ K(E)*` is `a(x) + b(x)y` for `a, b ∈ F(x)` (with `(a, b) ≠ (0,0)`).
  Then either `b = 0` (case i) or factor out `b` to get `b · (y + a/b)` =
  unit · (y - g(x)) form. — 200 LOC, mostly polynomial bookkeeping.

---

## Piece 2: T-PIC-C-003 — pushforward preserves principal

**Status**: OPEN. Worker-I's `NormValuation.lean` (721 LOC) provides the
core ring-theoretic bridge.
**Total estimate**: ~330 LOC across 4 sub-tickets.

### Strategy

Use the **norm-divisor correspondence** for finite separable extensions of
function fields:

> For `g ∈ K(E₁)*` and a closed point `q ∈ E₂` with `φ(q) = p`:
> `ord_p(N_{K(E₁)/K(E₂)}(g)) = Σ_{q' ∈ φ⁻¹(p)} f(q'/p) · ord_{q'}(g)`
>
> where `f(q'/p)` is the residue degree. Under `[IsAlgClosed F]`,
> `f(q'/p) = 1` (worker-I's `inertiaDeg_maximalIdealAt`).

This identity, restricted to `[IsAlgClosed F]`, is precisely what
`pushforwardProjectiveDivisor (div g) = div (N(g))` says.

Worker-I has shipped:
- `smoothPointEquivMaxIdeal` — bijection at the ring-theoretic level.
- `inertiaDeg_maximalIdealAt = 1` — the "no residue extension" fact.
- `sum_ramificationIdx_eq_finrank` — the sum formula.
- `smoothPoint_fiber_eq_primesOver` — fiber identification.

What's missing is the bridge:
- Connect our `pointValuation`-based `ord_P` to mathlib's
  `Ideal.HeightOneSpectrum.intValuation` (for height-one primes of F[E]).
- Apply `Ideal.relNorm_singleton` + `map_mul Ideal.relNorm` + UFM
  factorization in F[X] to extract per-prime ramification multiplicities.

### Sub-tickets

| ID | Title | Lines | File | Depends on |
|---|---|---|---|---|
| **T-PIC-C-003a** | Bridge: `ord_P f = multiplicity of (maxIdeal_P) in (f)` | ~100 | PicZeroPushforward.lean | NormValuation API |
| **T-PIC-C-003b** | Norm-divisor identity at affine points: `ord_p(Ng) = Σ ramId · ord_q g` | ~150 | PicZeroPushforward.lean | C-003a, NormValuation |
| **T-PIC-C-003c** | Infinity case: `ordAtInfty(Ng) = Σ ordAtInfty over fiber of ∞` | ~50 | PicZeroPushforward.lean | C-003b |
| **T-PIC-C-003d** | Assembly: `pushforwardProjectiveDivisor (div g) = div (N g)` | ~30 | PicZeroPushforward.lean | C-003c |

### Risks

- **C-003a** requires connecting `ord_P f` (defined via
  `pointValuation` from a smooth point) to `multiplicity (maxIdeal P) (f)`
  (mathlib's `UniqueFactorizationMonoid.normalizedFactors.count` or
  `IsDedekindDomain.HeightOneSpectrum.intValuation`). The two are
  mathematically the same but live in different mathlib namespaces. ~100
  LOC to reconcile.

- **C-003c** (infinity case) is the only "non-cookie-cutter" part. The
  `ordAtInfty` is defined via `RatFunc.intDegree`, and the norm of `g`'s
  infinity behavior must equal the sum of infinity ramifications above
  it. Worker-I's `Curves/Infinity.lean` has the relevant infrastructure.

- **`[IsAlgClosed F]`** dependency: required throughout (worker-I's
  surjection of SmoothPoint onto MaxSpec needs it). Documented as
  generality regression.

---

## Piece 3: T-PIC-F-001 — κ ∘ σ̄ = id (existence direction only)

**Status**: OPEN (no worker-K dependency for B-4-003)
**Total estimate**: ~170 LOC across 2 sub-tickets needed for B-4-003,
plus ~30 LOC for the optional uniqueness piece (F-001b).

### Strategy

Two independent pieces:

- **(F-001a, EXISTENCE — REQUIRED for B-4-003)**: For any `D ∈ Div⁰(E)`,
  there is some `P ∈ E` with `D ~ (P) - (O)`. Inductive proof:
  - Base case: `D = 0`, take `P = O`.
  - Single-point: `D = (Q) - (O)`, take `P = Q`.
  - Step: `D = D' + (Q₁) - (Q₂)` reduces via the chord/tangent identity
    `(Q₁) + (-Q₂) - (Q₁ - Q₂) - (O) ~ 0` (line through Q₁, -Q₂, -(Q₁−Q₂)).
  - Eventually D ~ (σ(D)) - (O).
  Uses **only A-002a (line case)**.

- **(F-001c, ASSEMBLY — REQUIRED for B-4-003)**: Combine existence with
  the **already-shipped** B-003 (`σ̄ ∘ κ = id` at divisor level) to get
  `picZeroOfPoint W (picZeroSum W D) = D` at Pic⁰ level.

- **(F-001b, UNIQUENESS — OPTIONAL, only for σ̄-iso package)**: If
  `(P) - (O) ~ (Q) - (O)`, then `P = Q`. This is worker-K's T-III-3-003.
  Needed for T-PIC-F-002 (packaging σ̄ as a `MulEquiv`), but **NOT
  needed** for B-4-003 itself.

### Sub-tickets

| ID | Title | Lines | File | Depends on | Required for B-4-003? |
|---|---|---|---|---|---|
| **T-PIC-F-001a** | Existence: ∀ D ∈ Div⁰, ∃ P, D ~ (P) − (O) | ~120 | PicZero.lean | A-002a | **YES** |
| **T-PIC-F-001c** | Assembly: κ ∘ σ̄ = id at Pic⁰ level | ~50 | PicZero.lean + HomProperty.lean | F-001a, B-003 (DONE), A-002 | **YES** |
| **T-PIC-F-001b** | Uniqueness via worker-K's T-III-3-003 | ~30 | PicZero.lean | T-III-3-003 (worker-K) | NO (only for F-002) |

### Risks

- **F-001a** is the only "real" piece in F. The induction on
  `D.support.card` is standard but the step case uses the divisor
  identity from A-002a (chord-line through three collinear points). So
  F-001a is gated on A-002a, not on worker-K.

- **F-001b is reclassified**: previously thought to be a B-4-003 blocker;
  re-analysis showed it provides the *converse* `σ̄`-injectivity direction,
  which is the σ̄-iso bijection (T-PIC-F-002), not the witness needed by
  `AddHomProperty_of_picZero_witnesses`. **No worker-K blocker remains
  for B-4-003.**

---

## Piece 4: Phase G — Galois Descent

**Status**: NEW (added 2026-04-29 in response to user's "can we avoid
the regression?" question)
**Total estimate**: ~210 LOC across 6 sub-tickets.

### Strategy

Build base-change machinery for `Isogeny.AG` and use it to descend
B-4-003 from F̄ to arbitrary F.

### Sub-tickets

| ID | Title | Lines | File | Depends on |
|---|---|---|---|---|
| **T-PIC-G-001** | `CurveMap.baseChange` along F → L | ~80 | CurveMap.lean (extension) | BaseChange.lean (DONE) |
| **T-PIC-G-002** | `Isogeny.AG.baseChange` | ~30 | EC/IsogenyAG/BaseChange.lean (NEW) | G-001 |
| **T-PIC-G-003** | `CoordHom.baseChange` | ~50 | EC/IsogenyAG/BaseChange.lean | G-001, G-002 |
| **T-PIC-G-004** | `toPointMap_baseChange` compatibility square | ~80 | EC/IsogenyAG/BaseChange.lean | G-002, G-003 |
| **T-PIC-G-005** | `AddHomProperty.of_baseChange` descent lemma | ~40 | EC/IsogenyAG/BaseChange.lean | G-004 |
| **T-PIC-G-006** | **Final unconditional B-4-003** over arbitrary F | ~20 | EC/IsogenyAG/HomProperty.lean | G-005 + A-002d + C-003d + F-001c |

### Risks

- **G-001 (function field base-change)**: mathlib doesn't have a direct
  `Frac(R) ⊗ L = Frac(R ⊗ L)` for the case we need. ~20 LOC of bridge
  via `IsLocalization`.
- **G-004 (compatibility square)**: depends on the exact `CoordHom`
  field structure; could inflate from ~80 to ~120 LOC if proofs of
  `Polynomial.eval ∘ map = map ∘ eval` don't compose cleanly.
- **`includePoint_add` for G-005**: mathlib likely has
  `WeierstrassCurve.Affine.Point.map_add` but exact name needs
  verification. If absent, ~30 LOC of explicit chord/tangent
  base-change compatibility.

---

## Total estimates

| Piece | Sub-tickets | New LOC | Worker-K dep? | Worker-I dep? |
|---|---|---|---|---|
| A-002 (over F̄) | 4 (1 done) | ~450 | No | No |
| C-003 (over F̄) | 4 | ~330 | No | YES (read-only) |
| F-001 (for B-4-003 over F̄) | 2 (+1 optional) | ~170 (+30 opt) | **NO** | No |
| **Phase G — Galois descent** | **6** | **~300** | No | No |
| **Total for unconditional B-4-003 over arbitrary F** | **16 sub-tickets** | **~1250 LOC** | None | API consumer |

**Sessions estimate**: 8-12 focused sessions for the full unconditional close
(allowing 1-2 sessions per phase plus debugging in G-004).

**Worker-K dependency for B-4-003: NONE** (revised). The worker-K
T-III-3-003 ticket remains relevant only for the σ̄-iso bijection package
(T-PIC-F-002), not for the universal AddHomProperty (B-4-003).

## Parallelism

Four workers can execute independently:

- **Worker α** on Piece 1 (A-002) — touches `PicZero.lean`,
  `PicZeroLineCase.lean`.
- **Worker β** on Piece 2 (C-003) — touches `PicZeroPushforward.lean`,
  consumes `NormValuation.lean`.
- **Worker γ** on Piece 3a (F-001a) — touches `PicZero.lean` (after
  worker α's A-002a lands).
- **Worker δ** on Phase G (G-001..G-005) — touches new `BaseChange.lean`
  files; **fully independent** of α, β, γ. Can start immediately.

**Coordination**: Worker α and γ both touch `PicZero.lean`, so γ should
wait for α's A-002a to land (1-2 sessions). β and δ are fully independent.

**G-006 is the final assembly** — needs all of A-002d, C-003d, F-001c,
G-005 done.

## Sequencing for unconditional close

1. **Phase W1** (parallel, 4 fronts):
   - A-002a, A-002c (worker α)
   - C-003a (worker β)
   - G-001, G-002 (worker δ)
2. **Phase W2** (parallel):
   - A-002d (worker α)
   - C-003b (worker β)
   - F-001a (worker γ, after A-002a)
   - G-003, G-004 (worker δ)
3. **Phase W3** (parallel):
   - C-003c, C-003d (worker β)
   - F-001c (worker γ)
   - G-005 (worker δ)
4. **Phase W4 (final assembly)**: G-006 — `AddHomProperty_universal`
   over arbitrary F. ~20 LOC corollary. Mark T-PIC-F-003 as subsumed.
5. **Phase W5 (cleanup)**: drop `_witnesses` suffix from public API,
   update `INDEX.md`, mark all tickets DONE, run `#print axioms` audit
   to verify no regressions.

(F-001b is **deferred** until worker-K's T-III-3-003 lands; it's needed
only for the optional σ̄-iso bijection package T-PIC-F-002, not for
B-4-003 itself.)

## Cleanup checkpoints

| ID | When |
|---|---|
| `CLEANUP-W-1` | After A-002 fully closed |
| `CLEANUP-W-2` | After C-003 fully closed |
| `CLEANUP-W-3` | After F-001a + F-001c closed |
| `CLEANUP-G-1` | After G-001..G-005 closed (descent infrastructure) |
| `CLEANUP-W-4` | Final: after G-006 lands (B-4-003 unconditional over arbitrary F) |

## Open questions for user

1. **`[IsAlgClosed F]` regression — RESOLVED via Phase G (Galois
   descent)**. Final B-4-003 is over arbitrary F. +210 LOC over the
   alg-closed version. On the critical path for Hasse over F_q.

2. **F-001b deferred to optional**: worker-K's T-III-3-003 is no longer
   on the B-4-003 critical path. Defer F-001b to a future session (only
   needed for the σ̄-iso package, not B-4-003).

3. **Order of execution preference**: 4 workers in parallel
   (A-002, C-003, F-001a, Phase G) or serial? Parallel maximizes
   throughput; Phase G is fully independent and can absorb spare cycles.
