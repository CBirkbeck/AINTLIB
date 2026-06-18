# Plan for Remaining Sorries (2026-04-18)

The codebase currently has **20 sorries** across 9 files. This document maps
each to its Silverman reference and proof strategy.

## Summary by topic

| Topic | Sorries | Key files | Primary ref |
|---|---|---|---|
| Dual isogeny | 9 | DualIsogeny.lean | Silverman III.6.1-2 |
| Pullback coefficient additivity | 2 | PullbackCoeff.lean | III.5.6 + IV |
| Endomorphism pullbacks (1-α, r·α-s) | 2 | Endomorphism.lean | III.4 |
| Addition pullback (transcendence) | 3 | AdditionPullback.lean | III.3 |
| Ramification (DVR at point) | 1 | Ramification.lean | II.1 |
| Degree quadratic form | 1 | DegreeQuadraticForm.lean | III.6.3 / V.1.2 |
| Frobenius trace | 1 | Frobenius.lean | V.1 |
| LocalExpansion coordHom | 1 | LocalExpansion.lean | IV.1 |
| DivisionPolynomial [n]*(x) | 1 | OmegaPullbackCoeff.lean | III.3 Ex |

## Detailed plan per sorry

### 1. DualIsogeny.lean (9 sorries) — Silverman III.6

These depend on the following chain (Silverman III.6.1):
- **(a)** For any nonzero α of degree n, there is a unique isogeny α̂ such that α̂ ∘ α = [n].
- **(b)** (α+β)̂ = α̂ + β̂ (III.6.2c), equivalent to `deg` being quadratic form (III.6.3).

Concretely needed machinery:
- Silverman proves III.6.1 by assembling: II.2.6 (deg-1 iso), III.4.10 (every isogeny is hom), III.4.15 (sep ⇒ #ker = deg), III.4.16 (factorization), III.4.17 (quotient curve). **None of these are done in our project.**
- Alternative: Silverman III.6.1 also follows from the correspondence Pic⁰(E) ≅ E (III.3.4) + the fact that an isogeny φ : E → E' induces a pullback on Pic⁰ which gives the dual. **T-III-3-004 is also blocked.**

**Status: genuinely BLOCKED** on either III.4.15/16/17 or Pic⁰ correspondence, both of which require substantial curve-level infrastructure (~600+ lines each).

Per-sorry breakdown:
- `L33 isogDual`: requires III.6.1(a) or III.3.4 + III.6.2
- `L37 isogDual_comp_self`: III.6.1(a) by construction
- `L41 self_comp_isogDual`: III.6.1(a) + composition associativity
- `L45 degree_isogDual`: III.6.2a — follows from III.6.1 since deg α · deg α̂ = deg(α ∘ α̂) = deg([deg α]) = (deg α)². When deg α ≠ 0, divides.
- `L49 isogDual_isogDual`: III.6.2b — ̂̂α is the dual of the dual; uses uniqueness in III.6.1(a).
- `L63-64 isogDual_add`: III.6.2c — requires formal group / pullback coefficient additivity (our IV-BRIDGE chain).
- `L68 isogDual_mulByInt`: [n]̂ = [n] — follows from [n]̂ ∘ [n] = [n²] ([n] has deg n²), combined with uniqueness.
- `L87 isogTrace_eq_dual`: III.8 — defines the trace as α + α̂.

**Strategy**: Mark tickets T-III-6-001..009 as BLOCKED with detailed dependency on either III.4.15/16/17 OR III.3.4 route. Recommend Pic⁰ route (shorter).

### 2. PullbackCoeff.lean (2 sorries)

**L138 `isogPullbackCoeff_add`** — Silverman III.5.6:
  `a_{α+β} = a_α + a_β` where `a_α = isogPullbackCoeff α`.
  Proof: via formal group bridge (T-IV-BRIDGE-003). Our `FormalGroupBridge.lean`
  already provides `isogPullbackCoeff_add_of_formal` — we just need to
  discharge its hypotheses (the `FormallyCompatible` bridge is not yet 
  established for the general case).
  **Status**: BLOCKED on T-IV-BRIDGE-001 (formalIsogenySeries).

**L171 `isogPullbackCoeff_dual_mul`** — `a_{α̂·α} = deg α`:
  Follows from Silverman III.6.1(a): `α̂ ∘ α = [deg α]`, then applying 
  `isogPullbackCoeff` (a ring hom): `a_{α̂} · a_α = a_{[deg α]} = deg α`.
  **Status**: BLOCKED on L33 (isogDual definition).

### 3. Endomorphism.lean (2 sorries)

**L59 `isogOneSub` — pullback of `1 - α`**:
  Needs Weierstrass addition formula on K(E) applied to the pullback. Silverman 
  III.2.3 gives explicit formulas; Sutherland Ch 6 packages this as a ring
  operation on the function field.
  **Status**: OPEN. Proof approach: use Affine.Formula to construct the pullback
  power-series style (but not strictly formal since we're over K(E), not a local
  parameter). Delegated to T-III-4-009.

**L85 `isogSmulSub` — pullback of `r·α - s·id`**:
  Same framework as L59. OPEN, same ticket T-III-4-009.

### 4. AdditionPullback.lean (3 sorries)

**L174 `addPullback_x_ne_const`**: The x-coordinate of P+Q (as an element of
K(E)) is NOT a constant in F (when P+Q ≠ O). Proof: ε-argument — the 
rational function addition formula has `x_gen` as a nontrivial term, preventing
constant-valuedness.
Strategy: expand via Affine.Formula x_add, show the denominator has a factor
depending on x_gen.

**L191 `x_gen_transcendental`**: follows from algebraic-in-F(x) impossibility
(mixing of algebraic closure argument). Technical.

**L220 transcendental sub-sorry**: part of same chain.

**Status**: OPEN. These are auxiliary to Silverman III.2 / III.3. Blocks T-III-4-004/005 (Hom torsion-free, End integral domain).

### 5. Ramification.lean:534

**`nonsingular_at_maximal_principal_via_jacobian`**: Jacobian criterion
application for T-II-1-001. When mk(polynomialY) in P and mk(polynomialX)
= (a1/2)·mk(polynomialY) - g(d'/4), show `(d'/4) not in p` gives principality.
Technical DVR argument.

**Status**: OPEN. Ticket T-II-1-001 (worker-A has other parts DONE).

### 6. DegreeQuadraticForm.lean:88

**`degree_quadratic_form_identity`**: `deg β = deg α · r² - tr(α) · r · s + s²`
where β = r·α - s·id. This is Silverman V.1.2 (proof of Hasse bound).
Proof: combine `degree_deg_pos_quadratic_form` (III.6.3) with the explicit
formula from `isogPullbackCoeff` bilinear form.

**Status**: BLOCKED on III.6.3 (positive-definite QF). Ticket T-III-6-009.

### 7. Frobenius.lean:100

**`frobeniusIsog_trace_eq`**: identifies the Frobenius trace with the scalar
appearing in the Hasse bound (Silverman V.1.1).

**Status**: OPEN. Needs V-1-003, V-1-004. Ticket T-V-1-003/004.

### 8. LocalExpansion.lean:501

**`localExpand_coordHom_injective`**: The local expansion homomorphism
K(E) → LaurentSeries F is injective. Silverman IV.1 (implicit via the
uniformizer at O being a ring hom isomorphism).

Proof strategy (from existing notes): order-parity argument. `formalX` has
order -2 (even), `formalY` has order -3 (odd). Polynomial evaluation at 
formalX is injective (transcendence of formalX). Decompose R elements via power
basis {1, root}, image is p(formalX) + q(formalX)·formalY. Even + odd orders
can't cancel unless both p and q are zero.

**Status**: OPEN. T-IV-BRIDGE-001. We have ALL the orderparitiy lemmas now 
(via my `PowerSeries.order_subst` work). This is genuinely closable.

### 9. OmegaPullbackCoeff.lean:477

**`mulByInt_pullback_x_eq`**: `[n]*(x) = Φ_n / Ψ²_n` as division polynomials.
Silverman Exercise III.3.7 / III.4 (the classical identity).
Proof: strong induction on m using the Wronskian recurrence. ~500 lines if 
fully formalized from scratch.

**Status**: OPEN. Ticket T-024 (existing). Blocks the division polynomial
identity which is needed for T-V-1-003/004.

## Prioritized plan

### Priority A — Immediately tractable (this session)

**A-1. LocalExpansion.lean:501 `localExpand_coordHom_injective`** 
  - Has clear order-parity proof strategy
  - Uses infrastructure I built this session
  - Single sorry, clean closure possible
  - Blocks T-IV-BRIDGE-001

  **Attempt 2026-04-18**: Subagent attempted (243 lines added); produced
  `rewrite pattern not found` errors in the Polynomial decomposition step.
  Reverted. The order-parity chain (`p(formalX)` has even order, 
  `q(formalX)·formalY` has odd order) is correct mathematically; the 
  difficulty is in the `Polynomial.eraseLead` / `natDegree`-based induction
  within the current mathlib API surface. Needs a cleaner polynomial-basis
  decomposition lemma or a different approach (e.g., direct via minpoly
  quadratic structure and explicit coefficient matching).

### Priority B — Bounded effort (days)

**B-1. Ramification.lean:534** — 
  - Single Jacobian criterion computation
  - Ticket T-II-1-001 (partial)
  - ~100-200 lines

**B-2. Endomorphism.lean 59, 85 (isogOneSub, isogSmulSub pullbacks)**
  - Needs Weierstrass addition formula on K(E)
  - Well-defined problem, ~300-500 lines

**B-3. Frobenius.lean:100 `frobeniusIsog_trace_eq`**
  - Direct computation once tr(π) machinery is set up

### Priority C — Substantial infrastructure (weeks)

**C-1. DualIsogeny.lean (9 sorries)** — need III.4.15/16/17 OR III.3.4 route
**C-2. AdditionPullback.lean (3 sorries)** — transcendence arguments for curves
**C-3. OmegaPullbackCoeff.lean:477** — division polynomial Wronskian (~500 lines)
**C-4. PullbackCoeff.lean (2 sorries)** — BLOCKED on IV-BRIDGE
**C-5. DegreeQuadraticForm.lean:88** — BLOCKED on III.6.3

## Action plan for this session

1. **Update tickets** with detailed Silverman references and proof strategies.
2. **Close Priority A-1** (LocalExpansion order-parity) using infrastructure
   now available from my `OrderSubst.lean` + `Logarithm.lean` work.
3. **Dispatch subagents** for Priority B tickets in parallel.
