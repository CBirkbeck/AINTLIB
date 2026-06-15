# Dependency Graph

This document describes the dependency structure between tickets. A ticket
depends on another if its proof or definition references the other one. Workers
should consult this when picking a ticket to work on.

## Top-level structure

The project is organized into 5 streams that can run concurrently:

- **Stream A** — Algebraic curves (Silverman II)
- **Stream B** — Weierstrass equations + group law (Silverman III.1, III.2, III.3)
- **Stream C** — Isogenies (Silverman III.4)
- **Stream D** — Formal groups (Silverman IV)
- **Stream E** — Invariant differential + dual isogeny + bridge (Silverman III.5,
  III.6, IV.4)

```
                    ┌────────────────────┐
                    │  Stream A (II)     │  Curves, maps, divisors, differentials
                    │                    │
                    │  II.1 → II.2 → II.3│
                    │             ↘ II.4 │
                    └─────────┬──────────┘
                              │
              ┌───────────────┼───────────────┐
              │               │               │
              ▼               ▼               ▼
       ┌──────────┐    ┌──────────┐    ┌──────────┐
       │ Stream B │    │ Stream C │    │ Stream D │
       │ (III.1-3)│    │ (III.4)  │    │ (IV)     │
       │ Weier-   │    │ Isogenies│    │ Formal   │
       │ strass   │    │          │    │ groups   │
       └────┬─────┘    └────┬─────┘    └────┬─────┘
            │               │               │
            └───────┬───────┴───────┬───────┘
                    │               │
                    ▼               ▼
              ┌──────────┐    ┌──────────┐
              │ Stream E │    │  BRIDGE  │
              │ (III.5+6)│◀───│  IV.4 ↔  │
              │ Inv diff │    │  III.5   │
              │ + dual   │    │          │
              └────┬─────┘    └──────────┘
                   │
                   ▼
              ┌──────────┐
              │  V.1     │
              │  Hasse   │
              │  bound   │
              └──────────┘
```

## Critical synchronization points

The following tickets are **synchronization gates** — work downstream of them
cannot proceed until they are DONE.

| Gate | Why |
|---|---|
| `T-II-2-009` (`#φ⁻¹(Q) = deg_s(φ)` for almost all Q) | Foundation for all kernel-degree proofs |
| `T-II-2-016` (factorization map = sep ∘ Frob^e) | Used in dual isogeny construction (Case 2) |
| `T-II-4-004` (separability ⇔ φ* on Ω injective) | Used in III.5.5 (Frobenius separability) |
| `T-III-1-009` (`div(ω) = 0`) | Used in III.5.1 translation invariance |
| `T-III-3-004` (Pic⁰(E) ≅ E) | Used in III.4.8 (every isogeny is a homomorphism) and III.6.1 (dual construction) |
| `T-III-4-015` (separable ⇒ #ker = deg) | Used in V.1 point counting |
| `T-III-4-016` (isogeny factorization) | Used in III.6.1 dual construction |
| `T-III-4-017` (quotient by finite subgroup) | Used in III.6.1 dual construction |
| `T-III-5-002` (pullback additivity) | Used in III.5.5 (Frobenius sep), III.5.6 (ring hom), III.6.5 (dual additivity) |
| `T-III-5-006` (ring hom End → K̄) | Used in III.6.5 (dual additivity) |
| `T-III-6-001` (dual isogeny existence) | Blocks all of III.6 and III.6.3 quadratic form |
| `T-III-6-009` (positive definite QF) | Direct prerequisite for V.1 Hasse bound |
| `T-IV-4-005` (formal group chain rule) | Bridge to III.5 |
| `T-IV-BRIDGE-003` (formal additivity ↔ curve) | Provides III.5.2 alternative path |

## Per-section dependency lists

### Stream A — Curves (Silverman II)

```
T-II-1-001 (DVR at smooth point)
   ↓
T-II-1-002 (ord_P)
   ↓
T-II-1-003 (uniformizer)
   ↓                        ↓
T-II-1-004 (no zero/pole ⇒ const)    T-II-1-005 (K(C)/K(t) finite separable)
   ↓                                              ↓
T-II-1-006 (K-rational uniformizer)            ↓
                                               ↓
T-II-2-001 (rational map = morphism on smooth) ←
   ↓
T-II-2-002 (nonconst surjective)
   ↓
T-II-2-003 (curves ↔ extensions functor)
   ↓
T-II-2-004 (deg, deg_s, deg_i)  ←  partial via SeparableDegree.lean
   ↓
T-II-2-005 (norm map φ_*)
T-II-2-006 (deg-1 = iso)
   ↓
T-II-2-007 (e_φ(P)) ←  needs II.1.3 (uniformizer)
   ↓
T-II-2-008 (Σ e_φ = deg)
   ↓
T-II-2-009 (#φ⁻¹(Q) = deg_s) ★ CRITICAL GATE
   ↓                       ↓
T-II-2-010 (chain rule)    T-II-2-011 (unramified iff)
   ↓
T-II-2-012 (Frobenius construction)
   ↓
T-II-2-013 (K(C^q) = K(C)^q)
   ↓
T-II-2-014 (Frobenius purely inseparable)
   ↓
T-II-2-015 (deg Frobenius = q)
   ↓
T-II-2-016 (factorization sep ∘ Frob^e) ★ CRITICAL GATE

T-II-3-001 (Divisor C)  ←  no deps
   ↓
T-II-3-002 (Divisor.degree)
T-II-3-003 (Div⁰)
T-II-3-004 (Galois action)
T-II-3-005 (div(f))   ←  needs II.1.2 (ord_P)
   ↓
T-II-3-006 (principal, ~)
T-II-3-007 (Pic, Pic⁰)
   ↓
T-II-3-008 (div(f) = 0 ⇔ f ∈ K̄*) ←  needs II.1.4 (no zero/pole = const)
T-II-3-009 (deg div(f) = 0)         ←  needs II.2.6 OR direct
T-II-3-010 (exact sequence)
T-II-3-011 (φ* and φ_* on divisors)
T-II-3-012 (Prop II.3.6 a-f)        ←  needs II.2.6c

T-II-4-001 (Differentials = Ω)  ←  uses mathlib KaehlerDifferential
T-II-4-002 (Ω is 1-dim)  ←  for general curves; for EC use kaehler_rank_one
T-II-4-003 (dx is basis when sep)
T-II-4-004 (separability ⇔ φ* injective) ★ CRITICAL GATE
T-II-4-005 (ω = g·dt for uniformizer t)
T-II-4-006 (df/dt regular at P)
T-II-4-007 (ord_P(ω) well-defined)
T-II-4-008 (order of f·dx)
T-II-4-009 (ord_P(ω) = 0 almost everywhere)
T-II-4-010 (div(ω))
T-II-4-011 (holomorphic, nonvanishing)
T-II-4-012 (canonical divisor class) — no RR
```

### Stream B — Weierstrass (Silverman III.1, III.2, III.3)

Most of this is in mathlib already.

```
T-III-1-001 (Weierstrass eq, b/c/Δ/j)         ✓ DONE in mathlib
T-III-1-002 (ω = dx/(2y+a₁x+a₃))             ✓ DONE locally
T-III-1-003 (change of variables)             ✓ DONE in mathlib
T-III-1-004 (nonsingular ⇔ Δ ≠ 0)             ✓ DONE in mathlib
T-III-1-005 (node ⇔ c₄ ≠ 0)                   new
T-III-1-006 (cusp ⇔ c₄ = 0)                   new
T-III-1-007 (iso ⇔ same j)                    partial
T-III-1-008 (every j₀ realized)               partial
T-III-1-009 (div(ω) = 0)  ★ CRITICAL          new (direct, no RR)
T-III-1-010 (singular curve birational ℙ¹)    optional
T-III-1-011 (Legendre form)                   optional

T-III-2-001 (composition law)                 ✓ DONE in mathlib
T-III-2-002 (abelian group)                   ✓ DONE in mathlib
T-III-2-003 (E(K) subgroup)                   ✓ DONE in mathlib
T-III-2-004 (algorithm)                       ✓ DONE in mathlib
T-III-2-005 (doubling)                        ✓ DONE in mathlib
T-III-2-006 (f even ⇔ f ∈ K(x))               new
T-III-2-007 (E_ns)                            optional
T-III-2-008 (E_ns ≅ G_a or G_m)               optional
T-III-2-009 (τ_Q : E → E translation)         new

T-III-3-001 (EC = (E,O))                      use mathlib's WeierstrassCurve
T-III-3-002 (K(E) = K(x,y), [K(E):K(x)] = 2)  new (no RR — direct)
T-III-3-003 ((P) ~ (Q) ⇒ P = Q)               new
T-III-3-004 (Pic⁰(E) ≅ E)  ★ CRITICAL         partial via Point.toClass
T-III-3-005 (D principal iff)                 new
T-III-3-006 (addition is morphism)            partial in mathlib
T-III-3-007 (exact sequence)                  new
```

### Stream C — Isogenies (Silverman III.4)

```
T-III-4-001 (Isogeny structure)               ✓ DONE
T-III-4-002 (deg, deg_s, deg_i, separable)    ✓ DONE
T-III-4-003 ([m] ≠ 0)                         partial
T-III-4-004 (Hom torsion-free)                new
T-III-4-005 (End integral domain)             new
T-III-4-006 (E[m])                            new
T-III-4-007 (deg-2 example)                   illustrative
T-III-4-008 (Frobenius endo on EC)            ✓ DONE
T-III-4-009 (translation map)                 same as III-2-009
T-III-4-010 (every isogeny is hom)            new (uses III.3.4)
T-III-4-011 (ker is finite)                   new
T-III-4-012 (#φ⁻¹(Q) = deg_s)                 new (uses II.2.6 + III.4.10)
T-III-4-013 (e_φ(P) = deg_i)                  new
T-III-4-014 (ker ≅ Aut Galois)                new
T-III-4-015 (separable ⇒ #ker = deg) ★        new
T-III-4-016 (factorization ker ⊂ ker) ★       new
T-III-4-017 (quotient by finite subgroup) ★   new
```

### Stream D — Formal groups (Silverman IV)

```
T-IV-1-001 (z, w local params)                partial
T-IV-1-002 (w(z) exists)                      partial
T-IV-1-003 (w(z) unique)                      new
T-IV-1-004 (A_n homogeneous)                  new
T-IV-1-005 (Hensel's lemma)                   partial in mathlib
T-IV-1-006 (x(z), y(z))                       new
T-IV-1-007 (ω(z))                             partial
T-IV-1-008 (F(z₁,z₂))                         ✓ DONE

T-IV-2-001 (FormalGroup R)                    new
T-IV-2-002 (FormalGroupHom)                   new
T-IV-2-003 (Ĝ_a)                              new
T-IV-2-004 (Ĝ_m)                              new
T-IV-2-005 (Ê for elliptic curve)             partial
T-IV-2-006 ([m])                              partial
T-IV-2-007 ([m](T) = mT + O(T²))              partial
T-IV-2-008 (m ∈ R* ⇒ [m] iso)                 new
T-IV-2-009 (invertibility lemma)              partial in mathlib

T-IV-3-001 (F(M))                             new
T-IV-3-002 (F(M^n))                           new
T-IV-3-003 (Ĝ_a(M) = (M, +))                  new
T-IV-3-004 (Ĝ_m(M) = (1+M, ·))                new
T-IV-3-005 (Ê(M) → E(K))                      new ★
T-IV-3-006 (F(M^n)/F(M^(n+1)) ≅ M^n/M^(n+1))  new
T-IV-3-007 (torsion p-power)                  new

T-IV-4-001 (InvariantDifferential F)          new
T-IV-4-002 (normalized)                       new
T-IV-4-003 (ω = F_X(0,T)⁻¹ dT unique)         partial
T-IV-4-004 (every inv diff = aω)              new
T-IV-4-005 (ω_G ∘ f = f'(T) ω_F)  ★ CRITICAL   new
T-IV-4-006 ([p] = pf + g(T^p))  ★ CRITICAL    new

T-IV-5-001 (log_F)                            new
T-IV-5-002 (exp_F)                            new
T-IV-5-003 (log_F iso for torsion-free)       new
T-IV-5-004 (every torsion-free formal commutative) new
T-IV-5-005 (b_n bound)                        new
T-IV-5-006 (log_F, exp_F structure)           new

T-IV-6-001 (torsion divides v(p) power)       new
T-IV-6-002 (F(pℤ_p) torsion-free p≥2)         new
T-IV-6-003 (v(n!) bound)                      new
T-IV-6-004 (formal series convergence)        new
T-IV-6-005 (log_F : F(M^r) ≅ Ĝ_a(M^r))        new
T-IV-6-006 (F(M^r) torsion-free)              new

T-IV-7-001 (height)                           new
T-IV-7-002 (height of [p])                    new
T-IV-7-003 (selected lemmas for V.1)          new

T-IV-BRIDGE-001 (omegaPullbackCoeff = formal coeff)  partial
T-IV-BRIDGE-002 (a_α ∈ F)                            new
T-IV-BRIDGE-003 (formal additivity → curve)          new
T-IV-BRIDGE-004 (Frobenius pullback = T^q)           new
T-IV-BRIDGE-005 (kaehler_rank_one)                   partial
```

### Stream E — Invariant differential + Dual

```
T-III-5-001 (τ_Q*ω = ω)              ←  needs T-III-1-009 (div ω = 0)
   ↓
T-III-5-002 ((φ+ψ)*ω = φ*ω + ψ*ω) ★  ←  needs T-IV-BRIDGE-003 OR direct via E×E
   ↓
T-III-5-003 ([m]*ω = mω)             ←  partial via T-IV-BRIDGE-001
   ↓
T-III-5-004 (m ≠ 0 ⇒ [m] separable)  ←  needs T-II-4-004
   ↓
T-III-5-005 (1-π separable)  ★       ←  needs T-III-5-002, T-IV-BRIDGE-004
   ↓
T-III-5-006 (ring hom End → K̄)  ★    ←  needs T-III-5-002 + chain rule (DONE)
   ↓
T-III-5-007 (kernel = inseparables)  ←  needs T-II-4-004
   ↓
T-III-5-008 (char 0 ⇒ commutative)

T-III-6-001 (dual existence) ★       ←  needs T-III-4-016, T-III-4-017
   ↓
T-III-6-002 (Pic⁰ description)
T-III-6-003 (φ̂∘φ = [m])             ←  T-III-6-001
T-III-6-004 ((λ∘φ)^ = φ̂∘λ̂)
T-III-6-005 ((φ+ψ)^ = φ̂+ψ̂) ★         ←  needs T-III-5-006
T-III-6-006 ([m]^ = [m], deg = m²)
T-III-6-007 (deg φ̂ = deg φ)
T-III-6-008 (φ̂̂ = φ)
T-III-6-009 (deg is positive def QF) ★ ←  needs T-III-6-005
T-III-6-010 (E[m] structure)
```

### Stream V.1 — Hasse bound

```
T-V-1-001 (E(F_q) = ker(1-π))
T-V-1-002 (1-π separable)             ←  T-III-5-005
T-V-1-003 (#E(F_q) = deg(1-π))        ←  T-III-4-015 + T-V-1-002
T-V-1-004 (#E(F_q) = q + 1 - tr π)    ←  T-V-1-003
T-V-1-005 (Cauchy-Schwarz)            ✓ DONE
T-V-1-006 (Hasse bound)               ✓ DONE algebraically; needs T-V-1-004 + T-III-6-009
```

## Stale checkout policy

A ticket that has been `CHECKED-OUT` or `IN-PROGRESS` for more than 7 days with no
Progress log entries may be released by any worker. See `PROTOCOL.md` for details.

## Tickets currently DONE in existing code

These tickets are mostly satisfied by existing files (some need minor signature
matching to fully qualify):

- `T-III-1-001` — DONE (mathlib)
- `T-III-1-002` — DONE (`InvariantDifferential.lean`)
- `T-III-1-003`, `T-III-1-004` — DONE (mathlib)
- `T-III-2-001..005` — DONE (mathlib + Affine.Formula)
- `T-III-4-001`, `T-III-4-002` — DONE (`Isogeny.lean` + `SeparableDegree.lean`)
- `T-III-4-008` — DONE (`FrobeniusIsogeny.lean`)
- `T-III-5-009`, `T-III-5-010` — DONE (`OmegaPullbackCoeff.lean` + `InvariantDifferentialPullback.lean`)
- `T-IV-1-008` — DONE (`FormalGroup.lean`)
- `T-V-1-005`, `T-V-1-006` — DONE algebraically (`HasseBound.lean`)

These are listed as `DONE` in `INDEX.md` from day 1.
