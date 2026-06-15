# Development Plan: Eliminate All Sorries in Hasse-Weil

## Goal
Prove Hasse's theorem `|#E(F_q) - q - 1| <= 2*sqrt(q)` in Lean 4 with **zero sorries**
and only standard axioms (propext, Classical.choice, Quot.sound).

## Current State
- 17 sorries across 6 files
- Root cause: `Basic.lean` has axiomatic Isogeny with degree as free data
- A restructured `Basic.lean` exists in worktree `agent-af4a1e78` with computed degree
- The project builds successfully; HasseBound.lean proofs are complete modulo upstream sorries

## Architecture Decision: Computed Degree from Pullback

The unified `Isogeny` carries:
1. `pullback : K(E2) ->_a[F] K(E1)` (injective F-algebra hom on function fields)
2. `toAddMonoidHom : E1.Point ->+ E2.Point` (group hom on rational points)
3. `degree` = `Module.finrank` from pullback (COMPUTED, not stored)

Degree multiplicativity follows from the tower law (already proved in Isogeny.lean).

## Key Mathlib Resources

| Resource | Mathlib Location | Use |
|----------|-----------------|-----|
| `natDegree_Phi` | `EllipticCurve/DivisionPolynomial/Degree.lean` | deg(Phi_n) = n^2 |
| `natDegree_PsiSq` | same | deg(PsiSq_n) = n^2-1 |
| `norm_smul_basis` | `EllipticCurve/Affine/Point.lean:412` | Norm on coordinate ring |
| `Point.map` | `EllipticCurve/Affine/Point.lean:791` | Group hom from algebra hom |
| `Module.finrank_mul_finrank` | `LinearAlgebra/Dimension/` | Tower law |
| `Field.finSepDegree` | `FieldTheory/SeparableDegree.lean` | Separable degree |
| `Algebra.norm` | `RingTheory/Norm/Basic.lean` | Norm of field extension |
| `Algebra.trace` | `RingTheory/Trace/Defs.lean` | Trace of field extension |

## Proof Strategy

### For deg([n]) = n^2
Use `natDegree_Phi` from mathlib: deg(Phi_n) = n^2. The pullback [n]* sends x -> Phi_n/Psi_n^2
in K(E). The extension degree [K(E) : [n]*K(E)] = n^2 follows from the polynomial degree.

### For the Hasse Bound
The restructured approach:
1. Frobenius pullback is concrete: f -> f^q, degree = q (from extension theory)
2. For the quadratic form: `deg(r*pi - s)` is computed from the explicit pullback
3. The pullback of `r*pi - s` uses the addition formula on the Weierstrass model
4. The resulting extension degree equals `q*r^2 - t*r*s + s^2`
5. Since degree is Module.finrank (a natural number), it's >= 0
6. Non-negativity for all r,s gives t^2 <= 4q

### For the Dual Isogeny
Instead of constructing a general dual, we construct it for specific endomorphisms:
- [n]_hat = [n] (self-dual, from [n]o[n] = [n^2])
- For the quadratic form proof, we bypass the dual by computing degrees directly

## File Structure

```
Basic.lean        -- Unified Isogeny structure (restructured)
Endomorphism.lean -- Endomorphism arithmetic (updated)
DualIsogeny.lean  -- Dual isogeny (to be restructured or eliminated)
DegreeQuadraticForm.lean -- Degree quadratic form (reproved via norm)
Frobenius.lean    -- Frobenius (updated)
HasseBound.lean   -- Final assembly (mostly unchanged)
PullbackCoeff.lean -- Pullback coefficient (reproved via Kahler diff)
Ramification.lean  -- Dedekind domain (independent)
```

## Dependency Graph
```
Isogeny.lean (concrete, 0 sorry) -+-> Basic.lean (unified)
DivisionPolynomial.lean ----------+     |
InvariantDifferential.lean -------+     v
                              Endomorphism.lean
                                   |
                   +---------------+---------------+
                   v               v               v
           PullbackCoeff    DualIsogeny      Frobenius
                   |               |               |
                   +-------+-------+               |
                           v                       |
                  DegreeQuadraticForm              |
                           |                       |
                           +-----------+-----------+
                                       v
                                  HasseBound

Ramification.lean (independent)
```
