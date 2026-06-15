# T-III-4-017: Finite subgroup → quotient curve E/Φ

**Status**: OPEN
**Silverman**: III.4.12
**Module**: `HasseWeil/EC/IsogenyFactor.lean` (new)
**Owner**: (unassigned)
**Estimated lines**: 400-800
**Difficulty**: very hard (CRITICAL)
**Stream**: C

## Depends on
- T-III-4-015 (separable Galois): for the Galois quotient argument
- T-III-4-016 (factorization): the universal property we're targeting
- T-III-3-002 (every function field of an elliptic curve is `K(E) = F(x, y)`
  with `y` quadratic over `F(x)`): to realize the fixed field as `K(E')`

## Blocks
- T-III-6-001 (dual existence): the main application

## Statement (Silverman III.4.12)
Let `Φ ⊂ E` be a finite subgroup of `E(K̄)`. Then there exists a unique (up
to isomorphism) elliptic curve `E'` and a separable isogeny `φ : E → E'`
with `ker φ = Φ`.

## Acceptance criteria

```lean
namespace HasseWeil

/-- For any finite subgroup Φ of E, there is a quotient curve E/Φ. -/
noncomputable def WeierstrassCurve.quotientByFiniteSubgroup
    {F : Type*} [Field F] [DecidableEq F]
    (E : WeierstrassCurve F) [E.toAffine.IsElliptic]
    (Φ : AddSubgroup E.toAffine.Point) [Finite Φ] :
    Σ (E' : WeierstrassCurve F), Isogeny E.toAffine E'.toAffine

theorem WeierstrassCurve.quotient_ker
    {F : Type*} [Field F] [DecidableEq F]
    (E : WeierstrassCurve F) [E.toAffine.IsElliptic]
    (Φ : AddSubgroup E.toAffine.Point) [Finite Φ] :
    (E.quotientByFiniteSubgroup Φ).2.kernel = Φ

theorem WeierstrassCurve.quotient_isSeparable
    ...
    (E.quotientByFiniteSubgroup Φ).2.IsSeparable

end HasseWeil
```

## Detailed Silverman III.4.12 proof

**Setup**: `Φ ⊆ E(K̄)` finite subgroup. Need to construct `E' = E/Φ` and
`φ : E → E'` with `ker φ = Φ`.

**Step 1 — Construct the subfield**:

Consider the subfield `L ⊆ K̄(E)` fixed by the action of `Φ` via
translations. That is,
```
L := K̄(E)^Φ = { f ∈ K̄(E) | ∀ P ∈ Φ, τ_P^*(f) = f }
```

By Galois theory (Artin's theorem): `K̄(E)/L` is a Galois extension with
`Gal(K̄(E)/L) = Φ`, and `[K̄(E) : L] = #Φ`.

**Step 2 — Transcendence and one-variable structure**:

`L` has transcendence degree 1 over `K̄` (since `K̄(E)` has transcendence
degree 1 and `[K̄(E) : L]` is finite). So `L = K̄(t)(u)` for some
transcendental `t` and algebraic `u`.

**Step 3 — Realize `L` as `K̄(E')` for an elliptic curve**:

This is the genuinely hard step. By "curves are the spectrum of their
function field" (for smooth projective curves over `K̄`), the field `L`
corresponds to some smooth projective curve `C` over `K̄`.

To show `C` is an elliptic curve: it has genus 1 (inherited from `E`
via the étale cover `E → C` of degree `|Φ|`) and has a rational point
(the image of any rational point on `E`).

**Explicit construction** (via invariants): Given generators `x, y ∈ K̄(E)`
with `y² = x³ + ax + b`, one computes:
- `X = ∑_{P ∈ Φ} τ_P^*(x)` (Φ-invariant)
- `Y = ∑_{P ∈ Φ} τ_P^*(y)` (Φ-invariant)
- Find the relation `Y² = ...` between them (after normalization).

The result is the Weierstrass equation for `E' = E/Φ`.

This explicit construction goes back to Velú's formulas (explicit for
points `P ∈ Φ`, which give rational expressions for `X`, `Y` in terms of
`x`, `y` and the `P`). Not needed for the abstract existence.

**Step 4 — Isogeny construction**:

The inclusion `L ⊆ K̄(E)` corresponds (via function-field-curve duality)
to a morphism `φ : E → C`. This is our `E → E'` isogeny with `φ* = incl`
and `ker φ = Φ` (by Step 1).

**Step 5 — Separability**:

`K̄(E)/L` is Galois by Step 1, hence separable. So `φ* : L → K̄(E)` is
a separable extension, i.e., `φ` is separable.

**Step 6 — Uniqueness**:

If `φ' : E → E''` also has `ker φ' = Φ`, apply T-III-4-016 twice to get
isogenies `λ : E' ↔ E''` inverse to each other, so `E' ≅ E''`.

## Infrastructure needed

1. **Fixed-field construction** (Galois theory): mathlib has
   `IntermediateField.fixedField` for finite groups. ~20 lines to adapt.
2. **Tr. deg. 1 finite ext ⇒ function field of a curve** (Silverman II.2.4):
   ~300 lines (crucial and non-trivial in Lean).
3. **Image curve has genus 1 + rational point**: uses
   `Riemann-Hurwitz` for the étale cover, which needs ramification theory.
   ~200 lines OR invoke via Velú's explicit formulas.
4. **Velú's formulas (alternative explicit path)**: ~400 lines, but
   avoids the genus computation.

Total: ~500-900 lines. This is the deepest piece in the dual isogeny
chain.

## Progress log

- **2026-04-18**: Detailed proof strategy added. Depends heavily on
  T-III-4-015/016.
