# T-PIC-C-003: `φ_*(div g) = div(N(g))` — pushforward preserves principal

**Status**: OPEN
**Silverman**: II.3 (norm map, II.3.6 pullback/pushforward properties)
**Module**: `HasseWeil/Curves/PicZeroPushforward.lean`
**Owner**: —
**Estimated lines**: ~150
**Difficulty**: medium-hard
**Phase**: C

## Depends on
- T-PIC-C-001 (`pushforwardProjectiveDivisor`)
- T-PIC-C-002 (degree preservation, used for type of N(g) in Div⁰)
- Existing `Curves.CurveMap.pushforward = Algebra.norm` (in `CurveMap.lean`)
- T-II-3-005 (DONE) — `divisorOf`, `projectiveDivisorOf`

## Blocks
- T-PIC-C-004 (descent of pushforward to `Pic⁰`)
- T-PIC-D-001, T-PIC-E-001, T-PIC-F-003

## Statement

The pushforward of a principal divisor is principal:

```lean
theorem pushforwardProjectiveDivisor_projectiveDivisorOf
    (φ : Isogeny W₁ W₂) (cd : φ.toCurveMap.CoordHom)
    (g : (⟨W₁⟩ : Curves.SmoothPlaneCurve F).FunctionField) (hg : g ≠ 0) :
    pushforwardProjectiveDivisor φ cd
      ((⟨W₁⟩ : Curves.SmoothPlaneCurve F).projectiveDivisorOf g) =
      (⟨W₂⟩ : Curves.SmoothPlaneCurve F).projectiveDivisorOf
        (φ.toCurveMap.pushforward g)
```

where `CurveMap.pushforward = Algebra.norm` is the function-field norm
(already defined in `Curves/CurveMap.lean`).

**Corollary** (immediate):
```lean
theorem pushforwardProjectiveDivisor_principal_mem (φ) (cd) (D)
    (hD : D ∈ (⟨W₁⟩).principalSubgroupProjective) :
    pushforwardProjectiveDivisor φ cd D ∈ (⟨W₂⟩).principalSubgroupProjective
```

## Mathlib check
This is "standard" but mathlib doesn't have it for our setup. The
underlying fact is: for a finite separable field extension, the norm of
a divisor equals the divisor of the norm.

For Dedekind domains, mathlib has `Ideal.relNorm` (relevant); we have
`HasseWeil/Curves/NormValuation.lean` providing the norm-valuation
bridge already (T-II-3-009 work uses this).

## Naming
- `pushforwardProjectiveDivisor_projectiveDivisorOf`
- `pushforwardProjectiveDivisor_principal_mem`

## Generality
- Phase C defaults plus `[IsAlgClosed F]` likely needed for the
  smoothPoint↔maxIdeal bijection to be reversible (so that the
  norm-of-function correspondence is invertible).

## Proof approach

The standard proof for finite morphisms:
1. For each prime `p` in `R₂` (= max ideal of `C₂.CoordinateRing`),
   `ord_p (N(g)) = Σ_{q | p} f(q/p) · ord_q(g)`
   where `f(q/p)` is the residue degree.
2. For our case (smooth curves), residue degrees are 1 (under
   `[IsAlgClosed F]`), so `ord_p(N(g)) = Σ_{q ↦ p} ord_q(g)`.
3. The pushforward divisor `(φ_* div(g))` at point `p` is
   `Σ_{q ↦ p} ord_q(g)` by definition.
4. So `ord_p(N(g)) = (φ_* div(g)) at p`, i.e., the divisors agree.

The key infrastructure:
- `Algebra.norm` (mathlib) for the function-field norm.
- `Ideal.relNorm` and related for the divisor-side norm.
- `Curves.NormValuation.lean` for the specific-to-our-setting bridge.

This is a substantive proof. Worker-K is using the same machinery for
T-II-3-009. Expect significant effort here.

**Alternative**: split this ticket into two:
- C-003a (~80 lines): finite-affine case for finite-rational points only.
- C-003b (~70 lines): infinity case, using ProjectiveDivisor's special
  handling of `.infinity`.

## Acceptance criteria

`#print axioms HasseWeil.EC.Isogeny.pushforwardProjectiveDivisor_projectiveDivisorOf`
reports only standard axioms.

## Risks

- This may genuinely require `[IsAlgClosed F]` to avoid residue-degree
  bookkeeping. If so, document as a generality regression to be resolved
  later.

## Progress log
