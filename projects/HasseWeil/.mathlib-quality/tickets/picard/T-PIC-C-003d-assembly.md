# T-PIC-C-003d: Assembly — pushforward of `div g` is `div (N g)`

**Status**: OPEN
**Silverman**: II.3.7
**Module**: `HasseWeil/Curves/PicZeroPushforward.lean`
**Owner**: —
**Estimated lines**: ~30
**Difficulty**: easy
**Phase**: C (final assembly)

## Depends on

- T-PIC-C-003a (ord ↔ multiplicity bridge)
- T-PIC-C-003b (norm-divisor at affine points)
- T-PIC-C-003c (norm-divisor at infinity)

## Blocks

- T-PIC-F-003 (B-4-003 closure) — provides the `h_pres` witness.

## Statement

```lean
theorem pushforwardProjectiveDivisor_projectiveDivisorOf
    [IsAlgClosed F]
    (φ : Isogeny W₁ W₂) (cd : φ.toCurveMap.CoordHom)
    (g : (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField) (hg : g ≠ 0) :
    pushforwardProjectiveDivisor φ cd
      ((⟨W₁⟩ : SmoothPlaneCurve F).projectiveDivisorOf g) =
      (⟨W₂⟩ : SmoothPlaneCurve F).projectiveDivisorOf
        (φ.toCurveMap.pushforward g)
```

Plus the corollary needed by `AddHomProperty_of_picZero_witnesses`:

```lean
theorem pushforwardProjectiveDivisor_principal_mem
    [IsAlgClosed F]
    (φ : Isogeny W₁ W₂) (cd : φ.toCurveMap.CoordHom)
    {D : ProjectiveDivisor (⟨W₁⟩ : SmoothPlaneCurve F)}
    (hD : D ∈ projPrincipalSubgroup ⟨W₁⟩) :
    pushforwardProjectiveDivisor φ cd D ∈ projPrincipalSubgroup ⟨W₂⟩
```

## Proof approach

Pure assembly via `Finsupp.ext`:

```lean
theorem pushforwardProjectiveDivisor_projectiveDivisorOf := by
  ext Q
  rcases Q.cases with
  | affine P => exact pushforward_div_eq_div_norm_at_affine ...
  | infinity => exact pushforward_div_eq_div_norm_at_infinity ...
```

Then the corollary:

```lean
theorem pushforwardProjectiveDivisor_principal_mem hD := by
  obtain ⟨g, hg, h_eq⟩ := hD
  exact ⟨φ.toCurveMap.pushforward g, by simpa using
    (pushforwardProjectiveDivisor_projectiveDivisorOf φ cd g hg).symm.trans
    (by rw [h_eq])⟩
```

## Acceptance criteria

```lean
#print axioms HasseWeil.EC.Isogeny.pushforwardProjectiveDivisor_projectiveDivisorOf
#print axioms HasseWeil.EC.Isogeny.pushforwardProjectiveDivisor_principal_mem
```
both report only standard axioms.

## Risks

Low. All ingredients are statements; the assembly is `Finsupp.ext` +
case-splitting. ~30 LOC.

The "norm of nonzero is nonzero" part needs `Algebra.norm_ne_zero_iff`
which holds for finite separable extensions.

## Progress log
