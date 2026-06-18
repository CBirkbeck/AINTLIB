# T-PIC-C-002: Pushforward preserves degree (lands in `Div⁰`)

**Status**: DONE (`degree_pushforwardProjectiveDivisor` +
`pushforwardDegZero` in `HasseWeil/Curves/PicZeroPushforward.lean`,
axiom-clean)
**Silverman**: II.3 (degree of pushforward = degree)
**Module**: `HasseWeil/Curves/PicZeroPushforward.lean`
**Owner**: —
**Estimated lines**: ~80
**Difficulty**: medium
**Phase**: C

## Depends on
- T-PIC-C-001 (`pushforwardProjectiveDivisor`)

## Blocks
- T-PIC-C-004 (group hom on Pic⁰)

## Statement

```lean
theorem degree_pushforwardProjectiveDivisor (φ : Isogeny W₁ W₂)
    (cd : φ.toCurveMap.CoordHom)
    (D : ProjectiveDivisor (⟨W₁⟩ : SmoothPlaneCurve F)) :
    (pushforwardProjectiveDivisor φ cd D).degree = D.degree

/-- The pushforward restricts to a hom on Div⁰. -/
noncomputable def pushforwardDegZero (φ : Isogeny W₁ W₂)
    (cd : φ.toCurveMap.CoordHom) :
    ProjectiveDivisor.degZero (⟨W₁⟩ : SmoothPlaneCurve F) →+
      ProjectiveDivisor.degZero (⟨W₂⟩ : SmoothPlaneCurve F) where
  toFun D := ⟨pushforwardProjectiveDivisor φ cd D.val,
    by rw [degree_pushforwardProjectiveDivisor]; exact D.property⟩
  map_zero' := ...
  map_add' := ...
```

## Mathlib check
Not in mathlib at the curve level. `Finsupp.sum_mapDomain_index` provides
the underlying degree-sum lemma.

## Naming
- `degree_pushforwardProjectiveDivisor` (the main fact)
- `pushforwardDegZero` (the restricted hom)

## Generality
Same as Phase C defaults.

## Proof approach

`degree D = D.support.sum fun P => D P` (treating coefficients as
degree-1 contributions, summed in ℤ). Pushforward via `Finsupp.mapDomain`
preserves the sum of values:

```
degree (pushforward D)
  = (pushforward D).support.sum fun Q => (pushforward D) Q
  = (Finsupp.mapDomain f D).sum fun Q n => n
  = D.sum fun P n => n      -- by Finsupp.sum_mapDomain_index
  = degree D
```

The Finsupp lemma `Finsupp.sum_mapDomain_index` is:
```
∀ {α β γ} [AddCommMonoid γ] (f : α → β) (h : β → γ → γ) (g : α →₀ γ)
  (h_zero : ∀ b, h b 0 = 0)
  (h_add : ∀ b c₁ c₂, h b (c₁ + c₂) = h b c₁ + h b c₂),
  (g.mapDomain f).sum h = g.sum fun a c => h (f a) c
```

Apply with `h b n := n` (independent of b).

## Acceptance criteria

`#print axioms HasseWeil.EC.Isogeny.degree_pushforwardProjectiveDivisor`
reports only standard axioms.

## Progress log
