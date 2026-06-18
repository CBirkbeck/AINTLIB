# T-II-3-011: φ* and φ_* on divisors

**Status**: OPEN
**Silverman**: II.3 (definition)
**Module**: `HasseWeil/Curves/Divisors.lean`
**Owner**: (unassigned)
**Estimated lines**: 80
**Difficulty**: medium
**Stream**: A

## Depends on
- T-II-3-001 (Divisor C)
- T-II-2-001 (rational map ⇒ morphism)
- T-II-2-007 (ramification index `e_φ(P)`)

## Blocks
- T-II-3-012 (properties of φ*/φ_*)
- T-III-4-016 (factorization of isogenies)

## Statement (Silverman II.3)
For a nonconstant morphism `φ : C₁ → C₂` of smooth curves, define
- the **pullback** `φ* : Div(C₂) → Div(C₁)` by `φ*(Q) = Σ_{P ∈ φ⁻¹(Q)} e_φ(P) · (P)`
- the **pushforward** `φ_* : Div(C₁) → Div(C₂)` by `φ_*(P) = (φ(P))`

extended ℤ-linearly to all divisors.

## Acceptance criteria

```lean
namespace HasseWeil.Curves

/-- The pullback of a divisor under a nonconstant morphism of curves.
    Reference: Silverman II.3. -/
def Divisor.pullback (φ : CurveMorphism C₁ C₂) (hφ : ¬ φ.IsConstant) :
    Divisor C₂ →+ Divisor C₁

/-- The pushforward of a divisor under a nonconstant morphism of curves.
    Reference: Silverman II.3. -/
def Divisor.pushforward (φ : CurveMorphism C₁ C₂) (hφ : ¬ φ.IsConstant) :
    Divisor C₁ →+ Divisor C₂

scoped notation:max φ "^*" => Divisor.pullback φ
scoped notation:max φ "_*" => Divisor.pushforward φ

lemma Divisor.pullback_single (φ : CurveMorphism C₁ C₂) (hφ : ¬ φ.IsConstant)
    (Q : C₂) :
    Divisor.pullback φ hφ (Divisor.single Q 1) =
      ∑ P in φ.fiber Q, (φ.ramificationIndex P : ℤ) • Divisor.single P 1

lemma Divisor.pushforward_single (φ : CurveMorphism C₁ C₂) (hφ : ¬ φ.IsConstant)
    (P : C₁) :
    Divisor.pushforward φ hφ (Divisor.single P 1) = Divisor.single (φ P) 1

end HasseWeil.Curves
```

## Notes
- Both maps are group homomorphisms.
- Need finiteness of fibers (T-II-2-002 surjectivity + properness).
- The pullback formula uses ramification indices.

## Progress log
