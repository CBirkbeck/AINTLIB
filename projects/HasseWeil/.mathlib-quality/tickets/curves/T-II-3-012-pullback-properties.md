# T-II-3-012: Properties of φ* and φ_* (Silverman II.3.6 a–f)

**Status**: OPEN
**Silverman**: II.3.6
**Module**: `HasseWeil/Curves/Divisors.lean`
**Owner**: (unassigned)
**Estimated lines**: 200
**Difficulty**: hard
**Stream**: A

## Depends on
- T-II-3-011 (φ*, φ_* defined)
- T-II-3-005 (div(f))
- T-II-2-008 (Σ e_φ = deg)

## Blocks
- T-III-4-016 (isogeny factorization)
- T-III-3-007 (exact sequence for E)

## Statement (Silverman II.3.6)
Let `φ : C₁ → C₂` be a nonconstant morphism of smooth curves.

(a) `deg(φ* D) = (deg φ) · deg D` for all `D ∈ Div(C₂)`.
(b) `φ*(div f) = div(φ*f)` for all `f ∈ K̄(C₂)*`.
(c) `deg(φ_* D) = deg D` for all `D ∈ Div(C₁)`.
(d) `φ_*(div f) = div(N_{C₁/C₂}(f))` for all `f ∈ K̄(C₁)*`.
(e) `φ_* ∘ φ* = (deg φ) · 1` on `Div(C₂)`.
(f) If `ψ : C₂ → C₃` is another nonconst morphism, then `(ψ ∘ φ)* = φ* ∘ ψ*`
    and `(ψ ∘ φ)_* = ψ_* ∘ φ_*`.

## Acceptance criteria

```lean
namespace HasseWeil.Curves

variable {C₁ C₂ C₃ : SmoothPlaneCurve F}

/-- Pullback multiplies degree by deg(φ). Silverman II.3.6(a). -/
theorem Divisor.degree_pullback (φ : CurveMorphism C₁ C₂) (hφ : ¬ φ.IsConstant)
    (D : Divisor C₂) :
    (Divisor.pullback φ hφ D).degree = φ.degree * D.degree

/-- Pullback commutes with div(·). Silverman II.3.6(b). -/
theorem Divisor.pullback_divisorOf (φ : CurveMorphism C₁ C₂) (hφ : ¬ φ.IsConstant)
    (f : C₂.FunctionField) (hf : f ≠ 0) :
    Divisor.pullback φ hφ (divisorOf C₂ f) =
      divisorOf C₁ (φ.functionFieldHom f)

/-- Pushforward preserves degree. Silverman II.3.6(c). -/
theorem Divisor.degree_pushforward (φ : CurveMorphism C₁ C₂) (hφ : ¬ φ.IsConstant)
    (D : Divisor C₁) :
    (Divisor.pushforward φ hφ D).degree = D.degree

/-- Pushforward of div is div of norm. Silverman II.3.6(d). -/
theorem Divisor.pushforward_divisorOf (φ : CurveMorphism C₁ C₂) (hφ : ¬ φ.IsConstant)
    (f : C₁.FunctionField) (hf : f ≠ 0) :
    Divisor.pushforward φ hφ (divisorOf C₁ f) =
      divisorOf C₂ (φ.normMap f)

/-- Pushforward then pullback is multiplication by degree. Silverman II.3.6(e). -/
theorem Divisor.pushforward_pullback (φ : CurveMorphism C₁ C₂) (hφ : ¬ φ.IsConstant)
    (D : Divisor C₂) :
    Divisor.pushforward φ hφ (Divisor.pullback φ hφ D) = (φ.degree : ℤ) • D

/-- Functoriality of pullback. Silverman II.3.6(f). -/
theorem Divisor.pullback_comp (φ : CurveMorphism C₁ C₂) (ψ : CurveMorphism C₂ C₃)
    (hφ : ¬ φ.IsConstant) (hψ : ¬ ψ.IsConstant) :
    Divisor.pullback (ψ.comp φ) (...) =
      Divisor.pullback φ hφ ∘+ Divisor.pullback ψ hψ

/-- Functoriality of pushforward. Silverman II.3.6(f). -/
theorem Divisor.pushforward_comp (φ : CurveMorphism C₁ C₂) (ψ : CurveMorphism C₂ C₃)
    (hφ : ¬ φ.IsConstant) (hψ : ¬ ψ.IsConstant) :
    Divisor.pushforward (ψ.comp φ) (...) =
      Divisor.pushforward ψ hψ ∘+ Divisor.pushforward φ hφ

end HasseWeil.Curves
```

## Notes
- (a) follows from T-II-2-008 (Σ e = deg).
- (b) and (d) are the key compatibility statements between div and the maps.
- (e) is a counting fact: each `Q ∈ supp D` is hit exactly `deg φ` times when
  counted with ramification.
- This is THE central proposition for relating divisors on different curves.

## Progress log
