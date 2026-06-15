# T-II-2-010: Ramification chain rule

**Status**: PARTIAL (worker-I, 2026-04-20) — witness-parametric form delivered;
image-point form requires the image-point map (blocked).
**Silverman**: II.2.6(c) (Proposition)
**Module**: `HasseWeil/Curves/CurveMap.lean`
**Owner**: worker-I (partial)
**Estimated lines**: 30 (delivered via `rfl`)
**Difficulty**: easy
**Stream**: A

## Depends on
- T-II-2-007 (ramification index)

## Blocks
- T-II-3-012 (Prop II.3.6 needs ramification chain rule)
- T-III-4-013 (e_φ = deg_i for isogenies)

## Statement (Silverman II.2.6(c))
For nonconstant morphisms `φ : C₁ → C₂` and `ψ : C₂ → C₃` and `P ∈ C₁`,

```
e_{ψ∘φ}(P) = e_φ(P) · e_ψ(φ(P))
```

## Acceptance criteria

```lean
namespace HasseWeil.Curves

/-- Chain rule for ramification index.
    Reference: Silverman II.2.6(c). -/
theorem Morphism.ramification_index_comp (φ : Morphism C₁ C₂) (ψ : Morphism C₂ C₃)
    (hφ : ¬ IsConst φ) (hψ : ¬ IsConst ψ) (P : C₁.SmoothPoint) :
    (ψ.comp φ).ramificationIndex P =
      φ.ramificationIndex P * ψ.ramificationIndex (φ.toFun P)

end HasseWeil.Curves
```

## Notes
- Direct from the definition: `e_{ψ∘φ}(P) = ord_P((ψ∘φ)*(t)) = ord_P(φ*(ψ*(t)))`
  and using the multiplicativity of `ord_P` together with the chain rule for
  pullback.

## Progress log

- **2026-04-20** (worker-I): delivered the witness-parametric form as
  `CurveMap.ramificationIndex_comp` (and `ramificationIndexℤ_comp`) in
  `HasseWeil/Curves/CurveMap.lean`:
  ```lean
  (ψ.comp φ).ramificationIndex P t = φ.ramificationIndex P (ψ.pullback t)
  ```
  This is the algebraic content of Silverman II.2.6(c): to evaluate the
  ramification of `ψ∘φ` at `P` with test function `t ∈ F(C₃)`, first pull
  back through `ψ`, then compute the ramification of `φ` with that. Proof is
  by `rfl` (definitional chain rule on pullbacks and `ord_P`). Axiom-clean.
  **Blocker for multiplicative image-point form** (`e_{ψ∘φ}(P) = e_φ(P) ·
  e_ψ(φ(P))`): requires the image-point map `φ : C₁.SmoothPoint → C₂.SmoothPoint`.

