# T-II-2-016: Factorization map = sep ∘ Frobenius^e ★★ CRITICAL

**Status**: OPEN
**Silverman**: II.2.12 (Corollary)
**Module**: `HasseWeil/Curves/Maps.lean`
**Owner**: (unassigned — assigned to Worker A in revised plan, 2026-05-08)
**Estimated lines**: 80 (full II.2.12); ~30 (immediate one-Frobenius-factor case for [p])
**Difficulty**: hard
**Stream**: A

## Depends on
- T-II-2-013, T-II-2-014, T-II-2-015 (Frobenius properties)
- T-II-2-004 (degree)

## Blocks
- T-III-6-001 (dual isogeny construction Case 2/3)

## Statement (Silverman II.2.12)
Every map `ψ : C₁ → C₂` of (smooth) curves over a field of characteristic `p > 0`
factors as

```
C₁ ──φ──→ C₁^(q) ──λ──→ C₂
```

where `q = deg_i(ψ)`, `φ` is the q-power Frobenius map, and `λ` is separable.

## Acceptance criteria

```lean
namespace HasseWeil.Curves

variable {K : Type*} [Field K] [DecidableEq K] [Fintype K]
variable {C₁ C₂ : SmoothPlaneCurve K}

/-- Every map of curves factors as Frobenius^e composed with a separable map.
    Reference: Silverman II.2.12. -/
theorem Morphism.factor_through_frobenius (ψ : Morphism C₁ C₂) (hψ : ¬ IsConst ψ) :
    ∃ (e : ℕ) (λ : Morphism (Morphism.frobeniusIter C₁ e).target C₂),
      λ.IsSeparable ∧
      (Morphism.frobeniusIter C₁ e).map.toMorphism.comp λ = ψ ∧
      (Morphism.frobeniusIter C₁ e).target = (some specific frobenius iterate)

end HasseWeil.Curves
```

(The exact signature can be adjusted; the essential content is the existence
of the factorization with the right properties.)

## Notes
- Standard result: the inseparable degree of `ψ` is a power of `p`, say `q = p^e`.
  The "Frobenius part" is the e-fold composition of the p-power Frobenius. The
  remainder is separable.
- This is **the** factorization used in the dual isogeny construction (Silverman
  III.6.1, Case 2).
- The construction in Silverman: let K be the separable closure of `ψ*K(C₂)`
  in `K(C₁)`. Then `K(C₁)/K` is purely inseparable, and `K/ψ*K(C₂)` is separable.
  The intermediate K corresponds to the curve in the factorization.

## Reviewer-driven plan (2026-05-08)

External mathematical reviewer flagged two scope issues:

### SCOPE WARNING (Frobenius twists)

The relative `p`-Frobenius is

```
F_{E/k} : E → E^{(p)}
```

NOT generally an endomorphism of the same Weierstrass curve unless the
coefficients are fixed by `p`-Frobenius. Over `k = F_q`, the `q`-Frobenius
lands back on `E`, but the intermediate `p`-Frobenius steps pass through
twists `E, E^{(p)}, E^{(p^2)}, …, E^{(p^r)} ≅ E`.

**Implication for formalisation**: II.2.12 must be formalised with
Frobenius twists explicitly (codomain is `E^{(p)}`, not `E`). Avoid a
same-curve endomorphism-only statement unless `E` is over the fixed
field of the chosen Frobenius. This is the most likely hidden type-level
complication.

### Immediate scope: one-Frobenius-factor for [p]

Worker A should first prove the narrow case needed for III.6.1 Case 2:

```lean
theorem mulByNat_p_factors_through_frobenius
    [Field k] [CharP k p] [Fact (Nat.Prime p)]
    (E : WeierstrassCurve k) :
    ∃ (ψ : Isogeny E^(p) E), ψ.Separable ∧ ψ ∘ Frob_{E/k} = [p]
```

This uses `[p]*ω = 0` in characteristic `p` (one-line corollary of the
shipped `omegaPullbackCoeff_mulByInt`) → `[p]` inseparable (via
III.4.2(c)) → factorisation through `Frob_p` (the immediate II.2.12).

Generalising to full II.2.12 (any non-constant map factors through
Frobenius^e) is the broader ticket; the immediate Hasse-critical need is
just one Frobenius factor for `[p]`.

### Downstream consumer

Worker C's T-FROB-DUAL-ASSEMBLY consumes this in witness-parametric form:
`exists_dual_frobenius_of_factorization (hfac : [p] = ψ ∘ Frob) :
IsDualOf Frob ψ`. Once Worker A's theorem ships, Worker C's witness
discharges and III.6.1 Case 2 closes unconditionally.

## Progress log
