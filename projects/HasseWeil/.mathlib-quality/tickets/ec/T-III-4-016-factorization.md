# T-III-4-016: ker φ ⊂ ker ψ + φ separable ⇒ ∃! λ : ψ = λ ∘ φ

**Status**: PARTIAL (witness-parametric, worker-A, 2026-04-21)
**Silverman**: III.4.11
**Module**: `HasseWeil/EC/IsogenyFactor.lean`
**Owner**: worker-A (partial)
**Estimated lines**: 400-600 unconditional (delivered ~150 witness form)
**Difficulty**: hard (CRITICAL)
**Stream**: C

## Depends on
- T-III-4-015 (separable Galois): provides `Gal(K(E₁)/φ*K(E₂)) = ker φ`
- T-III-3-005 (D principal iff): to check that the constructed `λ*` comes
  from a rational map (i.e., that the map on function fields extends to
  a morphism of curves)
- T-II-2-001 (rational map on smooth curve is a morphism)

## Blocks
- T-III-4-017 (quotient curve)
- T-III-6-001 (dual existence)

## Statement (Silverman III.4.11)
Let `φ : E₁ → E₂` and `ψ : E₁ → E₃` be isogenies, with `φ` separable. If
`ker φ ⊆ ker ψ`, then there exists a unique isogeny `λ : E₂ → E₃` such
that `ψ = λ ∘ φ`.

## Acceptance criteria

```lean
namespace HasseWeil.Isogeny

theorem factor_through_separable
    {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ W₃ : Affine F}
    [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic]
    (φ : Isogeny W₁ W₂) (hφ_sep : φ.IsSeparable)
    (ψ : Isogeny W₁ W₃)
    (hker : φ.kernel ≤ ψ.kernel) :
    ∃! λ : Isogeny W₂ W₃, ψ = λ.comp φ

end HasseWeil.Isogeny
```

## Detailed Silverman III.4.11 proof

**Setup**: `φ : E₁ → E₂` separable, `ψ : E₁ → E₃`, `ker φ ⊆ ker ψ`.

**Step 1 — Kernel action compatibility**:

Every `P ∈ ker φ` acts on `K(E₁)` as `τ_P^*` (translation pullback). By
T-III-4-015, `K(E₁)^{ker φ} = φ*(K(E₂))`.

Since `ker φ ⊆ ker ψ`: for every `P ∈ ker φ` and every `g ∈ K(E₃)`:
```
τ_P^*(ψ*(g)) = (ψ ∘ τ_P)*(g) = ψ*(g)  [because ψ(Q + P) = ψ(Q) + ψ(P) = ψ(Q)]
```
So `ψ*(g)` is fixed by `ker φ`, hence `ψ*(g) ∈ φ*(K(E₂))`.

**Step 2 — Lift to a field homomorphism `λ* : K(E₃) → K(E₂)`**:

Since `ψ*` lands in `φ*(K(E₂))`, and `φ*` is injective, define
`λ*(g) := (φ*)⁻¹(ψ*(g))` on the image. This is an F-algebra hom
`K(E₃) → K(E₂)`.

**Step 3 — `λ*` comes from a morphism of curves (Silverman II.2.4/4)**:

Given an F-algebra hom `λ* : K(E₃) → K(E₂)` between function fields of
smooth curves, there exists a unique morphism `λ : E₂ → E₃` inducing
this pullback (standard smooth-curves correspondence). This requires
T-II-2-001 (rational map ⇒ morphism on smooth curves).

**Step 4 — Commutativity `ψ = λ ∘ φ`**:

By construction, `ψ* = φ* ∘ λ*`. Since `(λ ∘ φ)* = φ* ∘ λ*`, we have
`ψ* = (λ ∘ φ)*`. Morphisms of curves are determined by their pullback
on function fields (Silverman II.2.4), so `ψ = λ ∘ φ`.

**Step 5 — `λ` is an isogeny (sends `O_{E₂}` to `O_{E₃}`)**:

`λ(O_{E₂}) = λ(φ(O_{E₁})) = ψ(O_{E₁}) = O_{E₃}` (as isogeny). So `λ`
satisfies the Isogeny structure requirement.

**Step 6 — Uniqueness**:

If `λ₁ ∘ φ = λ₂ ∘ φ`, apply pullback: `φ* ∘ λ₁* = φ* ∘ λ₂*`. By
injectivity of `φ*`, `λ₁* = λ₂*`, so `λ₁ = λ₂` (morphism uniqueness).

## Infrastructure needed

1. **Translation pullback** (T-III-2-009): `τ_P^* : K(E) → K(E)` as F-algebra
   endomorphism. ~80 lines.
2. **Field-of-invariants characterization** (consequence of T-III-4-015):
   already in scaffold.
3. **Rational map ⇒ morphism** (T-II-2-001): for smooth curves. ~200 lines.
4. **Curve morphism determined by function-field pullback** (II.2.4): ~50
   lines (mathlib may have this).
5. **Glue code**: ~100 lines.

Total: ~430 lines atop T-III-4-015.

## Witness-parametric form (delivered)

Delivered in `HasseWeil/EC/IsogenyFactor.lean`:

```lean
namespace HasseWeil.Isogeny

/-- Given pullback + point-map factor witnesses, package into an Isogeny. -/
theorem factor_through_isogeny_witness
    (φ : Isogeny W₁ W₂) (ψ : Isogeny W₁ W₃)
    (lamPb : W₃.FunctionField →ₐ[F] W₂.FunctionField)
    (h_pb : ψ.pullback = φ.pullback.comp lamPb)
    (lamHom : W₂.Point →+ W₃.Point)
    (h_hom : ψ.toAddMonoidHom = lamHom.comp φ.toAddMonoidHom) :
    ψ = (⟨lamPb, lamHom⟩ : Isogeny W₂ W₃).comp φ

/-- Existence form: ∃ λ with ψ = λ.comp φ. -/
theorem factor_through_isogeny_exists ...

/-- Uniqueness given point-map surjectivity (T-II-2-002 output). -/
theorem factor_unique_of_surjective
    (φ : Isogeny W₁ W₂) (ψ : Isogeny W₁ W₃)
    (lam₁ lam₂ : Isogeny W₂ W₃)
    (h_surj : Function.Surjective φ.toAddMonoidHom)
    (h₁ : ψ = lam₁.comp φ) (h₂ : ψ = lam₂.comp φ) :
    lam₁ = lam₂

/-- Combined `∃!` form. -/
theorem factor_through_isogeny_existsUnique_witness
    (φ : Isogeny W₁ W₂) (ψ : Isogeny W₁ W₃)
    (h_surj : Function.Surjective φ.toAddMonoidHom)
    (lamPb : W₃.FunctionField →ₐ[F] W₂.FunctionField)
    (h_pb : ψ.pullback = φ.pullback.comp lamPb)
    (lamHom : W₂.Point →+ W₃.Point)
    (h_hom : ψ.toAddMonoidHom = lamHom.comp φ.toAddMonoidHom) :
    ∃! lam : Isogeny W₂ W₃, ψ = lam.comp φ

end HasseWeil.Isogeny
```

Witness inputs map directly to the upstream tickets:
* `lamPb` + `h_pb` — from T-III-4-015 (Galois fixed-field theorem)
* `lamHom` + `h_hom` — from T-II-2-001 (smooth-curve duality)
* `h_surj` — from T-II-2-002 (nonconstant isogeny surjective)

All three dischargeable once stream-A / stream-C lands the corresponding
upstream theorems.

## Progress log

- **2026-04-18**: Detailed proof strategy added. Depends on T-III-4-015
  scaffold (now present in `HasseWeil/EC/IsogenyKernel.lean`).
- **2026-04-21** (worker-A): witness-parametric form delivered in
  `HasseWeil/EC/IsogenyFactor.lean` (~150 lines): existence + uniqueness +
  combined `∃!`. Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
  Routes Silverman III.4.11 through three named witnesses that map to
  T-III-4-015 / T-II-2-001 / T-II-2-002. Status: OPEN → PARTIAL.
