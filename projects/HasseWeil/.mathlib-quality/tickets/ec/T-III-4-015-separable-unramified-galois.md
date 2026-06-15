# T-III-4-015: φ separable ⇒ unramified, #ker = deg, K(E₁)/φ*K(E₂) Galois

**Status**: PARTIAL (witness-parametric via `card_kernel_eq_degree_of_separable_witness`, worker-A)
**Silverman**: III.4.10(c)

**Reviewer-driven correction (2026-05-08)**: the original ticket framed this
as needing the **fixed-field reverse inclusion** `K(E)^{ker φ} ⊆ φ*K(E')`
via descent through the quotient `E/ker φ ≅ E'`. **Silverman does NOT use
this route.** Silverman III.4.10(c) follows directly from III.4.10(a) at
`Q = O`: `#ker φ = #φ⁻¹(O) = deg_s φ = deg φ` (separable). The Galois
property is a **consequence** of (a)+(b), not the substantive deep step.

The substantive content is therefore **T-II-2-009** (Silverman II.2.6(b),
generic-fibre theorem) + the translation bootstrap. See T-II-2-009 for the
revised plan. This ticket closes mechanically once T-II-2-009 closes.
**Module**: `HasseWeil/EC/IsogenyKernel.lean` (scaffold) → `HasseWeil/EC/IsogenyFactor.lean` (full)
**Owner**: (unassigned)
**Estimated lines**: 300-500
**Difficulty**: hard (CRITICAL)
**Stream**: C

## Depends on
- T-III-4-012 (#fiber = deg_s): fiber cardinality of a finite morphism
- T-III-4-013 (e_φ = deg_i): ramification index equals inseparable degree
- T-III-4-014 (ker iso to Aut): kernel acts faithfully as Galois automorphisms
- T-III-2-009 (translation τ_Q on K(E)): for the kernel action on `K(E₁)`

## Blocks
- T-III-6-001 (dual existence)
- T-V-1-003 (#E(F_q) = deg(1-π))

## Statement (Silverman III.4.10(c))
Let `φ : E₁ → E₂` be a nonzero **separable** isogeny. Then:
- `φ` is unramified (every `e_φ(P) = 1`)
- `#ker φ = deg φ`
- `K̄(E₁)/φ*K̄(E₂)` is a Galois extension (and `ker φ ≅ Gal`).

## Acceptance criteria

Current scaffold (in `HasseWeil/EC/IsogenyKernel.lean`):
```lean
namespace HasseWeil.Isogeny

/-- Separability of the function-field extension K(E₁)/φ*K(E₂). -/
def IsSeparable (φ : Isogeny W₁ W₂) : Prop :=
  @Algebra.IsSeparable W₂.FunctionField W₁.FunctionField _ _ φ.toAlgebra

/-- Scaffold: the kernel as AddSubgroup. -/
noncomputable def kernel (φ : Isogeny W₁ W₂) : AddSubgroup W₁.Point :=
  φ.toAddMonoidHom.ker

end HasseWeil.Isogeny
```

Target (to be added in `IsogenyFactor.lean`):
```lean
theorem Isogeny.card_kernel_eq_degree_of_separable
    {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : Affine F}
    [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : Isogeny W₁ W₂) (hsep : φ.IsSeparable) [Finite φ.kernel] :
    Nat.card φ.kernel = φ.degree
```

## Detailed Silverman III.4.10(c) proof

**Setup**: `φ : E₁ → E₂` nonzero, separable isogeny. Write `K_i = K̄(E_i)`.
- `deg_s φ = deg φ` (separability)
- `deg_i φ = 1` (inseparable part trivial)

**Step 1 — Every fiber has size `deg_s φ = deg φ`**:

For a finite morphism of smooth curves, every fiber has cardinality between
`deg_s / deg_i` and `deg_s` (Silverman II.2.6). For unramified points the
inequality becomes equality. Since `φ` is separable with `deg_i = 1`, every
`e_φ(P) = 1` (Silverman III.4.10(a)), so every fiber has exactly `deg_s =
deg` points.

**Step 2 — `ker φ` = fiber over `O₂`**:

By `Isogeny.toAddMonoidHom` sending `0 ↦ 0`, the fiber over `0_{E₂}` is
`{P ∈ E₁ | φ(P) = 0} = ker φ`. Hence `#ker φ = deg φ`.

**Step 3 — Galois extension**:

`ker φ` acts on `E₁` by translations `τ_P : Q ↦ Q + P`. This induces an
action on `K_1 = K̄(E₁)` by `τ_P^* : f ↦ f ∘ τ_{-P}`. Key facts:
- **Fixed field**: `(K_1)^{ker φ} = φ^*(K_2)`. A function `f ∈ K_1` satisfies
  `τ_P^* f = f` for all `P ∈ ker φ` iff `f` is constant on fibers of `φ`,
  which (for surjective morphisms) is iff `f ∈ φ^*(K_2)`.
- **Order**: `|ker φ| = deg φ = [K_1 : φ^*(K_2)]`.

By Artin's theorem: if a finite group `G` acts faithfully on a field `L`
with fixed field `K`, then `L/K` is Galois with `Gal(L/K) = G`. Applied
with `G = ker φ`, `L = K_1`, `K = φ^*(K_2)`:
- Faithfulness: `τ_P^* = id ⟺ P = 0` (free transitive action on points).
- Hence `K_1/φ^*(K_2)` is Galois with `Gal ≅ ker φ`.

## Infrastructure needed

1. **Finite-fiber lemma** (II.2.6): For a finite morphism of smooth curves,
   fibers have cardinality between `deg_s/deg_i` and `deg_s`. ~200 lines.
2. **Translation map** (T-III-2-009): `τ_Q : K(E) → K(E)` as an F-algebra
   endomorphism. ~80 lines.
3. **Fixed-field identification**: `(K(E))^{ker φ} = φ*(K(E'))`. ~150 lines.
4. **Artin's theorem invocation**: mathlib has this as
   `IsGalois.of_fixedField` (in `Mathlib.FieldTheory.Galois`). Free.

Total: ~430 lines + composition.

## Alternative: via étale morphism theory

An isogeny is étale ⟺ separable. For étale morphisms of smooth curves,
finite-fibers + Galois are both consequences of étale-fundamental-group
theory. But this requires mathlib's étale-morphism theory which is
itself not fully developed for elliptic curves.

## Progress log

- **2026-04-18**: Created scaffold in `HasseWeil/EC/IsogenyKernel.lean`:
  `Isogeny.kernel`, `mem_kernel_iff`, `zero_mem_kernel`, `kernel_id`,
  `kernel_comp_le`, `IsSeparable`. Build clean, no new sorries introduced.
  Full theorem statements deferred to `IsogenyFactor.lean` (TBD).
