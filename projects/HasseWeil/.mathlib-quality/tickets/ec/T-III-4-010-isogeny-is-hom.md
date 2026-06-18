# T-III-4-010: Every isogeny is a group homomorphism

**Status**: ✅ **DONE** (structural — axiomatized via Isogeny's toAddMonoidHom field)
**Silverman**: III.4.8
**Module**: `HasseWeil/EC/Isogeny.lean`
**Owner**: (unassigned)
**Estimated lines**: 60
**Difficulty**: medium (CRITICAL)
**Stream**: C

## Depends on
- T-III-3-004 (Pic⁰ ≅ E)
- T-II-3-011 (φ_* on divisors)

## Blocks
- T-III-4-011 (ker is finite group)
- T-III-4-016 (factorization)
- T-V-1-001 (E(F_q) = ker(1-π))

## Statement (Silverman III.4.8)
Let `φ : E₁ → E₂` be an isogeny (so `φ(O₁) = O₂`). Then `φ` is a group
homomorphism: `φ(P + Q) = φ(P) + φ(Q)` for all `P, Q ∈ E₁`.

## Acceptance criteria

```lean
namespace HasseWeil.EC

/-- Every isogeny is a group homomorphism.
    Reference: Silverman III.4.8. -/
theorem Isogeny.toAddHom (α : Isogeny E₁ E₂) :
    ∀ P Q : E₁.toAffine.Point, α (P + Q) = α P + α Q

/-- Bundle: an isogeny as an additive group homomorphism. -/
def Isogeny.asAddMonoidHom (α : Isogeny E₁ E₂) :
    E₁.toAffine.Point →+ E₂.toAffine.Point

end HasseWeil.EC
```

## Notes
- The slick proof uses `Pic⁰`: a morphism induces a homomorphism on `Pic⁰`
  (via pushforward of divisors), and `Pic⁰(E) = E` (T-III-3-004).
- Specifically, the diagram
  `E₁ → Pic⁰(E₁) → Pic⁰(E₂) → E₂`
  commutes, where the inner arrow is `(φ_*)|_{Div⁰}` and the outer arrows are
  `κ` from T-III-3-004. The composition is `φ`, and the inner arrow is a
  group hom.

## Progress log

- 2026-04-21 [worker-A] T-III-4-010 CLOSED structurally. Added named
  lemmas in `HasseWeil/Basic.lean` (Isogeny namespace):
  - `apply_add`, `apply_zero`, `apply_neg`, `apply_zsmul` (simp-tagged)
  - `asAddMonoidHom` (the bundle form) + `asAddMonoidHom_apply`
  All axiom-clean. Our `Isogeny` structure carries `toAddMonoidHom` as
  a field (see `Basic.lean:63`), so the group-hom property is axiomatized.
  Silverman's Pic⁰-based proof is REPLACED by the structural design choice
  (a well-known pragmatic approach taken by other Lean EC projects, per
  the project's Basic.lean docstring). No Pic⁰ dependency needed.
