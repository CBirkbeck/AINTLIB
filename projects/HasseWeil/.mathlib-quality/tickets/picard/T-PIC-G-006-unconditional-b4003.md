# T-PIC-G-006: Unconditional B-4-003 over arbitrary F

**Status**: OPEN
**Silverman**: III.4.8 (the original target)
**Module**: `HasseWeil/EC/IsogenyAG/HomProperty.lean`
**Owner**: —
**Estimated lines**: ~20
**Difficulty**: easy (assembly of all prior pieces)
**Phase**: G (final unconditional theorem)

## Depends on

- T-PIC-A-002d (DONE-when-shipped) — σ vanishes on principal (witness 1+2)
- T-PIC-C-003d (DONE-when-shipped) — pushforward preserves principal (witness 3)
- T-PIC-F-001c (DONE-when-shipped) — κ ∘ σ̄ = id (witness 4)
- T-PIC-E-001 (DONE) — `AddHomProperty_of_picZero_witnesses`
- T-PIC-G-005 (descent lemma)
- Mathlib: `AlgebraicClosure F` exists

## Blocks

- Final B-4-003 unconditional consumption sites.

## Statement

```lean
/-- **Silverman III.4.8 (universal)**: every isogeny of elliptic curves
over an arbitrary field is a group homomorphism on points. -/
theorem AddHomProperty_universal
    {F : Type*} [Field F] [DecidableEq F]
    {W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : Isogeny W₁ W₂) (cd : φ.toCurveMap.CoordHom) :
    φ.AddHomProperty cd
```

**No `[IsAlgClosed F]` hypothesis.**

## Proof approach

```lean
theorem AddHomProperty_universal φ cd := by
  -- Step 1: pick L = AlgebraicClosure F
  let L := AlgebraicClosure F
  haveI : IsAlgClosed L := AlgebraicClosure.instIsAlgClosed F
  haveI : (W₁.baseChange L).IsElliptic := WeierstrassCurve.baseChange_isElliptic L W₁
  haveI : (W₂.baseChange L).IsElliptic := WeierstrassCurve.baseChange_isElliptic L W₂
  -- Step 2: descent
  apply AddHomProperty.of_baseChange (L := L)
    (FaithfulSMul.algebraMap_injective F L)
  -- Step 3: use alg-closed B-4-003 (the witness-parametric form
  -- instantiated with the shipped witnesses A-002d, C-003d, F-001c)
  exact AddHomProperty_of_picZero_witnesses
    (φ.baseChange L) (cd.baseChange L)
    (projectiveDivisorSum_principal (F := L))         -- A-002d at L
    (projectiveDivisorSum_principal (F := L))         -- A-002d at L
    (pushforwardProjectiveDivisor_principal_mem (F := L)) -- C-003d at L
    (picZeroOfPoint_picZeroSum (F := L))              -- F-001c at L
```

~20 LOC.

## Naming

`AddHomProperty_universal` (drop the `_witnesses` suffix; this is the
final unconditional version).

## Generality

`[Field F] [DecidableEq F]` — full generality, including F = F_q (the
project's actual target).

## Acceptance criteria

```lean
#print axioms HasseWeil.EC.AddHomProperty_universal
```
reports only standard axioms (no `IsAlgClosed F` hypothesis, no
new sorries, no unfilled axioms beyond mathlib's foundations).

## Cleanup

- Mark T-PIC-F-003 as **subsumed** by T-PIC-G-006 (this is the
  unconditional version of what F-003 was scoped to provide).
- Update `INDEX.md` to mark all picard/ tickets as DONE.

## Risks

- The `AlgebraicClosure F` instance comes "for free" from mathlib but
  requires `[DecidableEq F]` (already in our hypothesis list).
- The `WeierstrassCurve.baseChange_isElliptic` — need to verify mathlib
  name. Likely `WeierstrassCurve.IsElliptic.baseChange` or similar.
  ~5 LOC of typeclass plumbing.
- Witness instantiation at L (AlgebraicClosure F) needs to typecheck
  cleanly; `[IsAlgClosed L]` should propagate from the synthesized
  instance.

## Progress log
