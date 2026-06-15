# T-PIC-D-001: Diagram commute `κ_E₂ ∘ φ_pt = φ_∗ ∘ κ_E₁`

**Status**: OPEN
**Silverman**: III.4.8 proof — the commutative square between E and Pic⁰
**Module**: `HasseWeil/EC/IsogenyAG/HomProperty.lean` (NEW FILE)
**Owner**: —
**Estimated lines**: ~30
**Difficulty**: easy
**Phase**: D

## Depends on
- T-PIC-A-004 (`picZeroSumHom`)
- T-PIC-B-001 (`picZeroOfPoint`)
- T-PIC-B-003 (round-trip identity)
- T-PIC-C-004 (`pushforwardPicZero`)

## Blocks
- T-PIC-E-001 (witness-parametric universal)

## Statement

The diagram from Silverman's III.4.8 proof commutes:

```
        φ_pt = φ.toPointMap cd
W₁.Point ──────────────────────→ W₂.Point
   |                                 |
   |  κ = picZeroOfPoint              |  κ = picZeroOfPoint
   ↓                                 ↓
PicProj₀ W₁ ──────────────────→ PicProj₀ W₂
        φ_∗ = pushforwardPicZero
```

In Lean:

```lean
theorem picZeroOfPoint_pushforwardPicZero
    (φ : Isogeny W₁ W₂) (cd : φ.toCurveMap.CoordHom)
    (P : W₁.Point) :
    picZeroOfPoint W₂ (φ.toPointMap cd P) =
      pushforwardPicZero φ cd (picZeroOfPoint W₁ P)
```

(Naming reflects that this is a single equation in `Pic⁰`, not a
diagram.)

## Mathlib check
Trivial after the structural pieces.

## Naming
`picZeroOfPoint_pushforwardPicZero` (long but unambiguous; see if a
shorter mathlib-style name fits).

## Generality
Same as Phase C defaults (carries `[IsAlgClosed F]` if C-003 needed it).

## Proof approach

```lean
theorem picZeroOfPoint_pushforwardPicZero
    (φ : Isogeny W₁ W₂) (cd : φ.toCurveMap.CoordHom)
    (P : W₁.Point) :
    picZeroOfPoint W₂ (φ.toPointMap cd P) =
      pushforwardPicZero φ cd (picZeroOfPoint W₁ P) := by
  -- LHS unfolds to PicProj₀.mk ⟨(φ(P)) - (O), _⟩.
  -- RHS unfolds to:
  --   pushforwardPicZero (PicProj₀.mk ⟨(P) - (O), _⟩)
  --   = PicProj₀.mk ⟨pushforwardProjectiveDivisor ((P) - (O)), _⟩
  --   = PicProj₀.mk ⟨(φ(P)) - (φ(O)), _⟩
  --   = PicProj₀.mk ⟨(φ(P)) - (O), _⟩      -- since φ(O) = O via toPointMap_zero
  -- Hence equal.
  ...
```

The key step is `φ.toPointMap cd 0 = 0` which is the existing
`Isogeny.toPointMap_zero` lemma in `IsogenyAG.lean`.

## Acceptance criteria

`#print axioms HasseWeil.EC.Isogeny.picZeroOfPoint_pushforwardPicZero`
reports only standard axioms.

## Progress log
