# T-PIC-F-003: B-4-003 closure — universal `AddHomProperty`

**Status**: PARTIAL (`AddHomProperty_of_pushforward_principal` in
`HasseWeil/Curves/Miller.lean` reduces B-4-003 to a single
witness `h_pres : pushforward preserves principal divisors`. Once
T-PIC-C-003 lands, this becomes unconditional.)
**Silverman**: III.4.8 itself
**Module**: `HasseWeil/EC/IsogenyAG/HomProperty.lean`
**Owner**: —
**Estimated lines**: ~10
**Difficulty**: trivial after dependencies
**Phase**: F

## Depends on
- T-PIC-E-001 (`AddHomProperty_of_picZero_iso`)
- T-PIC-F-002 (`picZeroEquiv`)

## Blocks
- (terminal — closes B-4-003)

## Statement

```lean
/-- **Silverman III.4.8 (universal form)**: every isogeny is a group
homomorphism on rational points, **unconditionally**. -/
theorem AddHomProperty_universal
    (φ : Isogeny W₁ W₂) (cd : φ.toCurveMap.CoordHom) :
    φ.AddHomProperty cd :=
  AddHomProperty_of_picZero_iso φ cd
    (fun D => picZeroEquiv W₁ |>.left_inv D)
    (fun D => picZeroEquiv W₂ |>.left_inv D)
```

This **discharges** the universal AddHomProperty for the new
`Isogeny.AG` structure, completing **B-4-003**.

## Mathlib check
N/A — terminal theorem of the route.

## Naming
`AddHomProperty_universal`. Optionally also expose:

```lean
/-- The bundled `AddMonoidHom` of any isogeny — no witness needed. -/
noncomputable def Isogeny.toAddMonoidHom (φ : Isogeny W₁ W₂)
    (cd : φ.toCurveMap.CoordHom) : W₁.Point →+ W₂.Point :=
  φ.toAddMonoidHomOfWitness cd (AddHomProperty_universal φ cd)
```

## Generality
Inherits from T-PIC-F-002 (likely `[IsAlgClosed F]`).

## Proof approach

One line: instantiate T-PIC-E-001 with the iso witnesses from T-PIC-F-002.

## Acceptance criteria

`#print axioms HasseWeil.EC.Isogeny.AddHomProperty_universal` reports
only standard axioms.

## Progress log
