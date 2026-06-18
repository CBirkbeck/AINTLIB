# Inventory: ./HasseWeil/EC/TranslationEvaluation.lean

## Overview

This file is a **lemma-discovery / crystallisation file** containing zero named declarations.
Its entire content (lines 1–94) consists of:
- Import statements (lines 1–2)
- A module docstring explaining the purpose and proof plan for `pointValuation_translateX_xy_sub_addX_eq_zero` (Helper 2 of the ord-transport Step B'' discharge)
- Five anonymous `example` blocks (not `lemma`/`theorem`/`def`) that serve as compile-time checks of existing lemma signatures

No `def`, `lemma`, `theorem`, `instance`, `abbrev`, `structure`, or `class` declarations appear in this file.

## File metadata

| Field | Value |
|-------|-------|
| Imports | `HasseWeil.EC.Translation`, `HasseWeil.EC.TranslationOrd` |
| Namespace | `HasseWeil` |
| Total named declarations | 0 |
| `example` blocks | 5 |
| `sorry` | none |
| `set_option maxHeartbeats` | none |

## Anonymous `example` blocks (not inventoried as declarations)

### `example` 1 (lines 49–53)
Checks that `translateX_xy W xk yk` equals `(W_KE W).toAffine.addX (x_gen W) (algebraMap F W.toAffine.FunctionField xk) (translateSlope_xy W xk yk)`, via `translateX_xy_eq_addX`.

### `example` 2 (lines 55–60)
Checks that `translateY_xy W xk yk` equals `(W_KE W).toAffine.addY ...`, via `translateY_xy_eq_addY`.

### `example` 3 (lines 63–70)
Checks the mathlib addition formula `Affine.Point.add_some`: for nonsingular points `(x₁,y₁)` and `(x₂,y₂)` not in inverse position, their sum is the expected `Affine.Point.some`.

### `example` 4 (lines 77–83)
Checks `map_addX`: `(W_KE W).toAffine.addX (algMap a) (algMap b) (algMap c) = algMap (W.toAffine.addX a b c)`, via `WeierstrassCurve.Affine.map_addX`.

### `example` 5 (lines 85–93)
Checks `map_addY`: the analogous `addY` base-field compatibility, via `WeierstrassCurve.Affine.map_addY`.

## Notes

- This file has **no named declarations** whatsoever; it is purely a scratchpad / signature-crystallisation file used during development of Helper 2.
- The module docstring (lines 4–41) describes a four-step proof plan but none of the planned declarations have been written here yet.
- All five anonymous `example`s merely reference lemmas from `HasseWeil.EC.Translation`, `HasseWeil.EC.TranslationOrd`, and mathlib, and serve as type-checking witnesses only.
- No `sorry`, no `set_option maxHeartbeats`, no long proofs.
- This file is a prime candidate for eventual deletion or replacement once Helper 2 is moved into a proper `lemma`.
