# Reviewer reply — ChatGPT Pro (round 10) — 2026-05-15

## Assessment

Round 10 fixed the main round-9 defect (relative cover exposes actual units). Two issues remain:

1. **W3-transport too strong if `inner_rel` is arbitrary.** A random relative Laurent tree need not have labels that transport back to absolute. Only the *canonical ratio tree* with labels `u_f * u_g⁻¹` (where `u_i = f_i / C.base.s`) is transportable.

2. **W2's unit (`s⁻¹·f`) ≠ W3's unit (`u_f = f/C.base.s`).** These are equivalent only after using that `L.canonicalMap s` and `L.canonicalMap C.base.s` are units. Add bridge lemma.

## Manager message

- Add `IsRatioLaurentTreeFrom L C I_units h_unit_base inner_rel` predicate, requiring every split label to be `u_g * u_h⁻¹` for some g, h ∈ I_units.
- W3 output: also includes this predicate.
- W3-transport input: requires this predicate.
- Add bridge lemma: `IsUnit (L.canonicalMap (s⁻¹·f)) → IsUnit (relativeUnitGenerator L C f)` (via unitness of L.canonicalMap s and L.canonicalMap C.base.s).
- Add lemma deriving `IsUnit (L.canonicalMap C.base.s)` from `L ⊆ C.base` (so I.1 composition can discharge h_unit_base).
- Wrap `Spv.comap` transport in semantic `relativeUnitPiece_transport_rationalOpen` lemma (optional).

## After these changes: architecture is correct as proof target.
