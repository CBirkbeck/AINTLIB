# Reviewer reply — ChatGPT Pro (round 19) — 2026-05-15

## Assessment

None of the existing three Wedhorn 2.13 shapes fits P3 as-is.

Shape A and Shape B are overlap/equality-shape theorems. They model the locus where two values become equal, or where one passes through a minus/overlap construction. P3 needs the **half-space**

```
rationalOpen(L) ∩ {v(g) ≤ v(h)}.
```

That is not an overlap datum.

Shape C is the right theorem direction only after the absolute datum is already known. But P3 is precisely trying to construct that absolute datum. So Shape C cannot be used directly.

The right next theorem is **not** the fully general reverse Wedhorn 2.13 for arbitrary relative rational data. That is probably true and useful, but it is bigger than what P3 needs. The right target is a special reverse theorem for the actual P3 shape:

```lean
relative_ratio_split_transports_to_RatioNodeData :
  IsUnit (relativeUnitGenerator L C g h_unit_base) →
  IsUnit (relativeUnitGenerator L C h h_unit_base) →
  ∃ data : RatioNodeData L g h
```

This theorem should be proved by the Spa/presheaf-value equivalence and rational-subdomain stability, not by trying to prove the old-pair `hopen` statement

```
b/h ∈ locSubring(L.P, {g}, h).
```

That old-pair `hopen` obstruction is real and expected. It is not what Wedhorn uses.

## Mathematical idea

The ratio split lives naturally over

```
B := O(L).
```

The units are

```
u_g = image_L(g) / image_L(C.base.s),
u_h = image_L(h) / image_L(C.base.s).
```

The relative Laurent split at

```
r := u_g * u_h⁻¹
```

has plus piece

```
R_B({r}/1) = {w ∈ Spa(B) | w(r) ≤ 1}.
```

Under the homeomorphism

```
Spa(O(L)) ≃ rationalOpen(L) ⊆ Spa(A),
```

this piece becomes

```
{v ∈ rationalOpen(L) | v(g) ≤ v(h)}.
```

The proof is just cancellation of the common denominator `C.base.s`:

```
w(u_g) ≤ w(u_h)
⇔ v(g)/v(C.base.s) ≤ v(h)/v(C.base.s)
⇔ v(g) ≤ v(h),
```

because `C.base.s` is a unit on `O(L)` and hence nonzero at every point.

Wedhorn's proof does not require writing down the transported absolute datum using the old pair `L.P`. He uses the fact that rational subsets of a rational subset are again rational subsets of the original adic spectrum, and that the corresponding completed localizations agree. In Lean terms, this means the missing theorem is a **relative rational subdomain representation theorem**, not an approximate-inverse lemma in the original locSubring.

So the theorem you need is a P3-specialized reverse Wedhorn 2.13, not Shapes A/B/C and not a fully arbitrary reverse theorem.

## Lean-facing next steps

Do not continue trying to prove `hopen` for

```
T = {g}, s = h, P = L.P
```

or for the denominator-cleared datum with denominator `L.s * h`. That proof should not exist in the required generality.

Add a theorem at exactly the P3 boundary:

```lean
theorem relative_ratio_split_transports_to_RatioNodeData
    (L : RationalLocData A)
    (C : RationalCovering A)
    (g h : A)
    (h_unit_base : IsUnit (L.canonicalMap C.base.s))
    (hug : IsUnit (relativeUnitGenerator L C g h_unit_base))
    (huh : IsUnit (relativeUnitGenerator L C h h_unit_base)) :
    ∃ data : RatioNodeData L g h
```

The proof should internally use these pieces:

1. **A reverse Spa equivalence for presheaf values**:

   ```lean
   exists_spa_presheafValue_point_over_rationalOpen_point :
     v ∈ rationalOpen L.T L.s →
     ∃ w : Spa (presheafValue L), comap L.canonicalMap w = v
   ```

   or the project's equivalent `Spa(O(L)) ≃ rationalOpen(L)`.

2. **A rational-open transport lemma for the relative unit generator**:

   ```lean
   relativeUnitGenerator_vle_transport :
     w(relativeUnitGenerator L C g h_unit_base)
       ≤ w(relativeUnitGenerator L C h h_unit_base)
     ↔
     (comap L.canonicalMap w).vle g h
   ```

3. **A special absolute-representation theorem**:

   ```lean
   exists_absolute_ratio_rationalLocData :
     ∃ plus minus : RationalLocData A,
       rationalOpen plus.T plus.s =
         {v ∈ rationalOpen L.T L.s | v.vle g h} ∧
       rationalOpen minus.T minus.s =
         {v ∈ rationalOpen L.T L.s | v.vle h g}
   ```

   This is the actual reverse Wedhorn 2.13 special case. It should not prescribe `plus.P = L.P`.

4. **Package** those `plus` and `minus` into `RatioNodeData L g h`.

If the special absolute-representation theorem is awkward, prove the slightly more general but still controlled version:

```lean
theorem exists_absolute_rationalLocData_of_relative_unit_generated
    (L : RationalLocData A)
    (Drel : RationalLocData (presheafValue L))
    -- Drel is built from finitely many units / relative rational generators
    :
    ∃ Dabs : RationalLocData A,
      rationalOpen Dabs.T Dabs.s =
        image/comap of rationalOpen Drel.T Drel.s
```

But do **not** start with a theorem for arbitrary relative data unless the special theorem collapses into the same proof.

For the bridge lemma

```lean
IsUnit (D.canonicalMap g) → v(g) ≠ 0
```

use the same Spa-equivalence theorem. Do not use the density/uniform-inducing/nonarch triangle proof unless the Spa equivalence route is blocked.

## Answers

**Q1.** No existing Shape A/B/C fits P3. Shape A/B give overlap/equality-type loci. Shape C requires the absolute datum as input. Do not try to express P3 through iterated-minus or iterated-overlap.

**Q2.** Build a new **specific** Wedhorn 2.13 reverse instance for relative unit-ratio splits. This is smaller and better targeted than the fully general reverse theorem. If that proof naturally generalizes, factor it later.

**Q3.** Wedhorn does not write an explicit absolute datum with the old pair `L.P`. He uses stability of rational localizations/rational subdomains. Your Lean theorem should follow that: output some `RationalLocData A` with the right rational-open equality, not a predetermined denominator-cleared datum using `L.P`.

**Q4.** Wedhorn 7.49's reverse direction is a real theorem: valuations on the rational subset lift to valuations on the completed rational localization. It is not field-specific. Mathlib's field-only `Valued.extensionValuation` is not the right direct tool. You need a project-level Spa/presheaf-value equivalence or at least the special lifting theorem above.

**Q5.** This is a focused project-internal infrastructure gap, not a full mathlib-level rewrite. But it is substantive. The key theorem is the reverse Spa equivalence / reverse rational-subdomain representation. Do that before continuing W3-transport.

## Risks or missing facts

The main risk is wasting time trying to prove `hopen` for a fixed old pair. The correct absolute representative may require a different pair/data package; Wedhorn does not force the old pair.

The second risk is trying to weaken `RatioNodeData` to image-only data. Keep `RatioNodeData` with literal rational-open equalities.

The third risk is overgeneralizing too soon. A fully general reverse Wedhorn 2.13 theorem is attractive but may be much larger than needed. P3 only needs relative unit-ratio splits.

## Manager message

Do not try to fit P3 into existing Shapes A/B/C. None fits.

Do not try to prove the denominator-cleared `hopen` over `L.P`. That is the wrong construction.

New target:

```lean
relative_ratio_split_transports_to_RatioNodeData
```

Prove it as a special reverse Wedhorn 2.13 theorem for the relative Laurent split at

```lean
r = u_g * u_h⁻¹
```

inside `O(L)`. Use the Spa equivalence

```
Spa(O(L)) ≃ rationalOpen(L)
```

to show the relative plus piece transports to

```lean
{v ∈ rationalOpen L.T L.s | v.vle g h}
```

and the minus piece transports to

```lean
{v ∈ rationalOpen L.T L.s | v.vle h g}.
```

Then produce whatever absolute `RationalLocData A` the reverse-rational-subdomain theorem gives, and package it as `RatioNodeData`.

If needed, first prove the special lifting theorem:

```lean
v ∈ rationalOpen L.T L.s →
∃ w : Spa (presheafValue L), comap L.canonicalMap w = v
```

This also closes the unit-nonvanishing bridge.
