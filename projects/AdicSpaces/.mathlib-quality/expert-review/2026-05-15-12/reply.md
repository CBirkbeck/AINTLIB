# Reviewer reply — ChatGPT Pro (round 17) — 2026-05-15

## Assessment

The obstruction in P3 is real, but it does **not** invalidate the round-16 architecture. It shows that P3 is trying to construct the absolute ratio node in the wrong way.

The issue is not `plus_open_eq`; the issue is trying to build the absolute ratio piece directly from a fixed pair `L.P` and denominator `L.s * h`. That asks for an `hopen` witness which is not available from "`h` is a unit in `O(L)`." This is expected: the inverse of `h` lives in the completed rational localization, not necessarily in the algebraic localization subring over the original pair of definition.

So I would not choose Option A, and I would not pursue Option C. Option B is directionally closer, but I would phrase it differently:

**Do not construct a new pair of definition of `A` ad hoc from a completion-side inverse. Instead, construct the ratio split as a relative rational datum over `O(L)` and then transport it back to an absolute `RationalLocData A` using the already-closed relative rational localization/transitivity API.**

This preserves the literal equalities in `RatioNodeData`, avoids false `hopen` goals, and matches Wedhorn's proof: the ratio cover is naturally a Laurent cover over the affinoid `O(L)`, not a primitive rational datum over `A` with the old pair `L.P`.

## Mathematical idea

At a first-stage leaf `L`, the units are elements of `O(L)`:

```
u_f = L.canonicalMap f * (L.canonicalMap C.base.s)⁻¹.
```

Wedhorn Step (iii) forms Laurent covers from the ratios

```
u_g * u_h⁻¹
```

inside `O(L)`.

The relative plus piece is therefore the rational piece over `O(L)`:

```
R({u_g * u_h⁻¹}/1).
```

Transporting that rational open back along the equivalence

```
Spa(O(L)) ≃ rationalOpen(L) ⊆ Spa(A)
```

gives

```
{v ∈ rationalOpen(L) | v(g) ≤ v(h)}.
```

This is exactly the desired `RatioNodeData.plus_open_eq`.

The mistake in the blocked proof is trying to define that transported piece directly as

```
denominator = L.s * h,
numerators = {L.s * g} ∪ {t * h | t ∈ L.T}
```

using the original `L.P`. That formula describes the correct valuation locus when `h` is nonvanishing, but its `hopen` proof is not formal consequences of the old pair. The correct source of `hopen` is the **relative rational datum over `O(L)`**, transported to `A` via the relative-localization theorem.

So P3 should be reformulated as:

```
relative ratio Laurent split over O(L)
→ transported absolute RatioNodeData over A.
```

not:

```
denominator-cleared formula over A with old L.P
→ prove hopen directly.
```

## Lean-facing next steps

Replace the current P3 construction target by a transport theorem.

A good theorem shape is schematic:

```lean
theorem relative_ratio_split_transports_to_RatioNodeData
    (L : RationalLocData A)
    (C : RationalCovering A)
    (g h : A)
    (h_unit_base : IsUnit (L.canonicalMap C.base.s))
    (hug : IsUnit (relativeUnitGenerator L C g h_unit_base))
    (huh : IsUnit (relativeUnitGenerator L C h h_unit_base)) :
    ∃ data : RatioNodeData L g h,
      -- optional fields exposing how data.plus/minus came from the relative pieces
      True
```

Internally:

1. Define the relative ratio

   ```
   r := relativeUnitGenerator L C g h_unit_base *
        (relativeUnitGenerator L C h h_unit_base)⁻¹
   ```

   in `presheafValue L`.

2. Build the relative Laurent cover over `O(L)` at `r`:

   ```
   plus_rel  = R({r}/1)
   minus_rel = R({1}/r)
   ```

   or the project's equivalent relative Laurent data.

3. Use the relative rational localization/transitivity theorem, already listed as Group III, to transport `plus_rel` and `minus_rel` to absolute rational data over `A`.

4. Set:

   ```
   data.plus := transported plus_rel
   data.minus := transported minus_rel
   data.cover := derived cover from these two pieces
   ```

5. Prove:

   ```
   data.plus_open_eq :
     rationalOpen data.plus.T data.plus.s =
       {v ∈ rationalOpen L.T L.s | v.vle g h}
   ```

   by the rational-open transport theorem and cancellation of the common denominator `C.base.s`.

6. Prove the symmetric `minus_open_eq`.

With this formulation, `hopen` comes for free from the transported `RationalLocData`; it is not something you prove by manipulating `L.P`.

## Answers

For Q1: Option A is not the right fix. Weakening `plus_open_eq` to an inclusion might be enough for some `Refines` arguments, but it is too weak for the clean transport/inducing story. The equality is the semantic bridge between relative Laurent covers and absolute ratio nodes. Keep the equality and change the construction method.

For Q2: the round-16 architecture remains sound. The only refinement is that `RatioNodeData` should be produced by transporting relative rational data, not by direct denominator-cleared `hopen` construction. This is a local P3 adjustment, not an architecture reset.

For Q3: the density/uniform-inducing/nonarch proof of the bridge lemma is probably the wrong route. If you use the relative Spa equivalence

```
Spa(O(D)) ≃ rationalOpen(D),
```

then a unit in `O(D)` is automatically nonzero at every corresponding valuation. No approximation argument is needed. If that equivalence is not packaged, prove a targeted rational-open transport lemma rather than a general density proof. The field-only `Valued.extensionValuation` API is not the right dependency here.

For Q4: I would not try to enrich a pair of definition of `A` by a completion-side inverse. If the inverse is only in `O(L)`, it is not an element of `A`. The correct object is a relative rational datum over `O(L)`, followed by iterated-rational-localization transport back to `A`. Existing `HasLocLiftPowerBounded`-style machinery may help, but the theorem should be framed as transitivity of rational localizations, not "add `1/h` to `A₀`."

For Q5: pause P3 only long enough to change its statement/proof plan to the relative-transport version. Then continue with the round-16 order. You can work on W3 in parallel if useful, but W3-transport should not be proved using the direct denominator-cleared `hopen` approach.

## Risks or missing facts

The main risk is trying to fill an impossible `hopen` proof for denominator-cleared data over the old pair `L.P`. That proof should not exist in this generality.

A second risk is weakening `RatioNodeData` to inclusions. It may unblock some `Refines` code but will make the inducing and transport proofs less precise. The equality fields are good; the construction method should change.

A third risk is proving `IsUnit(D.canonicalMap(g)) → v(g) ≠ 0` by a long density argument. The conceptual proof is via the Spa equivalence for rational localization: points of `rationalOpen(D)` are points of `Spa(O(D))`, and units have nonzero valuation. If that theorem is not available, add it as a local bridge.

A fourth risk is leaning too hard on `HasLocLiftPowerBounded` in its current ad hoc form. The stable theorem is:

```
relative rational localization over O(L) transports to an absolute iterated rational localization over A.
```

That is the API P3 should consume.

## Manager message

Do not pursue the direct denominator-cleared `hopen` proof for P3. The obstruction is real.

Keep `RatioNodeData.plus_open_eq` and `minus_open_eq` as equalities, but construct the `RatioNodeData` differently:

1. Work over the relative ring `O(L)`.
2. Form the Laurent split at the relative ratio

   ```
   r = u_g * u_h⁻¹
   ```

   where

   ```
   u_f = relativeUnitGenerator L C f h_unit_base.
   ```
3. Transport the relative plus/minus rational data back to absolute `RationalLocData A` using the existing relative presheaf/rational-localization equivalence.
4. Use rational-open transport to prove:

   ```
   rationalOpen data.plus = {v ∈ rationalOpen L | v.vle g h}
   rationalOpen data.minus = {v ∈ rationalOpen L | v.vle h g}
   ```

This avoids the impossible `hopen` goal with the old pair `L.P`.

Also replace the unfinished bridge lemma's density argument by a Spa/rational-open transport argument if possible: a unit in `O(L)` is nonzero at every point of `Spa(O(L))`, hence nonzero on `rationalOpen(L)` under the Spa equivalence.

Proceed with the round-16 order after this local P3 adjustment.
