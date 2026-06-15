# Review brief — Tate acyclicity / IsSheafy (round 10: relativeUnitGenerator + algebraic identification)

*Prepared 2026-05-15 for ChatGPT Pro (continuing series, follow-up to round 9). Self-contained: no repo access required.*

*Compact follow-up to round 9. The round-9 reviewer flagged that `IsUnitGeneratedCoverFrom` pinned down the transported opens but did not expose actual units in `𝒪(L)`. Round-10 fixes: added `relativeUnitGenerator L C f h_unit_base` for the explicit unit `f / C.base.s`, strengthened `IsRelativeUnitPieceFor` with an algebraic identification clause (`piece.T = {u_f}, piece.s = 1`), and added a `IsUnit (u_f)` clause to `IsUnitGeneratedCoverFrom`.*

---

## 1. What changed since round 9

| Object | Round-9 issue | Round-10 fix |
|---|---|---|
| Missing relative generator | `IsUnitGeneratedCoverFrom` exposed only transported opens; W3's ratio-Laurent argument needs actual units | New definition `relativeUnitGenerator L C f h_unit_base := L.canonicalMap f * (L.canonicalMap C.base.s)⁻¹` (using an explicit `IsUnit` witness for `L.canonicalMap C.base.s`). |
| `IsRelativeUnitPieceFor` | Only transport equality | Added algebraic identification clause: `piece.T = {u_f}, piece.s = 1`. |
| `IsUnitGeneratedCoverFrom` | Three clauses (canonical base + two-way correspondence) | Added clause (4): `∀ f ∈ I_units, IsUnit (relativeUnitGenerator L C f h_unit_base)`. |
| W3 / W3-transport | Took `_h_unitCover : IsUnitGeneratedCoverFrom ... L_rel unitCover` | Now also take `h_unit_base : IsUnit (L.canonicalMap C.base.s)` as a parameter. |

## 2. The strengthened predicates (math + Lean)

### 2.1 `relativeUnitGenerator` — explicit generator

**Mathematical content.** *For `f ∈ A`, the relative unit generator $u_f \in \mathcal{O}(L)$ is the element $L.\mathrm{canonicalMap}(f) \cdot (L.\mathrm{canonicalMap}(C.\mathrm{base}.s))^{-1}$ — i.e., the image of $f / C.\mathrm{base}.s$ in $\mathcal{O}(L)$. The inverse exists because $L \subseteq C.\mathrm{base}$ makes $L.\mathrm{canonicalMap}(C.\mathrm{base}.s)$ a unit (taken as a hypothesis).*

**Lean.**
```lean
noncomputable def relativeUnitGenerator
    (L : RationalLocData A) (C : RationalCovering A) (f : A)
    [typeclasses on presheafValue L]
    (h_unit_base : IsUnit (L.canonicalMap C.base.s)) :
    presheafValue L :=
  L.canonicalMap f * ((h_unit_base.unit⁻¹ : (presheafValue L)ˣ) : presheafValue L)
```

### 2.2 `IsRelativeUnitPieceFor` — algebraic + transport

**Mathematical content.** *A piece is the relative unit-piece for `f` if (i) it has the form `R({u_f}/1)` (i.e., `piece.T = {u_f}` and `piece.s = 1`), AND (ii) the transport of its rationalOpen via `Spv.comap L.canonicalMap` equals $\{v \in R(L.T/L.s) : v(f) \le v(C.\mathrm{base}.s)\}$.*

The first clause is what makes the unit-structure visible to W3; the second is the descent identification W3-transport needs.

**Lean.**
```lean
def IsRelativeUnitPieceFor
    (L : RationalLocData A) (C : RationalCovering A)
    (f : A)
    [typeclasses on presheafValue L]
    (h_unit_base : IsUnit (L.canonicalMap C.base.s))
    (piece : RationalLocData (presheafValue L)) : Prop :=
  -- (i) algebraic identification
  piece.T = {relativeUnitGenerator L C f h_unit_base} ∧
  piece.s = 1 ∧
  -- (ii) transport equality
  Set.image (fun v : Spv (presheafValue L) => comap L.canonicalMap v)
    (rationalOpen piece.T piece.s)
  = {v ∈ rationalOpen L.T L.s | v.vle f C.base.s}
```

### 2.3 `IsUnitGeneratedCoverFrom` — with IsUnit clause

**Mathematical content.** *unitCover is the unit-generated cover from I_units if: (1) canonical base, (2) each piece is the relative unit-piece for some f ∈ I_units, (3) every f has a piece, (4) every relative unit generator $u_f$ is actually a unit in $\mathcal{O}(L)$.*

**Lean.**
```lean
def IsUnitGeneratedCoverFrom
    (L : RationalLocData A) (C : RationalCovering A)
    (_s : Aˣ) (I_units : Finset A)
    [typeclasses on presheafValue L]
    (h_unit_base : IsUnit (L.canonicalMap C.base.s))
    (L_rel : RationalLocData (presheafValue L))
    (unitCover : RationalCovering (presheafValue L)) : Prop :=
  unitCover.base = L_rel ∧
  (∀ piece ∈ unitCover.covers, ∃ f ∈ I_units,
    IsRelativeUnitPieceFor L C f h_unit_base piece) ∧
  (∀ f ∈ I_units, ∃ piece ∈ unitCover.covers,
    IsRelativeUnitPieceFor L C f h_unit_base piece) ∧
  -- (4) ROUND-10: actual units
  (∀ f ∈ I_units, IsUnit (relativeUnitGenerator L C f h_unit_base))
```

## 3. Updated W3 and W3-transport (round-10)

### 3.1 W3

```lean
theorem unitGeneratedCover_has_relative_ratioLaurentRefinement
    [project standing hypotheses on A]
    ... [as before] ...
    (I_units : Finset A)
    (_h_unit_generated : restricted_standard_cover_generated_by_units L C S s I_units)
    [typeclasses on presheafValue L]
    -- Round-10: explicit unit witness
    (h_unit_base : IsUnit (L.canonicalMap C.base.s))
    (L_rel : RationalLocData (presheafValue L))
    (_h_L_rel_canonical : IsCanonicalRelativeBase L L_rel)
    (unitCover : RationalCovering (presheafValue L))
    (_h_unitCover :
      IsUnitGeneratedCoverFrom L C s I_units h_unit_base L_rel unitCover) :
    ∃ inner_rel : LaurentTree (presheafValue L),
      inner_rel.Refines L_rel unitCover ∧
      inner_rel.allSplitsInducing L_rel
```

### 3.2 W3-transport

```lean
theorem relative_laurent_tree_to_absolute
    [project standing hypotheses on A]
    ... [as before] ...
    [typeclasses on presheafValue L]
    -- Round-10: explicit unit witness
    (h_unit_base : IsUnit (L.canonicalMap C.base.s))
    (L_rel : RationalLocData (presheafValue L))
    (_h_L_rel_canonical : IsCanonicalRelativeBase L L_rel)
    (unitCover : RationalCovering (presheafValue L))
    (_h_unitCover :
      IsUnitGeneratedCoverFrom L C s I_units h_unit_base L_rel unitCover)
    (inner_rel : LaurentTree (presheafValue L))
    (_h_refines_rel : inner_rel.Refines L_rel unitCover)
    (_h_split_rel : inner_rel.allSplitsInducing L_rel) :
    ∃ inner_abs : LaurentTree A,
      inner_abs.allSplitsInducing L ∧
      inner_abs.Refines L C
```

## 4. Questions

**Q1.** Is the round-10 `IsUnitGeneratedCoverFrom` now strong enough to support W3's ratio-Laurent argument? Specifically:
- Clause (i) of `IsRelativeUnitPieceFor` says each piece is `R({u_f}/1)` algebraically.
- Clause (4) of `IsUnitGeneratedCoverFrom` says each `u_f` is actually a unit.

These together expose the unit structure that Wedhorn Step (iii)'s `u_i · u_j⁻¹` ratio construction depends on. Is the algebraic identification (i) sufficient, or do we additionally need to know `piece` is the *rational locality datum* generated by `u_f` (i.e., satisfies a specific `hopen` condition)?

**Q2.** The unit witness `h_unit_base : IsUnit (L.canonicalMap C.base.s)` is taken as a hypothesis. Should we also add a separate lemma deriving it from `L ⊆ C.base`? Or is it cleaner to leave as a hypothesis at the W3/W3-transport boundary, to be discharged by downstream consumers?

**Q3.** `IsRelativeUnitPieceFor` still uses `Spv.comap` / `Set.image` for the transport equality. The reviewer suggested in round 9 that a `Spa`-level transport lemma might be cleaner. Should we (a) leave the `Spv.comap` form for now (since `rationalOpen` is automatically inside `Spa`), or (b) reformulate at the `Spa` level (with `rationalOpen_transport_eq` as a separate transport lemma)?

**Q4.** With these round-10 strengthenings, is the architecture now finally correct as a proof target for W1, W2, W3, W3-transport? Or are there remaining issues to address?

## 5. Document metadata

- Project name: Tate acyclicity / IsSheafy (round 10 of the series)
- Brief generated: 2026-05-15 (same day as rounds 6–9)
- Length: ~5 pages
- Build status: `lake build` clean; 6 sorries (W1, W2, W3, W3-transport, I.1's body, V.1 external)
- Round-9 reply integrated; this brief asks whether the round-9 feedback (algebraic identification + unit clause) was correctly applied.
