# Review brief — Tate acyclicity / IsSheafy (round 9: canonical unitCover predicate)

*Prepared 2026-05-15 for ChatGPT Pro (continuing series, follow-up to round 8). Self-contained: no repo access required.*

*Compact follow-up to round 8. The round-8 reviewer flagged that `unitCover` was under-specified — `unitCover.base = L_rel` alone was too weak. Round-9 fixes: added two new predicates `IsCanonicalRelativeBase` and `IsRelativeUnitPieceFor`, plus the strong specification `IsUnitGeneratedCoverFrom` packaging the relative unit-generated cover correspondence. W3 and W3-transport now take these as hypotheses.*

---

## 1. What changed since round 8

| Object | Round-8 issue | Round-9 fix |
|---|---|---|
| `L_rel : RationalLocData (presheafValue L)` | Arbitrary; could be a sub-base of the relative ring | Added `IsCanonicalRelativeBase L L_rel : Prop := L_rel.T = ∅ ∧ L_rel.s = 1` — characterises the canonical "whole-space" relative base. |
| `unitCover : RationalCovering (presheafValue L)` with only `unitCover.base = L_rel` | Far too weak — arbitrary unitCover need not be the unit-generated cover from I_units | Added `IsUnitGeneratedCoverFrom L C s I_units L_rel unitCover : Prop`, requiring (i) canonical base, (ii) bijection between pieces and I_units via `IsRelativeUnitPieceFor`. |
| Transport identification | Implicit in helper clause (d) only | Made explicit: new predicate `IsRelativeUnitPieceFor L C f piece` says the Spv-comap transport of `piece`'s relative rationalOpen equals the absolute restricted unit-piece $\{v \in R(L.T/L.s) : v(f) \le v(C.\mathrm{base}.s)\}$. |
| W3 / W3-transport | Took weak `_h_unitCover_from_I_units : unitCover.base = L_rel` | Now take both `_h_L_rel_canonical : IsCanonicalRelativeBase L L_rel` and `_h_unitCover : IsUnitGeneratedCoverFrom L C s I_units L_rel unitCover`. |

## 2. The new predicates (math + Lean)

### 2.1 `IsCanonicalRelativeBase`

**Mathematical content.** *A relative base $L_{\mathrm{rel}} \in \mathrm{RationalLocData}(\mathcal{O}(L))$ is canonical (= the whole-space base) if its $T$-component is empty and its $s$-component is $1$. Then $\mathrm{rationalOpen}(L_{\mathrm{rel}}.T, L_{\mathrm{rel}}.s) = \mathrm{Spa}(\mathcal{O}(L), \mathcal{O}(L)^+)$ — the whole relative adic space.*

**Lean.**
```lean
def IsCanonicalRelativeBase
    (L : RationalLocData A)
    [typeclasses on presheafValue L]
    (L_rel : RationalLocData (presheafValue L)) : Prop :=
  L_rel.T = ∅ ∧ L_rel.s = 1
```

### 2.2 `IsRelativeUnitPieceFor`

**Mathematical content.** *A relative piece $\mathrm{piece} \in \mathrm{RationalLocData}(\mathcal{O}(L))$ is the relative unit-piece for $f$ if the transport of its rational open via $\mathrm{Spv.comap}\,L.\mathrm{canonicalMap}$ equals the absolute restricted unit-piece at $f$:*

$$\mathrm{Spv.comap}(L.\mathrm{canonicalMap})''\, \mathrm{rationalOpen}(\mathrm{piece}.T, \mathrm{piece}.s) = \{v \in R(L.T/L.s) : v(f) \le v(C.\mathrm{base}.s)\}.$$

**Lean.**
```lean
def IsRelativeUnitPieceFor
    (L : RationalLocData A) (C : RationalCovering A)
    (f : A)
    [typeclasses on presheafValue L]
    (piece : RationalLocData (presheafValue L)) : Prop :=
  Set.image (fun v : Spv (presheafValue L) => comap L.canonicalMap v)
    (rationalOpen piece.T piece.s)
  = {v ∈ rationalOpen L.T L.s | v.vle f C.base.s}
```

### 2.3 `IsUnitGeneratedCoverFrom`

**Mathematical content.** *A relative cover $\mathrm{unitCover}$ at canonical relative base $L_{\mathrm{rel}}$ is the unit-generated cover from $I_{\mathrm{units}}$ if (i) $\mathrm{unitCover}.\mathrm{base} = L_{\mathrm{rel}}$, (ii) each piece of $\mathrm{unitCover}$ is the relative unit-piece for some $f \in I_{\mathrm{units}}$, and (iii) every $f \in I_{\mathrm{units}}$ has a corresponding piece in $\mathrm{unitCover}$.*

The two-way correspondence (ii) + (iii) ensures the bijection between $I_{\mathrm{units}}$ and the pieces of $\mathrm{unitCover}$.

**Lean.**
```lean
def IsUnitGeneratedCoverFrom
    (L : RationalLocData A) (C : RationalCovering A)
    (_s : Aˣ) (I_units : Finset A)
    [typeclasses on presheafValue L]
    (L_rel : RationalLocData (presheafValue L))
    (unitCover : RationalCovering (presheafValue L)) : Prop :=
  unitCover.base = L_rel ∧
  (∀ piece ∈ unitCover.covers, ∃ f ∈ I_units,
    IsRelativeUnitPieceFor L C f piece) ∧
  (∀ f ∈ I_units, ∃ piece ∈ unitCover.covers,
    IsRelativeUnitPieceFor L C f piece)
```

## 3. Updated W3 and W3-transport signatures

### 3.1 W3 (round-9)

```lean
theorem unitGeneratedCover_has_relative_ratioLaurentRefinement
    [project standing hypotheses on A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A) (S : Finset A)
    (_hS_contain : refines_contain C S)
    (s : Aˣ)
    (L : RationalLocData A)
    (_hL_subset : rationalOpen L.T L.s ⊆ rationalOpen C.base.T C.base.s)
    (I_units : Finset A)
    (_h_unit_generated : restricted_standard_cover_generated_by_units L C S s I_units)
    [typeclasses on presheafValue L]
    (L_rel : RationalLocData (presheafValue L))
    (_h_L_rel_canonical : IsCanonicalRelativeBase L L_rel)
    (unitCover : RationalCovering (presheafValue L))
    (_h_unitCover : IsUnitGeneratedCoverFrom L C s I_units L_rel unitCover) :
    ∃ inner_rel : LaurentTree (presheafValue L),
      inner_rel.Refines L_rel unitCover ∧
      inner_rel.allSplitsInducing L_rel
```

### 3.2 W3-transport (round-9)

```lean
theorem relative_laurent_tree_to_absolute
    [project standing hypotheses on A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A) (S : Finset A)
    (_hS_contain : refines_contain C S)
    (s : Aˣ)
    (L : RationalLocData A)
    (_hL_subset : rationalOpen L.T L.s ⊆ rationalOpen C.base.T C.base.s)
    (I_units : Finset A)
    (_h_unit_generated : restricted_standard_cover_generated_by_units L C S s I_units)
    [IsNoetherianRing (locSubring L.P L.T L.s)]
    [typeclasses on presheafValue L]
    -- Round-9 reviewer additions:
    (L_rel : RationalLocData (presheafValue L))
    (_h_L_rel_canonical : IsCanonicalRelativeBase L L_rel)
    (unitCover : RationalCovering (presheafValue L))
    (_h_unitCover : IsUnitGeneratedCoverFrom L C s I_units L_rel unitCover)
    -- The relative inner tree (W3 output):
    (inner_rel : LaurentTree (presheafValue L))
    (_h_refines_rel : inner_rel.Refines L_rel unitCover)
    (_h_split_rel : inner_rel.allSplitsInducing L_rel) :
    ∃ inner_abs : LaurentTree A,
      inner_abs.allSplitsInducing L ∧
      inner_abs.Refines L C
```

## 4. The transport chain (now fully explicit)

The W3-transport descent argument, made explicit per round-8 reviewer:

> `inner_rel` refines `unitCover` at `L_rel`
> $\Rightarrow$ each `unitCover` piece (relative) transports back via `Spv.comap L.canonicalMap` to the absolute restricted unit-piece $\{v \in R(L.T/L.s) : v(f) \le v(C.\mathrm{base}.s)\}$ for some $f \in I_{\mathrm{units}}$
> $\quad$ (by `IsUnitGeneratedCoverFrom` $\to$ `IsRelativeUnitPieceFor`)
> $\Rightarrow$ that absolute restricted unit-piece is contained in $L \cap R(\mathrm{insert}(f, C.\mathrm{base}.T)/C.\mathrm{base}.s)$
> $\quad$ (by `restricted_standard_cover_generated_by_units` clause (d))
> $\Rightarrow$ $R(\mathrm{insert}(f, C.\mathrm{base}.T)/C.\mathrm{base}.s)$ is contained in some $C$-piece
> $\quad$ (by `refines_contain C S`, project-side data from W1)
> $\Rightarrow$ `inner_abs` (transported) refines $C$ at base $L$.

Each arrow has a project-side or round-9-introduced witness; no missing bridges.

## 5. Questions

**Q1.** Is the round-9 `IsUnitGeneratedCoverFrom` predicate now strong enough? Specifically, the two-way correspondence (every piece corresponds to some $f$, every $f$ has a piece) plus the relative-unit-piece identification via `IsRelativeUnitPieceFor` should pin down `unitCover` mathematically. Is anything missing (e.g., bijection-as-function vs. mere existence of correspondences)?

**Q2.** Is `IsRelativeUnitPieceFor`'s formal statement (Spv-comap image equals absolute restricted unit-piece) the right A-level reading of "the relative unit-piece $R(\mathrm{image}_L(s^{-1}f)/1)$ in $\mathrm{Spa}(\mathcal{O}(L))$ transports to the absolute set"? Concretely, the predicate says $\mathrm{Spv.comap}\,L.\mathrm{canonicalMap}'' \,R(\mathrm{piece}) = \{v \in R(L) : v.vle\,f\,C.\mathrm{base}.s\}$. Reviewer noted in round 8: "the relative generator should correspond to $f / C.\mathrm{base}.s$, not merely to $s^{-1} f$". Does the predicate correctly encode this?

**Q3.** Is `IsCanonicalRelativeBase` (with $L_{\mathrm{rel}}.T = \emptyset \land L_{\mathrm{rel}}.s = 1$) the right canonical form? Or should it be something else (e.g., $L_{\mathrm{rel}}$'s rationalOpen equals all of $\mathrm{Spa}(\mathcal{O}(L), \mathcal{O}(L)^+)$, which is equivalent but more semantic)?

**Q4.** With these round-9 predicates in place, is the architecture now correct as a proof target? Or are there further structural issues to address before proof work begins?

## 6. Document metadata

- Project name: Tate acyclicity / IsSheafy (round 9 of the series)
- Brief generated: 2026-05-15 (same day as rounds 6-8)
- Length: ~5 pages
- Build status: `lake build` clean; 6 sorries (W1, W2, W3, W3-transport, I.1's body, V.1 external)
- Round-8 reply integrated; this brief asks whether the round-8 feedback (canonical unit-cover predicate) was correctly applied.
