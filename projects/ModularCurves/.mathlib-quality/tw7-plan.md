# T-W7 — constructive group-scheme structure on a LocallyWeierstrass curve (`/develop` plan)

**Planned:** beastmode-A 2026-07-07. **Route:** rigidity lemma (Faltings–Chai I / Mumford
GIT §6.1). **Scope:** full `GrpObj` construction + canonicity.

## Sharp goal

Discharge the single sorry `abelEnrichment_exists` (GroupLaw.lean:74):

```lean
theorem abelEnrichment_exists (G : EllipticCurveGeom S) :
    ∃ E : EllipticCurve S, E.toEllipticCurveGeom = G
```

i.e. **construct `GrpObj (Over.mk G.π)`** (a commutative group-object in the cartesian-monoidal
`Over S`, product = pullback, unit = zero section) for an arbitrary `EllipticCurveGeom` `G` (which
carries `localModel : LocallyWeierstrass G.π G.zero G.zero_π`, T-A8). Everything downstream —
`mulBy`/`mulByHom` ([N]), `pointEquivOverHom`, `pointAddCommGroup`, `baseChange` — is already
derived from the `grp` field via mathlib's `GrpObj` API; T-W7 is the *only* missing piece, and it
is on the critical path (owner directive: only BB-RR may be assumed).

## Infrastructure ledger

| Component | Status |
|---|---|
| `GrpObj`/`MonObj`/`Grp_Class`, cartesian-monoidal `Over S` | mathlib (`CategoryTheory.Monoidal.Grp_`, `ChosenPullbacksAlong.cartesianMonoidalCategoryOver`) |
| affine formulas `addX`/`addY`/`negY`/`slope` + `equation_add`/`nonsingular_add` | mathlib (`EllipticCurve.Affine.Formula`, over `CommRing`/`Field`) |
| `addX_smul`/`addY_smul`/`slope_smul`/`negY_smul` (coordinate-level variableChange-invariance) + `pointEquiv` | **DONE** (`ForMathlib/AffinePointVariableChange.lean`) — gluing data |
| `LocallyWeierstrass` predicate + `baseChange`; `projModel`, `isPullback_projModelBaseChange`, `projModelZero_baseChange` | **DONE** (T-A8/T-A2, WeierstrassModel.lean) |
| **negation morphism** `E → E` over `S` | **GAP** (T-W7.1) |
| **multiplication morphism** `E ×_S E → E` over `S` | **GAP — crux** (T-W7.2) |
| **rigidity lemma** for proper-flat-connected-fibre `S`-schemes | **GAP** (T-W7.4a — the heaviest new AG lemma) |

## Source status (BINDING — source-faithfulness)

- **Explicit formulas / group law over a field**: Silverman, *AEC* III.2 (formulas), III.3
  (the group law; associativity via Riemann–Roch / the divisor-class isomorphism). *Not in
  refs/* — **owed**: obtain Silverman III or use mathlib's `Affine.Point.instAddCommGroup`
  (field-level associativity is already formalised) as the fibrewise substrate.
- **Rigidity lemma / group-scheme axioms over an arbitrary base**: **Faltings–Chai**,
  *Degeneration of Abelian Varieties* I (rigidity), and **Mumford**, *GIT* §6.1 ("Rigidity
  Lemma"). ⚠ **Faltings–Chai is a `.djvu` in refs/ — the Read tool cannot open it.** Before
  T-W7.4 is worked, this source must be made readable (convert to PDF) or replaced by a readable
  equivalent (**Hida GME** ch. 2, or **Katz–Mazur** 2.1 which cites the rigidity argument, both
  PDFs in refs/). A worker MUST NOT start T-W7.4 from memory — the over-a-base associativity is
  exactly where invented-infra risk is highest.
- **Moduli context / group scheme of the universal curve**: Katz–Mazur 2.1–2.3, Hida GME 2.2
  (both readable in refs/).

## Decomposition (rigidity route)

The construction has two halves. **(I)** build the three structure *morphisms* (`neg`, `mul`,
`one=zero`) by gluing the affine formulas across Weierstrass charts using the invariance cocycle.
**(II)** prove the group *axioms* — and here the rigidity lemma does the heavy lifting so we do
**not** re-derive associativity as a giant polynomial identity over a non-reduced base.

### Phase I — structure morphisms

- **T-W7.1 `negHom`** (negation morphism). `negY` is denominator-free, so on the single global
  chart of `projModel` it is already a morphism; `negY_smul` shows it is chart-independent. Over a
  general `LocallyWeierstrass` `G` it glues from the per-chart `negY`. *Tractable — do first.*
  - `def negHom (G) : G.E ⟶ G.E`; `negHom_π : negHom ≫ π = π`; `negHom_zero : zero ≫ negHom = zero`.
- **T-W7.2 `mulHom`** (multiplication morphism `pullback G.π G.π ⟶ G.E`). Internal node; sub-leaves:
  - **T-W7.2a** — on the open `U ⊆ E ×_S E` where both points and their secant sum stay in a
    fixed affine Weierstrass chart, `mul|U` is `Spec`-locally `(addX, addY)` (a morphism, over
    `CommRing`; `equation_add`/`nonsingular_add` show it lands on the curve).
  - **T-W7.2b** — these opens (ranging over charts + the coordinate-changed charts that move a
    point off the degenerate/tangent/at-infinity locus) **cover** `E ×_S E`. Uses that any
    two/three points can be simultaneously moved into the affine locus by a variableChange
    (the atlas group acts transitively enough); `LocallyWeierstrass` gives the charts.
  - **T-W7.2c** — the chart-local `mul`s **agree on overlaps** via `addX_smul`/`addY_smul`/
    `slope_smul` (the invariance cocycle, DONE) → glue to a global `mulHom` (scheme-gluing of
    morphisms, `Scheme.Hom` glueing / `IsOpenImmersion` cover).
  - `def mulHom (G) : pullback G.π G.π ⟶ G.E`; `mulHom_π`.
- **T-W7.3 unit laws.** `mulHom ∘ (zero-on-left) = fst`, `mulHom ∘ (zero-on-right) = snd`
  (identity is the zero section), and `negHom` is a two-sided inverse for `mulHom`. On the affine
  chart these are `addX/addY/negY` identities at `(x,y)=O`; `add_zero`/`add_left_neg`
  mathlib-affine facts + gluing.

### Phase II — axioms via rigidity

- **T-W7.4a `rigidityLemma`** (the heavy new AG lemma). *Statement (Faltings–Chai I / Mumford GIT
  §6.1):* let `p : X → S` be proper, flat, with `p_* O_X = O_S` (geometrically connected fibres)
  and a section `e : S → X`; let `f : X ×_S Y ⟶ Z` be an `S`-morphism with `f ∘ (e ×_S id)`
  factoring through `S` (constant along the `e`-axis). Then `f` factors through the projection
  `X ×_S Y ⟶ Y`. **This is the leaf that most needs the readable source** (proper pushforward of
  `O`, `Stein`-type connectedness). Likely itself an internal node: needs (i) `p_*O_X = O_S`
  for `E/S` (from smooth proper geometrically-connected genus-1 + section — cohomology-and-base-
  change, gated behind BB-COHBC / the coherent-cohomology stream), (ii) the "constant on an axis ⇒
  factors" core. **Flag: (i) may itself be a black box** unless BB-COHBC lands first — re-audit.
- **T-W7.4 `mulHom_assoc`.** With `neg`, `mul`, `zero` in place, `E/S` is a "pre-group"; the two
  associativity morphisms `E×_S E×_S E ⟶ E` agree on every geometric fibre (mathlib affine
  associativity over the residue fields) and, being pointed (both send the triple-zero to zero),
  **rigidity forces them equal** over the whole base — including non-reduced `S`. *This is why the
  rigidity route was chosen: it never re-proves the polynomial identity over `ℤ[ε]`.*
- **T-W7.5 `mulHom_comm`.** `mul ∘ swap` and `mul` are pointed morphisms agreeing on fibres →
  rigidity ⇒ equal (or: any proper group scheme with connected fibres is commutative, Faltings–
  Chai I / the standard corollary of rigidity).
- **T-W7.6 assemble `grpObj` + `abelEnrichment_exists`.** Package `negHom`/`mulHom`/`zero` +
  T-W7.3/.4/.5 as `MonObj` (mul, one, mul_assoc, mul_one, one_mul) + `GrpObj` (inv, laws) +
  `IsCommMonObj`; then `abelEnrichment_exists G := ⟨{ toEllipticCurveGeom := G, grp := grpObj G,
  comm := …, one_eq_zero := … }, rfl⟩`. Mostly plumbing once Phase I/II land.
- **T-W7.7 `abelEnrichment_unique`** (canonicity, T-A6b). Two group structures with the same zero
  section: their "difference/comparison" morphism is pointed → rigidity ⇒ they coincide. Same
  rigidity lemma; independent of the existence tickets.

### Then (was folded into old T-W7; now free from `GrpObj`)

- `[N]`/division polynomials: `mulBy n` is **already derived** from `grp` (`GrpObj.comp_zpow`).
  Division-polynomial *formulas* for `[N]` are a separate optional refinement, not needed to
  retire the T-A6 gate.

## Dependency graph & parallelism

```
DONE: affine cocycle, LocallyWeierstrass, projModel(Zero/BaseChange), universalEllipticCurve
  │
  ├── T-W7.1 negHom ──────────────┐
  ├── T-W7.2 mulHom (2a,2b,2c) ───┤
  │                                ├── T-W7.3 unit/inverse laws
  │                                │
  │        T-W7.4a rigidityLemma ──┼── T-W7.4 assoc ──┐
  │        (⚠ needs readable src;  ├── T-W7.5 comm ───┤
  │         maybe BB-COHBC for     │                   ├── T-W7.6 assemble → abelEnrichment_exists
  │         p_*O = O)              └── T-W7.7 unique (parallel; also needs rigidityLemma)
```
- **Parallel now:** T-W7.1 ∥ T-W7.2 ∥ T-W7.4a (rigidity lemma is independent of the morphisms).
- **Blocking:** T-W7.4/.5/.7 need T-W7.4a; T-W7.6 needs everything.

## Feasibility verdict (honest)

Well-posed **modulo two owed items**: (1) a **readable rigidity source** (Faltings–Chai `.djvu`
→ PDF, or substitute Hida GME / Katz–Mazur) — do this before T-W7.4a; (2) `p_*O_{E} = O_S`
(T-W7.4a item i) may require **coherent-cohomology-and-base-change**, currently the BB-COHBC
stream — if unavailable, T-W7.4a is partially gated and should be re-scoped or that sub-fact
assumed under BB-COHBC. The morphism half (Phase I) is unblocked and rests entirely on DONE
infrastructure (the affine cocycle) — **T-W7.1 and T-W7.2 are ready to work now**.

## Cleanup cadence

New file `EllipticCurve/GroupLawConstruction.lean` (or extend GroupLaw.lean). Proof tickets
T-W7.1, .2, .3, .4, .5, .6, .7 → insert `[CLEANUP-W7-1]` after T-W7.3, `[CLEANUP-W7-2]` (final,
after T-W7.6/.7), and `[CLEANUP-ALL-W7]` before T-W7.6 (milestone: retires the T-A6 gate).
