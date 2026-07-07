# T-W7 — constructive group-scheme structure on a LocallyWeierstrass curve (`/develop` plan)

**Planned:** beastmode-A 2026-07-07. **Scope:** full `GrpObj` construction + canonicity.
**Route (CORRECTED after source check — see §"Source check" below):** *existence* axioms
(assoc/comm/unit/inverse) via **reduction to the universal integral atlas + base change**, NOT
rigidity; rigidity (Mumford GIT §6.1) is used **only** for *canonicity* (uniqueness), and only
there because arbitrary (non-reduced) bases are needed.

## Sharp goal

Discharge the single sorry `abelEnrichment_exists` (GroupLaw.lean:74):

```lean
theorem abelEnrichment_exists (G : EllipticCurveGeom S) :
    ∃ E : EllipticCurve S, E.toEllipticCurveGeom = G
```

i.e. **construct `GrpObj (Over.mk G.π)`** (commutative group-object in cartesian-monoidal `Over S`,
product = pullback, unit = zero section) for an arbitrary `EllipticCurveGeom` `G` (carrying
`localModel : LocallyWeierstrass`, T-A8). Everything downstream — `mulBy`/`mulByHom` ([N]),
`pointEquivOverHom`, `pointAddCommGroup`, `baseChange` — is already derived from the `grp` field via
mathlib's `GrpObj` API. Critical path (owner directive: only BB-RR may be assumed).

## Source check (BINDING — this changed the route)

Read Faltings–Chai I (converted `.djvu`→`refs/ModularCurves/faltings-chai-degeneration.pdf`; OCR
text confirms):

- **FC I.1.1 (def):** "An abelian scheme is a **group scheme** π : A → S which is smooth, proper
  with (geometrically) connected fibres." FC **assumes** the group structure and studies its
  properties — it does **not** construct the group law from a bare genus-1-with-section curve.
- **FC I.1.2(b):** "By the **rigidity lemma of GIT prop. 6.1.**, every abelian scheme is
  commutative." → rigidity gives **commutativity** and (I.2.7) **unique extension of
  homomorphisms**, *given* a group structure.
- **FC I.2.7 (Prop):** extension of a homomorphism from a dense open requires S **noetherian
  normal** — so it does **NOT** cover the arbitrary/non-reduced bases the moduli application needs.

**Consequence (source-drift caught):** rigidity does **not** prove associativity of an
explicitly-constructed `mul`. Associativity is *not* in FC's toolkit for our situation. The
source-faithful route for the *existence* axioms is the **explicit-formula construction** (Silverman
*AEC* III.2–3), with associativity/commutativity obtained by:

> the addition formula's associativity is a **universal identity** — it holds over the *fraction
> field* `K` of the integral universal atlas ring `R = ℤ[a₁..a₆][Δ⁻¹]` (mathlib's
> `Affine.Point.instAddCommGroup` gives `add_assoc`/`add_comm` over any field), and `R ↪ K`
> transfers the rational-function identity back to `R`; the degenerate locus is handled by density
> (`E_U^n` integral over the domain `R`). Then **base change** carries it to every `S` (associativity
> is a morphism identity, and every `EllipticCurveGeom` is *locally* a base change of `E_U`).

Rigidity (GIT §6.1, "constant-on-an-axis ⇒ factors", valid over **arbitrary** bases) re-enters only
for **canonicity** (T-W7.7). ⚠ GIT is not in refs/; its short proof must be reconstructed or found
(KM 2.1 cites it; Hida GME) before T-W7.7 — but T-W7.7 is *separable* from the existence goal.

## Infrastructure ledger

| Component | Status |
|---|---|
| `GrpObj`/`MonObj`, cartesian-monoidal `Over S` | mathlib (`Monoidal.Grp_`, `cartesianMonoidalCategoryOver`) |
| affine formulas `addX`/`addY`/`negY`/`slope` + `equation_add`/`nonsingular_add` | mathlib |
| **field-level group axioms** `Affine.Point.instAddCommGroup` (`add_assoc`, `add_comm`, …) | **mathlib (the substrate for existence via K)** |
| `addX_smul`/`addY_smul`/`slope_smul`/`negY_smul` + `pointEquiv` (variableChange-invariance) | **DONE** (`AffinePointVariableChange.lean`) |
| `LocallyWeierstrass` + `baseChange`; `projModel`, `isPullback_projModelBaseChange`, `projModelZero_baseChange`; `universalEllipticCurve` over the **integral** atlas `R` | **DONE** (T-A8/T-A2/T-W5) |
| atlas ring `R = Localization.Away Δ (MvPolynomial (Fin 5) ℤ)` is a **domain** | provable one-liner (`Localization` of a domain) — key to the K-embedding route |
| **negation / multiplication morphisms** over `S` | **GAP** (T-W7.1 / T-W7.2) |
| **rigidity lemma** over arbitrary base (GIT §6.1) | **GAP — canonicity only** (T-W7.7); source owed |

## Decomposition

### Phase 0 — universal-atlas group law (the load-bearing lemmas; base = integral `R`)

- **T-W7.0a `atlasRing_isDomain`** : `IsDomain WeierstrassAtlasRing`. One-liner
  (`Localization.Away` of the domain `MvPolynomial (Fin 5) ℤ`). **READY NOW.**
- **T-W7.0b — the universal affine addition is associative/commutative over `R`** as a
  rational-function identity, via `R ↪ Frac R` + `Affine.Point.add_assoc`/`add_comm` over `Frac R`.
  This is where mathlib's field-level group law is imported. Statement: the `addX`/`addY` formulas
  on `universalWeierstrassLoc` satisfy the group axioms on the non-degenerate locus.

### Phase I — structure morphisms (glue via the DONE invariance cocycle)

- **T-W7.1 `negHom`** (`G.E ⟶ G.E`, `negHom_π`, `negHom_zero`). `negY` denominator-free ⇒ morphism
  on each `projModel` chart; `negY_smul` glues. **READY NOW — tractable first ticket.**
- **T-W7.2 `mulHom`** (`pullback G.π G.π ⟶ G.E`). Sub-leaves **2a** chart-local `mul=(addX,addY)`
  (`equation_add`/`nonsingular_add` land it on the curve), **2b** charts+coordinate-changed-charts
  cover `E ×_S E`, **2c** overlaps agree via `addX_smul`/`addY_smul`/`slope_smul` (DONE) ⇒ glue.
  For `E_U` (single global Weierstrass chart) this is markedly simpler than for general `E`. **crux.**

### Phase II — group axioms (existence) by reduce-to-universal + base change

- **T-W7.3 unit + inverse laws** (`mul(zero,·)=id`, `mul(·,zero)=id`, `neg` two-sided inverse).
  Affine identities at `O` (`add_zero`, `add_left_neg`) transported; over `R` via Phase 0.
- **T-W7.4 `mulHom_assoc`** — associativity **as a morphism identity, over any `S`**. Proof: holds
  over the universal atlas `E_U` (Phase 0: `R↪K` + fibre density on integral `E_U³`), then **base
  change** — every `EllipticCurveGeom` is *locally* `E_U ×_U (classifying map)`, so `mulHom` is
  locally a base change of `E_U`'s associative `mulHom`; associativity is a morphism identity
  checkable on the open cover. **No rigidity, no ℤ[ε] polynomial identity.**
- **T-W7.5 `mulHom_comm`** — same reduce-to-universal route (`add_comm` over `K` + density +
  base change). (Rigidity would also give it, but reduce-to-universal avoids the GIT dependency.)
- **T-W7.6 assemble `grpObj` + `abelEnrichment_exists`** (MILESTONE — retires T-A6 EXISTENCE).
  Package `neg`/`mul`/`zero` + T-W7.3/.4/.5 as `MonObj`+`GrpObj`+`IsCommMonObj`; then
  `abelEnrichment_exists G := ⟨{ …, grp := grpObj G, … }, rfl⟩`. Plumbing.

### Phase III — canonicity (separable; the ONE genuine rigidity use)

- **T-W7.7a `rigidityLemma`** (GIT §6.1): for `p : X ⟶ S` proper flat with `p_*O_X = O_S`
  (geom. connected fibres) + section, `f : X ×_S Y ⟶ Z` constant along the `e`-axis ⇒ factors
  through `Y`. **Source owed** (GIT not in refs; reconstruct short proof or use KM 2.1/Hida GME).
  Sub-fact `p_*O_E = O_S` may need coherent-cohomology-&-base-change (**BB-COHBC**) — re-audit.
- **T-W7.7 `abelEnrichment_unique`** (T-A6b). Two group structures with the same zero section:
  `id : (E,m) → (E,m')` is a pointed morphism ⇒ homomorphism (T-W7.7a) ⇒ `m = m'`. Works over
  **arbitrary** `S` (rigidity needs no normality — unlike FC 2.7). **Deferrable** past the
  existence milestone.

## Dependency graph & parallelism

```
DONE: affine cocycle, LocallyWeierstrass, projModel(Zero/BaseChange), universalEllipticCurve
  │
  ├── T-W7.0a atlasRing_isDomain (1-liner) ──┐
  │                                          ├── T-W7.0b universal-atlas add group law
  ├── T-W7.1 negHom ─────────────────────────┤       │
  ├── T-W7.2 mulHom (2a/2b/2c) ──────────────┤       │
  │                                          ├── T-W7.3 unit/inverse
  │                                          ├── T-W7.4 assoc (uses 0b + base change)
  │                                          ├── T-W7.5 comm  (uses 0b + base change)
  │                                          └── T-W7.6 assemble → abelEnrichment_exists  [MILESTONE]
  │
  └── T-W7.7a rigidity (GIT §6.1; src OWED) ── T-W7.7 canonicity  [Phase III, separable/deferrable]
```
- **Parallel now:** T-W7.0a, T-W7.1, T-W7.2 (all on DONE infra).
- **Existence milestone (T-W7.6) does NOT depend on rigidity** — the big de-risk from the source check.

## Feasibility verdict (post source-check)

- **Existence (T-W7.0–.6)** is **well-grounded on DONE infrastructure**: the atlas is an integral
  domain, mathlib supplies the field-level group axioms, T-W5 gives `universalEllipticCurve`, and the
  affine cocycle gives the gluing. No deep rigidity theory, no non-reduced-base polynomial identity.
  The crux remains **T-W7.2** (building `mulHom` as a scheme morphism from the charts) — real
  scheme-gluing work, but on solid inputs. **T-W7.0a/.1 are one-to-few-liners; start there.**
- **Canonicity (T-W7.7)** genuinely needs the **GIT §6.1 rigidity lemma over arbitrary bases**
  (FC 2.7 is normal-base-only). Source owed; `p_*O_E = O_S` may pull in BB-COHBC. **Separable** —
  the existence gate can be retired first.

## Cleanup cadence

New file `EllipticCurve/GroupLawConstruction.lean`. `[CLEANUP-W7-1]` after T-W7.3;
`[CLEANUP-ALL-W7]` before T-W7.6 (milestone); `[CLEANUP-W7-2]` final after T-W7.6; T-W7.7 (Phase III)
gets its own final cleanup when it lands.
