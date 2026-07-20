# Development Plan: Modular curves as arithmetic moduli (Katz–Mazur)

*/develop Phase 1, 2026-07-05, branch `dev/modular-curves`, worktree `../aintlib-modular-curves`.*
*Design decisions confirmed with the project owner (C. Birkbeck) on 2026-07-05; reviewer round pending (`/expert-review`).*

## Goal

Formalise the theory of modular curves **as representing objects of moduli problems of
elliptic curves**, in the Katz–Mazur framework:

1. **Elliptic curves over an arbitrary base scheme** (definition, group law, `[N]`,
   torsion subgroup schemes) — a prerequisite project in its own right, layered so it can
   later stand alone.
2. **The Weil pairing** `e_N : E[N] × E[N] → μ_N` over a base.
3. **Drinfeld level structures** (KM Ch. 1: relative Cartier divisors, full sets of
   sections, points of exact order `N`) — the definitions of record over any base; the
   naive fibrewise notions recovered as *theorems* when `N` is invertible.
4. **Moduli problems** (KM Ch. 4 / Loeffler §3.7): the category `Ell/R`, relative
   representability, rigidity, and `representable ⟺ relatively representable + rigid`;
   the honest **stack-facing statements** (fppf descent of elliptic curves) alongside.
5. **Representability where true**: Tate normal form and the universal `(E,P)` with `P`
   nowhere of order ≤ 3 (Loeffler §3.3, provable *now* at ring level); `Y₁(N)` for
   `N ≥ 4` and `Y(N)` for `N ≥ 3`, smooth affine over `ℤ[1/N]`.
6. **Endgame** (Buzzard, *Formalizing Fermat* L8 p. 33): the twisted curve `Y(ρ̄_N)/ℚ`
   representing elliptic curves with `E[N] ≅ ρ` as representations-with-pairing — smooth,
   affine, geometrically irreducible (irreducibility black-boxed, "see 1980s").

Headline Lean statements (all present, `sorry`d, in the skeleton — see file structure):
`EllipticCurve` (def), `Section.HasExactOrder` (def, KM 1.4.1),
`ModuliProblem.representable_iff` (KM 4.7), `gammaOneNaive_representable` (Y₁(N)),
`gammaFullNaive_representable` (Y(N)), `yRho_representable` (Y(ρ,p)).

## Confirmed design decisions

| # | Decision | Choice |
|---|----------|--------|
| D1 | Placement of EC-over-schemes | Same project/branch, **strictly layered** `ModularCurves/EllipticCurve/*` + `GroupScheme/*` with no imports from the moduli layer; extractable later by a folder move |
| D2 | Base generality | **KM definitions over arbitrary base from day 1** (Drinfeld structures are the definitions of record); theorem waves sequenced `N`-invertible first; KM Ch. 5–7 (char `p` \| `N` regularity, crossings) are later phases — statements never weakened |
| D3 | Stack packaging | **KM formalism (`Ell/R` + presheaves) as the engine** + stack bridge: fppf-descent statements now (`Moduli/Stack.lean`), `Pseudofunctor.IsStack` packaging as ticket `T-E8` |
| D4 | Reviewer | Senior arithmetic geometer, full-detail brief |
| D5 | Group law (expert review Q1/Q3, 2026-07-05) | **Bundled in the working record**: `EllipticCurve extends EllipticCurveGeom` with `grp`/`comm`/`one_eq_zero` fields; Abel/Pic⁰ becomes the deferred canonicity ("purity/comparison") project with seven named black boxes; **DS2 deleted** |
| D6 | Moduli values (review Q7) | **Groupoid-valued internally** (`Moduli/Groupoid.lean`); set-valued only after rigidification (bridge: `aut_trivial_of_fullLevel`) — small-`N`/`Γ₀`/level-1 statements must use the groupoid layer |
| D7 | Weil pairing (review Q5/Q6) | Final API via **Cartier duality/autoduality**; KM 2.8 norm/divisor as comparison backend; char-0 étale-descent construction acceptable first milestone with the same API. **Normalisation: Silverman convention** (`σζ = ζ^χ`, `det ρ_E = χ`), pinned by the symplectic formula + Galois equivariance + `N ∣ M` compatibility |
| D8 | Y(ρ̄) route (review Q9) | **Direct symplectic-Isom construction** (`Isom^symp(E[N], V_ρ̄)`, T-F6) carries the moduli interpretation by construction; Galois-twist identification is a separate later theorem |

## Faithfulness constraints (binding, from the project owner)

- State definitions and lemmas in Lean with `sorry` wherever possible; where genuinely
  not expressible yet, the **precise mathematical statement lives in the docstring** and
  an API-gap ticket exists. No target drift; no weakening by extra hypotheses; no junk
  structures that bundle the hard content without a discharge obligation.
- KM may use stacks without saying so — every such point is surfaced explicitly (the
  `Ell/R`-is-a-stack remark, coarse vs fine at `Γ₀(N)`, quotient steps in KM 4.7 ⇐).
- Mazur (`X₀(N)/ℤ`, stacky at char \| N) and the Shimura-surface material are **black
  boxes for consumers** — nothing here may quietly depend on them.

## The DATA-SORRY REGISTER (the audited surface of unconstructed data)

Every `sorry` at *definition* (data) level is listed here; each has (i) its precise
mathematical definition in its docstring, (ii) a construction ticket, (iii)
specification theorems pinning it down — **which must include base-change/naturality
and functoriality, not only fibrewise comparison** (expert review Q4: fibrewise
agreement does not pin morphisms over non-reduced bases), (iv) a rule: **downstream
code may use it only through its stated specifications**. Anything not on this list
must be `theorem`-level `sorry` only. (Verified by the cleanup checkpoints.)

*2026-07-05: DS2 (group law) deleted — the group structure is now a field of the
working record `EllipticCurve` (design D5); `pointEquivOverHom`, `pointAddCommGroup`
and the base-change group structure are real (sorry-free) definitions.*

| ID | Declaration | File | Construction ticket | Pinned down by |
|----|-------------|------|---------------------|----------------|
| DS1 | ~~`projModel`, `projModelπ`, `projModelZero`~~ **CONSTRUCTED 2026-07-06** (Proj of the quotient grading, `ForMathlib/GradedQuotient.lean`; `zero ≫ π = 𝟙` proved) | EllipticCurve/WeierstrassModel.lean | T-A2 remaining: spec theorem only | `IsWeierstrassModel` + uniqueness T-A4 |
| DS3 | ~~`muNGrpObj`, `constZModGrpObj`, `muNPointsEquiv`~~ **CONSTRUCTED 2026-07-06 (T-B2)** — by representability (`GrpObj.ofRepresentableBy`) from the points presheaves; pins proved: `muNPointsEquiv` + `_natural`/`_one`/`_mul`, `constSchemePointsEquiv` + `_natural` | GroupScheme/MuN.lean | T-B2 done; rank/étale specs remain T-B7 | `muNπ_isFinite`, `muNπ_flat`/`_finrank`, `muNπ_etale_iff` (T-B7, sorried) |
| DS4 | `weilPairing` | WeilPairing/Basic.lean | T-C1 (duality API; KM 2.8 backend; char-0 étale version first = T-C0) | `weilPairing_over`; bilinear/alternating/nondegenerate (T-C2/3); **base-change naturality (T-C2a); `N∣M` compatibility (T-C2b); symplectic pin (T-C2c, Silverman convention)**; fibre comparison T-C4 |
| DS4a | `RelEffCartierDiv.sectionsDivisor` | LevelStructure/CartierDivisor.lean | T-D3 (ideal products) | `sectionsDivisor_degree`, base-change spec |
| DS5 | `vRho`, `vRhoπ`, `vRhoPointsEquiv` | ModularCurve/YRho.lean | T-F1 (Galois descent of constant gp scheme) | `vRhoπ_finite_etale`; **pinned by the finite-étale/Galois equivalence (review Q4), not merely geometric points** — equivalence spec is T-F1's gate |
| DS5d | `PairingCompatAt` (relation) | ModularCurve/YRho.lean | T-F3 (unfold via Γ–Spec iso) | consumed only by `RhoLevelStructure.pairing_compat` |

`torsionIdeal` (LevelStructure/Basic.lean) is DS-adjacent: discharged by T-B3a from
`torsionι_isClosedImmersion`.

**DS-W7 block (added 2026-07-07T14:05Z per coordinator §3 — the decompose-skeleton carve-out).**
The T-W7 `/develop --decompose` skeleton (commit `ba82784b`) deliberately states its
construction *defs* with `sorry` bodies; they are governed by the SAME four-point DS rule
above, with (ii) = their board tickets and (iii) = the skeleton's own spec lemmas (each def is
followed in-file by its `_π`/`_left`/`_specPoints`/restriction pins — consumers may use ONLY
those). Register (construction ticket in parentheses):

| DS-W7 defs | File | Ticket |
|---|---|---|
| `blOpenZ`, `blOpenY`, `addOnZ`, `addOnY` | EllipticCurve/GroupLawConstruction.lean | T-W7.0c-i |
| `mulModelHom` | 〃 | T-W7.0c-ii |
| `mulOver`, `oneOver`, `invOver` | 〃 | T-W7.0g |
| `negModelHom` | 〃 | T-W7.0b |
| `projModelVCIso` | EllipticCurve/ModelVariableChange.lean | T-W7.mvc |
| `projModelPointsEquiv` | EllipticCurve/PointsDictionary.lean | T-W7.0f (+ §2-P2 value-lemmas) |
| `EllipticCurveGeom.negHom`, `.mulHom`, `.grpObj` | EllipticCurve/GroupLawDescent.lean | T-W7.12 / T-W7.36 |

**DS-END0 block (added 2026-07-08, coordinator — repairing the same-commit rule for the
T-END0 skeleton 745cd328):**

| DS-END0 defs | File | Ticket |
|---|---|---|
| `endDeg`, `endDual`, `endTrace` | EllipticCurve/EndomorphismDegree.lean | T-END0b (deg/dual) / T-END0d (trace) |

Pins (consumers may use ONLY these): `endDual_comp_self` (KM 2.6.1), `endDeg_mulBy`
(KM 2.6.1.1), `endDual_mulBy` (KM 2.6.2.1), `endTrace_spec` (KM 2.6.2.2). Discharge route:
Abel/Pic⁰ autoduality — a LIVE dependency on fable-PIC0's T-PIC0+COH-1 stream (tickets.md
§v10.11) — + the HasseWeil anchors in decomposition-end0.md.

**DS-GH1 + DS-NISOG block (added 2026-07-08, coordinator, same commit as the v10.37
skeletons):**

| DS defs | File | Ticket |
|---|---|---|
| DS-GH1: `gammaHAut` (+ spec) | Moduli/GammaHRepresentability.lean | STREAM-GH P0 (GH1) |
| DS-NISOG-1: `quotientCurve` · DS-NISOG-2: `quotientHom` | GroupScheme/NIsogeny.lean | STREAM-NISOG L6 (constructions cite [T-G3D-INFRA]) |

Pins shipped in the skeletons (incl. `pointMap_eq_zero_iff` = Ker π = G); base-change pins
recorded as construction-ticket obligations. Consumers use pins only, per the standing rule.

Rule for future decompose passes: skeleton `def := sorry` decls MUST be added to this
register in the same commit that creates them.

**DS-OMEGA block (added 2026-07-13, STREAM-OMEGA, same commit as the T-E-OMEGA R1
skeletons; decomposition: decomposition-omega-r1.md):**

| DS-OMEGA defs | File | Ticket |
|---|---|---|
| `UnitCocycle.{sectionsMap, presheafAb, presheafOfModules, lineBundle, lineBundleSectionsEquiv, trivSection, sectionsEquivOfLE, Compat.sectionsEquiv, pullbackCocycle, sectionsPullback}` | ForMathlib/UnitCocycleSheaf.lean | T-OM-A2/A3/A4/A7 |
| `LocalPresentation.transport` (e/compat fields) | EllipticCurve/InvariantDifferential.lean | T-OM-B3 |
| `omegaCocycle` (u field) | EllipticCurve/InvariantDifferential.lean | T-OM-B5 |
| `omegaCompat`, `omegaBasisMap` | Moduli/OmegaFunctor.lean | T-OM-B7 |

Pins (consumers may use ONLY these): `omegaModules` + `omegaModules_isInvertible` (ω2 ★),
`OmegaBasis` + its `Γ(S,⊤)ˣ`-`SMul` + `OmegaBasis.existsUnique_unit_smul` (ω3 torsor),
`omegaBasisMap` + `_id`/`_comp`/`_smul` (ω4, T-E14 statability), `omegaCocycle_res`
(chart-transition spec), `negVC_u` (ω5 `{±1}`). Discharge route: comparison-theorem
uniqueness (1b + `projModelVCIso_{one,mul,map,injective}`) + `Scheme.exists_unit_glue`;
NO new axioms, target = sorry-free within the T-E-OMEGA stream (same marathon).

**DS-OMEGA DISCHARGED (2026-07-13, same marathon, ★★).** Every def-sorry in the table
above is proven; all three files are sorry-free and every pin above is axiom-verified
(standard 3). The register block is retained as the pin list (consumer contract) only —
no open data-sorries remain in the T-E-OMEGA stream.

## The BLACK-BOX REGISTER — **RR-ONLY** (owner directive, 2026-07-05)

**Standing black box (the only one):**

| ID | Statement | Source | Where stated / used |
|----|-----------|--------|---------------------|
| BB-RR | **:= GME 2.1.2 (Grothendieck–Serre duality for relative curves) + 2.1.3 (RR) + 2.1.6 (relative RR) — exactly these, nothing else enters the box** | GME §2.1 (full text in refs); Silverman III.3.1 fibrewise | A6.α, A7.b (fibre vanishing + rank counts); T-A4 |

**De-black-boxed (owner, 2026-07-05: "the only black box should be Riemann–Roch;
the others we should plan to do, in parallel if possible")** — each former box is now
a **planned workstream**; its sorried Lean statement stays exactly where it is, but as
the headline *target* of the stream, not a standing assumption. Survey agents are
checking mathlib PRs, external Lean repos (incl. the FLT project), and AINTLIB itself
for existing work before the detailed tickets are cut; scoping tickets exist now:

| Stream | Was | Target statement(s) | First tickets | Feeds |
|--------|-----|--------------------|---------------|-------|
| **COH** | BB-COHBC | COH-1 = GME Lemma 1.10.4 (cohomology & base change); COH-2 = GME Cor 1.9.12 (`Γ(E,O)=Γ(S,O)`); COH-3 = `R^i f_*` + affine vanishing + LES (mathlib lane #36345/#36218 — coordinate, don't build); + T-PIC0 (Pic of a scheme, unclaimed) | T-COH0 scoping done via survey; sources pinned in decomposition-gme2.md | Abel canonicity (A6 chain); A7 ranks; relative Picard |
| **FLAT** | BB-FLAT | Fibrewise flatness criterion (EGA IV 11.3.10): `X → Y` over `S`, `X` `S`-flat + fibrewise flat ⇒ flat; and the local criterion of flatness | T-FLAT0 scoping (mathlib `RingTheory.Flat` state + survey); T-FLAT1 Lean statement (needs fibre-morphism helper) | T-B4 (`E[N]` rank `N²`) |
| **OT** | BB-DELIGNE | A finite locally free commutative group scheme of rank `N` is killed by `N` (Deligne's norm argument) | T-OT0 scoping after T-SG1 (needs the flf-group-scheme vocabulary); norm machinery: `Algebra.norm` + FltRegular's norm lemmas (rescan running) | T-D5 (exact order ⟹ killed) |
| **DESC** | BB-DESC | torsor descent of levelled curves (`levelledCurve_descent_of_torsor`, `Moduli/Stack.lean` — DEF-2 form; the cocycle-free fppf statement was false and is deleted) + fppf-covers-are-epis (subcanonicity, consumed by T-E11) | T-DESC0 scoping: mathlib `Morphisms/Descent`, `FlatDescent` coverage (survey); route: descend via relatively ample `ω`/ideal-at-zero embedding ⟶ module descent (in mathlib) + Proj | T-E10/T-E8; T-E9 route |
| **IRR** | BB-IRR | Geometric connectedness/irreducibility of `Y(N)`, `Y(ρ̄)` (`yRho_geometricallyIrreducible` — statement in `YRho.lean`) | T-IRR0 scoping: algebraic route via KM Ch. 10 (components via `T[N]`, Tate-curve/cusp degeneration — ⧗KM) vs analytic route (uniformisation, hooks LeanModularForms). Buzzard sanctioned sorrying this ("see 1980s"); owner directs planning it anyway — late-phase, parallel | T-F5 |

Rule: BB-RR may be *used* only via its stated Lean theorems. The five streams'
target statements may likewise be used downstream while open (they are ordinary
sorried theorems), but every use is a dependency edge on the corresponding stream,
tracked on the board — not an assumption that may quietly become permanent.

## Mathlib inventory (survey 2026-07-05, pin 11b908e5cdd9)

| Concept | Mathlib status | Our action |
|---|---|---|
| Weierstrass curves over rings, `Δ`, `j`, `IsElliptic`, `VariableChange`, division polys `Ψ` | `Mathlib.AlgebraicGeometry.EllipticCurve.*` | USE throughout (ring level) |
| Group law on points | over fields only (`Affine.Point`) | USE on fibres; scheme-level is DS2 |
| Morphism classes: `Smooth`, `SmoothOfRelativeDimension`, `IsProper`, `IsFinite`, `Flat`, `IsEtale?`, `LocallyOfFinitePresentation`, `Surjective`, `finrank` | mature (`Morphisms/*`, `FlatRank`) | USE (they carry the definition) |
| ZMT, fibres `Scheme.Hom.fiber`, residue fields, valuative criteria | present | USE |
| Group objects: `GrpObj` in `Over S`, Cartesian monoidal `Over` | present, thin | USE as the group-scheme language |
| Sites: zariski, étale, fppf/fpqc precoverages; `Precoverage.toGrothendieck`; `Pseudofunctor.IsStack` | present | USE for the stack bridge |
| Fibred categories, descent of module/algebra props | present (abstract) | USE later (T-E8) |
| **Absent**: EC over schemes, Weil pairing (any), level structures, moduli, μ_n scheme, Cartier duality, eff. Cartier divisors, coherent cohomology/genus/RR, Pic(scheme), quotients by finite groups, torsors, algebraic spaces/stacks | — | WE DEFINE (this project) or API-gap |

API gaps (each gets its own sub-development before dependent tickets):
**AG-LB** invertible ideal sheaves / line bundles (blocks official Cartier def, T-D1) ·
**AG-COH** coherent cohomology & genus (blocks `fibre_condition_iff_genus_one`, T-A9) ·
**AG-CD** Cartier duality vocabulary (blocks perfectness T-C3 full form) ·
**AG-QUOT** quotients of schemes by finite groups (blocks KM 4.7 ⇐, Y₀(N); Loeffler 3.6.1) ·
**AG-GG** Grothendieck–Galois for finite étale ℚ-schemes (DS5 discharge).

## In-repo reuse (AINTLIB — import, never re-prove)

- `HasseWeil`: field-level Weil pairing + nondegeneracy + symplectic scaling
  (`HasseBound/WeilPairing/*`), `E[N] ≅ (ℤ/N)²` alg. closed (`NTorsion/TorsionGeneralN`),
  Tate modules, dual isogenies, formal groups. → fibre comparisons (T-C4, T-B6).
  ⚠ `Isogeny/Kernel.lean`: Silverman III.4.10 explicitly deferred there — do not assume.
- `NagellLutz/Universal.lean`: universal Weierstrass curve over `ℤ[A₁..A₆]` +
  `specialize` — reuse for elementary universal families. Division polynomials: use
  **mathlib's** (NagellLutz's are a fork; do not fork again).
- `LeanModularForms`: congruence subgroups + nebentypus bookkeeping (the group-theoretic
  shadow); the analytic `Y(Γ)(ℂ) = Γ\ℍ` comparison lives there eventually (T-G*, phase 3).

## File structure (skeleton, all compiling with sorries)

```
projects/ModularCurves/ModularCurves/
├─ EllipticCurve/WeierstrassModel.lean   WS-A  projModel interface (DS1) + uniqueness
├─ EllipticCurve/Basic.lean              WS-A  THE definition; Point functor; baseChange
├─ EllipticCurve/GroupLaw.lean           WS-A  DS2 group structure + specs; mulBy
├─ EllipticCurve/Torsion.lean            WS-B  E[N]; finite loc. free rank N²; étale
├─ GroupScheme/MuN.lean                  WS-B  μ_N, (ℤ/N)_S, DS3 + points spec
├─ LevelStructure/CartierDivisor.lean    WS-D  rel. eff. Cartier divisors; full sets of sections
├─ LevelStructure/ExactOrder.lean        WS-D  KM 1.4: exact order N; 1.4.4 equivalences
├─ LevelStructure/Basic.lean             WS-D  Γ(N)/Γ₁(N)/Γ₀(N), naive ⟺ Drinfeld
├─ WeilPairing/Basic.lean                WS-C  DS4 pairing + bilinear/alt/nondeg specs
├─ Moduli/EllCategory.lean               WS-E  Ell/R; moduli problems; KM 4.7 statement
├─ Moduli/Representability.lean          WS-E  Tate normal form (provable now!); Y₁(N); Y(N)
├─ Moduli/Stack.lean                     WS-E  fppf descent statements (stack bridge)
├─ Moduli/Groupoid.lean                  WS-G  groupoid of elliptic curves; rigidification
├─ Moduli/GammaH.lean                    WS-H  P_H for H ≤ GL₂(ℤ/N); Drinfeld problems over ℤ;
│                                              not-rigid at N ≤ 2; levelled groupoid
├─ Moduli/Coarse.lean                    WS-M  coarse j-line; coarse Y_{P_H} (Y₀(N), small N)
└─ ModularCurve/YRho.lean                WS-F  GaloisRepData; V_ρ (DS5); Y(ρ̄_N); Isom^symp
```

## Workstreams & parallelism

Six lanes; A→(B,C,D) fan-out; E consumes A/B/D interfaces (not proofs); F consumes
B/C/E statements. **Lanes B, C, D, E can run in parallel immediately after the A-layer
interfaces freeze** (they already have: the skeleton compiles). Within lanes, tickets
marked `Parallel: yes` are independent.

- **WS-A** foundations: projModel construction; base-change props; Abel (DS2 chain);
  locally-Weierstrass (BB-RR consumers).
- **WS-B** torsion & group schemes: μ_N/const wiring (T-B2); E[N] closed immersion,
  finite flat rank N² (BB-FLAT), étale when invertible; fibre comparison to HasseWeil.
- **WS-C** Weil pairing: KM 2.8 construction (needs full KM text); specs; fibre
  comparison + normalisation pin (T-C4).
- **WS-D** ★ Drinfeld structures: divisor sums (T-D3); full-sections globalisation (T-D2/4);
  KM 1.4.4 equivalences (T-D6/7); naive ⟺ Drinfeld for Γ(N), Γ₁(N) (T-D8/9).
  **★ CLAIMED: beastmode-D, 2026-07-06T09:25Z** — work order on the ticket board
  (§Amendments v5); binding proof plans in `decomposition-km1.md`.
- **WS-E** moduli: Ell/R plumbing sorries; **T-E1/T-E2 (Tate normal form — provable
  now, start here)**; KM 4.7 (needs AG-QUOT); Y₁(N), Y(N); fppf statements; T-E8 stack
  packaging.
- **WS-F** Y(ρ,p): DS5 construction (AG-GG); T-F3 scheme-level compat; T-F4
  representability; BB-IRR.

## Phasing

- **Phase 1 (now)**: skeleton green; T-E1/T-E2 proved; T-A2 projModel; T-B2 μ_N wiring;
  divisor sums T-D3. *Gate: full KM PDF acquired for Ch. 2–4 quote-fidelity.*
- **Phase 2**: KM 1.4.4 equivalences; E[N] theorems; Weil pairing construction; KM 4.7
  via AG-QUOT; Y₁(N)/Y(N) representability over ℤ[1/N].
- **Phase 3**: Y(ρ,p); analytic comparison with LeanModularForms; coarse `Y₀(N)`.
- **Phase 4 (KM over ℤ)**: Ch. 5 regularity, Ch. 6 cyclicity, Ch. 7 quotients, Ch. 8
  compactification (needs Faltings–Chai as PDF for degenerations if pursued to X(N)/ℤ).

## Cleanup cadence (binding; also the maxHeartbeats rule)

Per `/develop` §1g: `[CLEANUP-n]` after every 3rd proof/def ticket per file; final
per-file cleanup; `[CLEANUP-ALL-n]` before each milestone (T-E2, T-E7, T-E9, T-F4);
`[CLEANUP-FINAL]` last. **Every cleanup ticket explicitly includes: remove every
`set_option maxHeartbeats` (a proof needing one is a proof needing decomposition —
file a `/decompose-proof` ticket instead); re-verify the DATA-SORRY register (no new
data-sorries outside it); `#print axioms` on the file's theorems (only
`propext`/`Classical.choice`/`Quot.sound` + the registered `sorryAx` while WIP).**
**v10.24 extension (owner, 2026-07-08): slowdown ⟹ decompose** — a crawling proof is split
into private helpers immediately; a heavy (chart-iso-scale) definition ships its opaque
interface (`_apply`/injectivity/cancellation + `irreducible`) in the same increment;
consumers never touch raw terms. (Retro-fit precedent: tickets.md [T-W7.1b-faith-infra].)

## Constraints & risks

- ~~Full Katz–Mazur text is not yet in `refs/`~~ **RESOLVED 2026-07-08** — the full KM text
  is in `refs/ModularCurves/katz-mazur-arithmetic-moduli-FULL.pdf` (gate lifted, 90ed0986).
  The standing order to re-run `/develop --decompose` on WS-C and WS-E's KM-sourced subtrees
  is now DUE and dispatched: **[T-C1-KM28]** + **[T-E5-KM47]** (tickets.md §Amendments v10).
- Faltings–Chai is `.djvu` (unreadable by tooling); only needed in Phase 4.
- Mathlib's `GrpObj`/`Over` monoidal API is young; if `mulBy`-style definitions fight
  elaboration, the fallback (recorded, faithful) is explicit structure-morphisms — a
  mechanical refactor, not a mathematical change.
- `sorry`s are allowed on `main` as WIP markers, but fleet workers must not touch files
  whose results still carry them (AINTLIB rule); the register keeps that boundary sharp.


## Expert-review amendments (2026-07-05) — APPLIED

Reply archived at `expert-review/2026-07-05/reply.md`; integration record at
`…/integration.md`. Summary of applied changes:

1. **Cartier-incidence representability block** (`LevelStructure/Incidence.lean`, new):
   zero locus of a section of a finite locally free module; divisor base change (real,
   via `Scheme.Hom.ker` of the pulled-back closed immersion); `IsSubdivisor`;
   `exists_incidenceLocusLE/EQ` (KM 1.3.4/1.3.5, verbatim source in hand);
   `exists_subgroupLocus` (KM 1.3.7, `1 + deg + deg²` equations, verbatim + proof in
   hand); `exists_exactOrderLocus` / `exists_fullLevelLocus` (KM 1.5–1.6 instances).
   Tickets T-D11–T-D21; general-`A` statement is T-D21.
2. **Two-record design** (D5): `EllipticCurveGeom` (geometry) + `EllipticCurve`
   (with `grp`, `comm`, `one_eq_zero`). Abel/Pic⁰ → deferred canonicity project
   (`abelEnrichment_exists/unique`) with the reviewer's seven named boxes. Torsion and
   level structures no longer wait on Pic⁰.
3. **Fibre condition** restated as a pointed **scheme isomorphism** with `projModel`
   (review Q2), not a functor-of-points identification; geometric-genus form remains
   the eventual statement of record (AG-COH, T-A9).
4. **Groupoid layer** (`Moduli/Groupoid.lean`): category (→ groupoid, T-G1) of
   elliptic curves over `S`; `IsoClasses`; rigidification bridge
   `aut_trivial_of_fullLevel` (T-G3). Policy: small-level statements go through this
   layer (D6).
5. **Weil pairing**: convention + pins per D7 (`weilPairingEval_restrict/_mul/
   _symplectic`); T-C0 = char-0 étale-descent construction as first milestone.
6. **Y(ρ̄)**: `rhoLevel_relativelyRepresentable` (T-F6, the `Isom^symp` scheme) is the
   route of record; twist-identification demoted to a later comparison theorem (D8).
7. **New workstreams**: SG (finite locally free closed subgroups; fppf-local
   cyclicity is REQUIRED before any Γ₀ representability theorem — T-D10 gate), and
   Q (finite quotients, split per the reviewer: group action; free action vs
   stabilizers; affine quotient via invariants; base change of invariants; gluing;
   quotients of rigidified problems; coarse statements). Phase 2 additionally gets
   N-Isog and cyclicity-as-closed-condition as named blocks (review Q8 list).
8. **Source gate — LIFTED 2026-07-08**: the full KM text is now in
   `refs/ModularCurves/katz-mazur-arithmetic-moduli-FULL.pdf`. KM 2.3 ([N]), KM 2.8 (pairings),
   KM 4.7, KM 5–7, KM 8–10, KM 12–13 may now be **proved-from-KM** — read the cited pages and
   quote them verbatim (page + section); do not prove from memory. (Was: may state from
   [Loe]/[Hida] quotes but not prove-from-KM until the full text is in `refs/`.)

### Revised spine (reviewer's A–N, adopted)

A Weierstrass examples & projective cubic models → B elliptic curves as smooth proper
**commutative group schemes** with genus-one fibres → C official relative effective
Cartier divisors → D smooth-curve divisor theory (sections, finite flat divisors,
degree) → E zero locus of a section of a finite locally free module → F incidence
`D' ≤ D`, `D = D'` → G subgroup-divisor closed locus → H exact order, A-structures,
A-generators → I `E[N]` finite flat rank `N²`, étale when `N` invertible → J Weil
pairing → K relative representability over `M_ell`/rigidified bases → L fine schemes
`Y(N)`, `Y₁(N)`, then `Γ₀`/N-Isog → M finite quotients & coarse moduli → N twisted
curves `Y(ρ̄,p)`.

### Composability guarantee (owner's question, answered 2026-07-05)

Full-level-`N` moduli for **all** `N` and arbitrary levels `P_H` come from this
machinery without rework: the incidence/A-structure block is uniform in the level
datum; the groupoid-valued problem *is* the stack for every `N` (honest at `N ≤ 2`,
level 1, `Γ₀`-stacky points), with `Y(N)` (`N ≥ 3`) providing presentations; other
`H`-levels arise by the Q-stream quotients. The excluded shortcuts (set-valued-
everywhere; naive fibrewise level definitions) are exactly the two that would have
forced redo. Deferred-not-redone: coarse moduli (KM 8), char `p ∣ N` theory (KM 5–7),
compactification; formal DM-stack *packaging* tracks mathlib's stack API (T-E8) but
no definition changes when it lands.

## Expert-review amendments (2026-07-06) — v8 staging correction (Weierstrass atlas / quotient stack)

Full detail + tickets in `tickets.md` §"Amendments v8". A **staging correction**, not a
KM replacement:

1. **`LocallyWeierstrass` is the Phase-1 definition of record** (owner's T-A8, validated);
   the abstract genus-1-fibre definition is a **Phase-4 comparison target** (`T-W-cmp`). The
   fibrewise-Weierstrass condition (`FibrewiseElliptic`) is NOT the definition of record — it
   does not directly give local equations, and proving it does needs the coherent-cohomology
   machine we avoid.
2. **`M_ell = [U/G]` concretely**: `U = Spec ℤ[a₁..a₆,Δ⁻¹]`, `G =
   WeierstrassCurve.VariableChange` (in mathlib). With locally-Weierstrass this is *almost the
   definition* — no RR. New **Stream W** (`T-W1`–`T-W8`, `T-W-cmp`): projective-space warm-up,
   groupoid-valued moduli core, quotient-stack core, coordinate-change group, universal atlas,
   the `M_ell^W` equivalence, group-law-from-charts, level spaces `U_P`.
3. **Group law from local Weierstrass charts + descent**, not Abel/Pic⁰ (`T-W7`); Abel/Pic⁰
   canonicity (T-A6) leaves the critical path into the COH stream.
4. **Coherent cohomology is a separate NON-blocking COH stream** — blocks only the abstract
   comparison, Hodge/modular forms, and compactification, never `Y(N)`/`Y₁(N)`/`Y(ρ̄,p)`.
5. **Cartier machinery is NOT replaced** — D-stream incidence still cuts out the level loci
   over `U`; the stack layer only organises the moduli object.


## Worker-grade proof plans + ecosystem (2026-07-05, v4)

Sources now READ IN FULL with proofs: KM Ch. 1 §§1.1–1.9 (all of it) and GME
2.2.1–2.2.6, 2.6.1–2.6.4. Binding worker decompositions:
- `decomposition-km1.md` — divisors, degrees, incidence loci, subgroup locus, 1.4.4,
  A-structures/A-generators, factorization, full sections; standing hard bits
  HB-NOETH / HB-FLF / HB-FIBCRIT; sub-tickets T-D22–T-D32.
- `decomposition-gme2.md` — chains A6 (Abel; COH pins), A7 (Weierstrass embedding —
  T-A2 now via Proj + Hida's 8-conditions chart analysis), E12–E15 (M₁, rigidity,
  Legendre, ℰ₃ — the KM-4.7 bootstrap objects, fully explicit), B8–B9 (dual
  isogeny/Hasse/Aut-computation), **C (Weil pairing construction — T-C1 un-gated)**,
  Y (Thm 2.6.8 = Y(N) over ℤ[1/p]/ℤ, incl. the G-torsor descent engine 2.6.7 and the
  reduced-universal-base transfer principle T-RED0).
- `ecosystem-survey-2026-07-05.md` — reuse/coordinate/watch table (mathlib PRs
  #25218/#41300/#35151/#40500/#36345/#36218/#24434/#38472-lane; toric; XYin;
  Loeffler's OpenModularCurve; FLT stubs; AINTLIB incremental reuse for OT/DESC/COH/
  FLAT/IRR) + the binding coordinate-don't-duplicate policy + owner actions.

## STREAM-E4 (2026-07-20, v5) — the receipts under the level-4 B2 resolution

B2 adjudicated (board v10.342, b2_log B2-DECISION): D(2) rigidifier = naive level 4.
Binding decomposition: `decomposition-e4.md` (verbatim KM quotes §0; trees §2–§8;
sympy-certified ℰ₄ ring design). Skeleton LANDED GREEN this session:
`Moduli/UniversalLevelFour.lean` (E4A: ring R[B,u,v][(B(1−16B))⁻¹]/(curve, e4Rel),
curve ⟨1,B,B,0,0⟩, P=(0,0), Q=(u,v), units/killing/keystone/bridges/packaging — 15
sorried leaves) + `Moduli/LevelFourTorsor.lean` (E4B: the two TorsorData exports).
Streams: E4-A ℰ₄-machine; E4-B torsor re-instantiation (all deps general-N — audit in
decomposition §3); E4-C engine rewire + Legendre quarantine; E4-D mouth core (route-map
v10.339/340, ForMathlib prereqs ALL banked); E4-E recollement glue (in-file recipes);
E4-F Drinfeld invertible-N reroutes (2 leaves); E4-G capstone census. Receipt matrix:
decomposition §8. NO cleanup tickets — producers do not clean (AINTLIB CLAUDE.md);
cleanup happens centrally on main post-merge.
