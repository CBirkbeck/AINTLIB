# Decomposition — the ENDOMORPHISM-DEGREE KEYSTONE (STREAM-KM v10.192 charter)

*Adversarial `/develop --decompose` (planning-only), 2026-07-14. Sources read at decompose time:
KM §§2.3, 2.5–2.7 (`refs/ModularCurves/katz-mazur-arithmetic-moduli-FULL.pdf`, pdf = print + 11,
verbatim quotes already banked in `decomposition-end0.md` + `decomposition-km2.3-b5d.md`);
HasseWeil `Foundation/Basic.lean` (degree stack) verified in-repo this session; the T-B6′ fibre-
comparison chain (`ModelRecord.lean`, `Comparison.lean`) re-verified GREEN today. Consumers: G0
(c4 rank-N²), GH ([RIG-2] rigidity root). NO held file edited; this is a planning artifact.*

## Charter & scope (the three keystone items, in order)

The keystone is the arithmetic root under {GH rigidity, both levels} + {G0 c4 = E[N] rank-N²} +
{BB-DEG `mulByHom_finrank=N²`, Torsion.lean:152}. Scope (coordinator v10.192):

- **(i)** `mulByHom_finrank (E) N x = N²` (`Torsion.lean:152`, sorry) — the SCHEME-theoretic fibre
  rank of `[N]`. **G0 consumes** for c4 (`torsion_rank`, Torsion.lean:193, already reduces to it via
  `finrank_pullback_snd`). Route: HasseWeil `mulByInt_degree` + the T-B6 fibrewise-degree→finrank bridge.
- **(ii)** `mulByHom_locallyQuasiFinite (E) N` (`Torsion.lean:140`, sorry) — `[N]` locally quasi-finite.
  **My own** `gammaOneDrinfeld_affineOverEll` E[N]-finiteness dep (via `torsionπ_isFinite`→`mulByHom_isFinite`).
- **(iii)** `deg(α−1)` for CM autos = the rigidity root. **GH consumes** via `aut_endo_eq_one`
  (`EndomorphismDegree.lean:240`, KM Cor 2.7.2(1)) / `endDeg_mulBy` (:107). Handshake the exact
  `deg(α−1)` signature with GH ([RIG-2] "Aut(E/k̄) acts freely on exact-order-N points, N≥3").

NOT BB-FLAT (`mulByHom_flat`, Torsion.lean:147 — a separate deeper comm-alg item, depth+A-B or local
flatness criterion; excluded by charter).

## THE ARITHMETIC ROOT IS T-B6′ (adversarial finding #1)

All three scopes lift HasseWeil's **field-level** degree to the **scheme** level, and every lift
routes through the **T-B6′ comparison**: the scheme fibre `E_s` over `κ(s)` ↔ a HasseWeil `Affine κ(s)`
Weierstrass curve, carrying scheme-`[N]` → Weierstrass-`[N]`.

- HasseWeil `mulByInt_degree` (`Foundation/Basic.lean:727`, PROVEN, `hn : n ≠ 0`):
  `(mulByInt W n).degree = (n^2).toNat`. Here `Isogeny.degree` (Basic:87) is **`Module.finrank` of
  FUNCTION FIELDS** `[K(E₁):K(E₂)]` — canonicity-FREE (tower law `[K(E):F(x)]=2`), over any **field**
  `F` (`[Field F][DecidableEq F][IsElliptic]`, no char/alg-closed hypothesis). This is the numeric root.
- `Scheme.Hom.finrank` (mathlib `FlatRank.lean:88`) is the scheme fibre rank; **hinge**
  `finrank_SpecMap_algebraMap` (:134): `finrank (Spec.map (algebraMap R S)) x = Module.rankAtStalk S x`
  `[Module.Finite R S][Flat R S]`. `finrank_pullback_snd` (:156) is already used by `torsion_rank`.
- **The bridge itself is UNBUILT** — no decl anywhere in `projects/` connects HasseWeil `Isogeny.degree`
  to `Scheme.Hom.finrank`; the two worlds are code-disjoint (HasseWeil is all Point/function-field level).

### Adversarial finding #2 — the 07-09 "WALL" is substantially breached (re-verified today)

`black-box-plan.md` (2026-07-09) called T-B6′ a *"several-hundred-LOC WALL rooted in the sorried
`abelEnrichment_exists`."* **That read is now stale.** Verified 2026-07-14:

- `EllipticCurve/ModelRecord.lean` — **0 sorries.** Provides `modelEllipticCurve (W : WeierstrassCurve R)
  [W.IsElliptic] : EllipticCurve (projModel scheme)` (:68) and the group-compat
  `modelEllipticCurve_point_add_val` (:269), routing through the **PROVEN**
  `abelEnrichment_unique_of_isLocallyNoetherian` (Rigidity.lean) — **NOT** the sorried *existence*
  `abelEnrichment_exists` (GroupLaw.lean:75, still sorry, but AVOIDED here).
- `EllipticCurve/Comparison.lean` — **0 sorries.** Fibre-Weierstrass identification:
  `isElliptic_of_fibrewiseElliptic_projModel` (:300), `locallyWeierstrass_projModel` (:243),
  `fibrewiseElliptic_iff_locallyWeierstrass_projModel` (:427); base-changes `WeierstrassCurve R` to
  `κ(p)` with `IsPullback` fibre squares (`fiberToSpecResidueField`, `projModelBaseChange`).

So the **group-compatible fibre-comparison scaffolding EXISTS sorry-free.** What remains is the
**DEGREE bridge on top of it** — a MODERATE leaf, not a wall.

## Prose proof of scope (i) `mulByHom_finrank = N²` (the crux; source = KM 2.3.1 / Silverman III.6.2(d))

KM 2.3.1 (print p.73, pdf 84): *"the S-homomorphism `[N]:E→E` is finite locally free of rank `N²`."*
Proof reduces fibre-by-fibre (KM p.74): the rank at `x` is computed on the geometric fibre `E_s`, where
`[N]` is a degree-`N²` isogeny (Silverman III.6.2(d) = HasseWeil `mulByInt_degree`). Formalisation chain:

1. **Fibre-reduce** `(E.mulByHom N).finrank x` to the fibre over `s = (E.π ≫ …) x` / the residue field
   `κ(s)`. `Scheme.Hom.finrank` is locally constant on the finite-flat locus (`isLocallyConstant_finrank`);
   compute it after base-change to `Spec κ(s)`.
2. **Identify the fibre** `E_s ≅ modelEllipticCurve (W_s)` for a Weierstrass `W_s / κ(s)` — from
   `Comparison.lean` (green). `W_s.IsElliptic` holds fibrewise (`isElliptic_of_fibrewiseElliptic_projModel`).
3. **Match `[N]`**: `(E.mulByHom N)` on the fibre = `modelEllipticCurve`'s `[N]` = the Weierstrass
   model's `[N]` — via `ModelRecord.modelEllipticCurve_point_add_val` (green group-compat) + `mulBy` = the
   hom-group power.
4. **Degree = N²**: the model's `[N]` scheme-finrank = `rankAtStalk` (via `finrank_SpecMap_algebraMap`) =
   the coordinate-ring rank = HasseWeil `(mulByInt W_s N).degree = N²` (`mulByInt_degree`, `N ≠ 0` from
   `NeZero N`). The one genuinely-new identity: **finite-flat scheme fibre-rank = HasseWeil function-field
   degree** for the model's `[N]` (rank = generic-fibre field-extension degree for finite flat isogenies).

## Ordered leaf decomposition (scope i/ii; scope iii = existing `decomposition-end0.md` + GH handshake)

- **K1** (leaf, mathlib+project): fibre-reduction `mulByHom_finrank` → fibre finrank over `κ(s)`.
  Discharge: `finrank_pullback_snd` + `isLocallyConstant_finrank` (mathlib, verified) + base-change to
  residue field (`fiberToSpecResidueField`, Comparison.lean). Source: KM 2.3.1 fibre reduction, p.74.
- **K2** (leaf, project-green): fibre `E_s ≅ modelEllipticCurve W_s`. Discharge: `Comparison.lean`
  (0 sorries). Source: KM 2.3.1 "geometric fibre by geometric fibre."
- **K3** (leaf, project-green): `[N]`-group-compat on the model. Discharge:
  `ModelRecord.modelEllipticCurve_point_add_val` (0 sorries) + `mulBy` power. Source: `[N]` = N-fold sum.
- **K4** (leaf, THE new bridge, MODERATE): model `[N]` scheme-finrank = HasseWeil `mulByInt_degree` = N².
  Discharge: `finrank_SpecMap_algebraMap` (mathlib hinge) + rank=field-degree for finite-flat + HasseWeil
  `mulByInt_degree` (import). Source: Silverman III.6.2(d) / KM 2.3.1. **This is T-BB-DEG-1, the primary grind.**
- **K5** (assembly): `mulByHom_finrank = N²` = K1∘K2∘K3∘K4. Then `torsion_rank` (already wired) gives c4 for G0.
- **QF1** (leaf, scope ii): `mulByHom_locallyQuasiFinite` — `[N]` nonconstant (from `mulByInt_degree = N² ≠ 0`
  ⟹ `[N] ≠ 0`, fibrewise) ⟹ finite fibres ⟹ locally quasi-finite. Discharge: same K2/K3 fibre route +
  nonconstancy + fibre criterion. Source: KM 2.3.1 fibre input (BB-QF), `black-box-plan.md` T-BB-QF-1/2.
  (Cheaper than K4 — only needs `[N] ≠ 0` on fibres, not the exact degree.)
- **scope (iii)** `deg(α−1)`: the ABSTRACT `endDeg` route (`decomposition-end0.md`, `aut_endo_eq_one`
  already ASSEMBLED + proven modulo its leaves; `gme_deg_trace_forces_zero` proven). `endDeg_mulBy=N²`
  (:107) is the same K1–K4 numeric anchor. GH's [RIG-2] consumes a `deg(α−1)`-shaped fact — **exact
  signature pending GH handshake** (see below).

### Adversarial finding #3 — the finrank-degree UNIFICATION (highest-leverage route, flagged for owner)

The abstract `endDeg` (EndomorphismDegree.lean:43, DATA-sorry) is KM-defined via the **dual isogeny**
`f^t f = [deg f]` (KM 2.6.1), and `endDual` (`f^t = Pic(f)` via Abel's iso, KM 2.5.1) is **canonicity/
Abel-Pic⁰-gated** (the deferred canonicity project — same family as `abelEnrichment_exists`). BUT KM's
own identification is `deg = "isogeny degree" = finrank`. Since `Scheme.Hom.finrank` is now the tractable
route (green T-B6′ scaffolding), the keystone can be **UNIFIED**: define the degree via the scheme
finrank (K4/notion-3), so `endDeg_mulBy = mulByHom_finrank = N²` is ONE bridge and `deg(α−1) =
finrank(α−1)` — **avoiding the Abel-gated dual construction**. TENSION: the rigidity computation
(`aut_endo_eq_one`) also uses `endTrace`/`endDeg_one_add` (the quadratic-form polarization); a
finrank-degree must be shown to satisfy `deg(f+g) = deg f + deg g + ⟨f,g⟩` (bilinear) — that polarization
may still need the dual/trace, which is the residual Abel-gated piece. **Recommendation: build scope (i)
K1–K5 (scheme finrank, Abel-FREE) FIRST — it discharges G0's c4 + my E[N]-finiteness with no canonicity
gate; then assess whether GH's `deg(α−1)` needs only `deg[N]/finrank` numerics (Abel-free) or the full
trace polarization (Abel-gated).**

## Attacks attempted (per crux leaf)

- **K4** (the new bridge):
  - [1] Counterexample: is scheme fibre-rank ≠ function-field degree? For a finite FLAT morphism the
    fibre rank equals the generic-fibre field-extension degree (locally constant, `isLocallyConstant_finrank`);
    `[N]` is finite flat (given `mulByHom_flat`/`torsionπ_flat` — but note the rank K4 does NOT need flat if
    computed as `rankAtStalk` at the specific fibre). No counterexample; the identity is standard for finite flat.
  - [2] Edge cases: `N=1` → `[1]=id`, finrank 1 = 1² ✓; `N=0` excluded (`NeZero N`, and `mulByInt_degree`
    needs `n≠0`); char `p | N` (supersingular) → `[N]` inseparable but STILL degree `N²` (mulByInt_degree
    has NO char hypothesis — it's the flat degree, insep-robust) ✓, and finrank counts with multiplicity ✓.
  - [3] Hypothesis test: does K4 need `N` invertible? NO — the RANK is `N²` in all characteristics (only
    étale-ness/separability needs `N` invertible; the finrank is char-free). So K4 (and c4) is char-free,
    unlike the unramified BB-DIFF. Confirmed against KM 2.3.1 ("finite locally free of rank N²" — no
    invertibility) vs the separate "E[N] étale iff N invertible."
  - [4] Source-drift: KM 2.3.1 says rank `N²` (Silverman III.6.2(d) `deg[N]=N²`); HasseWeil
    `mulByInt_degree = (n²).toNat`. Match (`.toNat` = `N²` for `N:ℕ`). No drift.
  - [5] Discharge: `finrank_SpecMap_algebraMap` verified (FlatRank.lean:134, needs `Finite`+`Flat`);
    `mulByInt_degree` verified (Basic:727); `modelEllipticCurve`/`Comparison` green. The rank=field-degree
    step is the one un-cited composition — **primary execution risk, validate FIRST in beastmode.**
- **K1/K2/K3, QF1**: discharge on green scaffolding (`Comparison`/`ModelRecord` 0 sorries) + mathlib
  `finrank_pullback_snd`/`isLocallyConstant_finrank`. Attacks: fibre-reduction is char-free; nonconstancy
  (QF1) needs only `N²≠0`. SURVIVED.

## Feasibility verdict

**MODERATE, BUILDABLE — no longer walled.** The 07-09 "T-B6′ wall" is breached: the group-compatible
fibre-comparison scaffolding (`modelEllipticCurve`/`ModelRecord`/`Comparison`, 0 sorries, via proven
`abelEnrichment_unique`) exists. Scope (i) `mulByHom_finrank=N²` decomposes into K1–K5 with **one new
MODERATE leaf K4** (scheme fibre-rank = HasseWeil function-field degree) + green scaffolding + mathlib
hinges; it is **char-FREE and Abel-FREE** (adversarial finding: the RANK needs neither invertibility nor
canonicity — only the ÉTALE-ness does). Scope (ii) QF1 is cheaper (needs only `[N]≠0` fibrewise). Scope
(iii) deg(α−1): the abstract endDeg is Abel-gated via the dual, BUT can be **re-anchored on the K4 scheme
finrank** (unification) to serve GH's numeric `deg(α−1)` Abel-free — pending the GH signature handshake +
the trace-polarization assessment. **Recommended grind order: K4 (the bridge) → K1/K2/K3/K5 assembly →
mulByHom_finrank ⟹ G0's c4 + my E[N]-finiteness; QF1 in parallel; then GH-handshake deg(α−1).**

## Consumer API (pinned)

- **G0** ⟵ `mulByHom_finrank (E) N x = N²` (Torsion.lean:152) ⟹ `torsion_rank` (already wired) = c4 rank-N².
- **GH** ⟵ `deg(α−1)` / `endDeg_mulBy` / `aut_endo_eq_one` (EndomorphismDegree.lean:240). **Exact signature
  PENDING GH handshake** — GH's [RIG-2] is "Aut(E/k̄) acts freely on exact-order-N points, N≥3"; the root
  is `deg(α−1) < N` for CM units. Need from GH: is the consumed fact `endDeg (α - 1) = <value>` in
  End(E/S)-language, or a fibre/`κ(s)`-level `Isogeny.degree`? This determines Abel-free (finrank) vs
  Abel-gated (dual/trace).

## Next step

`/beastmode` after this decompose (coordinator directive). First grind = **K4** (the finrank↔HasseWeil-
degree bridge — the primary risk to validate) on the green `Comparison`/`ModelRecord` scaffolding; then
K1/K2/K3/K5 assembly → `mulByHom_finrank`; QF1 in parallel. Handshake GH for the `deg(α−1)` signature
before committing scope (iii)'s Abel-free-vs-dual route.

---

## BEASTMODE GRIND STATUS (2026-07-14, STREAM-KM) — K4 FOUNDATION DELIVERED, CRUX ISOLATED

Source-faithful refinement of the "MODERATE" verdict after reading the actual sources
(`FlatRank.lean`, `FreeLocus.lean`, `MulByIntPullback.lean`, `PointsDictionary`, `ModelRecord`,
mathlib `FunctionField.lean`): K4 is **feasible on green scaffolding but BB-DIFF-scale** — the
field-level finrank bottoms out at the SAME T-B6′ crux (scheme model-[N] ↔ HasseWeil `mulByInt`
coordinate/pullback match) that leaves BB-DIFF (`formallyUnramified_torsionπ`) sorried. NOT a wall
(every leaf has concrete mathlib/project support), but a multi-lemma marathon.

**DELIVERED GREEN (committed, `MulByHomDegree.lean` + `FinrankFractionField.lean`):**
- **Leaf A** `finrank_SpecMap_algebraMap_eq_finrank` — scheme affine finrank = R-module rank over a
  domain (via `finrank_SpecMap_algebraMap` + `Ideal.finrank_fiber_eq_finrank`). *The primary-risk
  rank=field-degree step, VALIDATED in code.*
- **Point-[N]-match** `projModelPointsEquiv_add`/`_AddEquiv`/`_zsmul` — scheme model-[N] = mathlib
  `Affine.Point` [N] under the green dictionary (`mulModelHom_specPoints` + `point_smul_eq_comp_mulBy`).
- **(B)** `projModelFunctionFieldEquiv` — `K(projModel W) ≃+* W.toAffine.FunctionField`
  (`functionField_isFractionRing_of_isAffineOpen` + `coordRingToZSection` + `MulEquivClass.map_nonZeroDivisors`).
- **(D) local-constancy** `modelEllipticCurve_finrank_const` — finrank(model-[N]) constant on integral
  `projModel W` (`isLocallyConstant_finrank` + preconnectedness).

**REMAINING (the isolated crux) for `modelEllipticCurve_mulByHom_finrank = N²` (field-level target):**
- **single-point value**: by local-constancy, compute finrank(model-[N]) at one x₀ ∈ Z-chart:
  affine-restrict model-[N]|_{[N]⁻¹(Zchart)} = `Spec.map (Γ(Zchart) → Γ([N]⁻¹Zchart))` → Leaf A gives
  `= Module.finrank W.CoordinateRing Γ([N]⁻¹Zchart)`.
- **(C) coordinate/pullback match**: that rank = `(mulByInt W.toAffine N).degree = N²`, because the
  restricted ring map's fraction-field = `mulByInt_pullbackAlgHom` — provable from the GREEN point-[N]-match
  read at the generic point via `projModelPointsEquiv_some` (coordinate readout = division polynomials =
  `mulByInt_xHom`). **This is the deep arithmetic anchor (tied to the model's Proj-coordinate structure ↔
  HasseWeil's division polys) — the true residual crux, shared with BB-DIFF.**

**Then Torsion assembly** (discharges `Torsion.lean:152`): L-K1 fibre-reduction (`finrank_pullback_snd`,
Torsion's flat/finite) + L-K2 one-point model iso (`E_s ≅ projModel W_s` via `LocallyWeierstrass` over the
one-point base `Spec κ(s)` + rigidity) ⟹ arbitrary-E `mulByHom_finrank` ⟹ G0's c4 + affineOverEll E[N]-finiteness.

## BEASTMODE GRIND STATUS (2026-07-14 cont'd, STREAM-KM) — K4a + K4b-1 GREEN; K4b-2 = SINGLE ISOLATED WALL

The field-level target `modelEllipticCurve_mulByHom_finrank = N²` is now **GREEN modulo ONE pure-algebra
sorry**. Everything scheme-theoretic AND affine-algebraic is discharged. New green (committed):
- **Target** `modelEllipticCurve_mulByHom_finrank = N²` = crux `modelEllipticCurve_finrank_eq_mulByInt_degree`
  (`finrank x = (mulByInt N).degree`) + `HasseWeil.mulByInt_degree`. GREEN-modulo-crux.
- **K4a** (scheme reduction, GREEN): general helpers `finrank_eq_appTop_finrank_of_affineOpen`,
  `finrank_of_isAffine` — a finite-flat-LFP endomorphism of a preconnected scheme has fibre rank =
  `appTop` RingHom.finrank of its restriction `f⁻¹(U)→U` (local-constancy + `finrank_pullback_snd` +
  `isoSpec`/`finrank_SpecMap_eq_finrank`). *Stated generically → the `(modelEllipticCurve W).E` vs
  `projModel W` instance-transparency wall is breached at the model call via `show ((…).E).Opens from …` casts.*
- **K4b-1** (appTop→module rank, GREEN): `appTop_finrank_eq_module_finrank` + `finrank_algebraMap_eq_module_finrank`
  + `finrank_eq_module_finrank_of_affineOpen` — over a domain base, `appTop.finrank = Module.finrank Γ(U) Γ(f⁻¹U)`.
  `IsDomain Γ(Z-chart)` auto (`IsIntegral projModel` + `Nonempty` → mathlib `Properties.lean:244`).

**K4b-2 (THE isolated wall)** — the sole remaining sorry, cleanest possible form:
`Module.finrank Γ(Z) Γ([N]⁻¹Z) = (mulByInt W.toAffine N).degree`. Decomposition (source-faithful) + hinges:
- **L1** `Γ(Z) ≃+* W.CoordinateRing` — `coordRingToZSection` (green) + `Γ(U.toScheme,⊤)`↔`Γ(X,U)` bridge.
- **L3** rank over domain = rank over Frac — **mathlib `finrank_of_isFractionRing`** (Algebraic/Integral.lean:552,
  needs `FaithfulSMul`/`IsAlgebraic`/`NoZeroDivisors`, all from finite-flat + `[N]⁻¹Z` integral-open-of-projModel).
- **L4 (deep)** `Frac Γ(Z) = Frac Γ([N]⁻¹Z) = W.FunctionField` **and the appTop map = `mulByInt_pullbackAlgHom`** —
  i.e. the scheme morphism `[N]`'s function-field pullback = HasseWeil's division-polynomial `mulByInt` pullback.
  Both realise `[N]` (green dictionary `projModelPointsEquiv_zsmul`; `mulByInt_apply`), matched at the GENERIC point.
  **mathlib LACKS a packaged `Scheme.Hom.functionFieldMap`** (only `germToFunctionField` + stalk algebra) → L4 needs
  BUILDING the scheme-morphism function-field pullback + the generic-point coordinate readout = division polys
  (HasseWeil `GenericPointZsmul.lean`). This is the genuine multi-session infra, the SAME crux as BB-DIFF.

Note: full `Torsion.lean:152` (arbitrary `E/S`) additionally needs K1/K2/K3/K5 (fibre base-change of finrank to
`κ(s)` via `fiberToSpecResidueField` + `(projModelπ W).fiber ≅ projModel(W.map …)` in Comparison.lean) ON TOP of K4.
