# Decomposition — the four Y(ρ̄) caveats (2026-07-25)

Planning pass for the four gaps that remain after `yRho_representable'` landed:

| # | Gap | Scale | Status of source |
|---|-----|-------|------------------|
| G1 | derive `p` from `det_cyclo` | small (≈150–250 LOC) | mathlib `toFun_spec` + in-repo `card_rootsOfUnity_algClosureQ` |
| G2 | DS4 Weil pairing over `S` | MAJOR (stream C) | GME 2.6.4 pp. 152–153, transcribed in `decomposition-gme2.md` §Chain C |
| G3 | Legendre registers (3) | medium ×3 | KM 4.6.2 + Silverman III.1.7(b); in-repo `SqrtCoverGlue`/`LegendreTorsor` |
| G4 | geometric irreducibility | shell small + core MAJOR-INFRA | KM 10.9.2 p. 303, transcribed in `decomposition-km10.md` |

---

## G1 — `p` from `det_cyclo` (the Λ²ρ̄ ≅ μ_N normalisation)

### Plain-English proof

`V_ρ̄` is `(ℤ/N)²` with `G_ℚ` acting through `ρ̄`, so `Λ²V_ρ̄` is free of rank one over
`ℤ/N` with `G_ℚ` acting through `det ρ̄`. The hypothesis `det ρ̄ = χ_N` says this action
is the mod-`N` cyclotomic one, which is exactly the action on `μ_N(ℚ̄)`. Hence
`Λ²V_ρ̄ ≅ μ_N` equivariantly. Concretely: choose a primitive `N`-th root of unity
`ζ ∈ ℚ̄` (exists: `ℚ̄` is algebraically closed of characteristic zero, and the repo's
`card_rootsOfUnity_algClosureQ` already extracts one from `Polynomial.cyclotomic N`).
Define `p : Multiplicative (ℤ/N) ≃* μ_N(ℚ̄)` by `a ↦ ζ^a`. This is a group isomorphism
because `ζ` is primitive (so `Subgroup.zpowers ζ = rootsOfUnity N ℚ̄` and the order is
`N`). Equivariance is then *automatic*, not an extra condition: for `σ ∈ G_ℚ`,
`σ(ζ^a) = (σζ)^a = (ζ^{χ(σ)})^a = ζ^{χ(σ)a} = p(a^{χ(σ)})`, where the middle equality
is the defining property of the modular cyclotomic character. Note `det_cyclo` is **not
used** in this step: any `ζ` works, and equivariance holds for the cyclotomic action by
definition. `det_cyclo` is what makes `p` the *right* normalisation downstream — it is
the hypothesis that the `Λ²ρ̄`-action agrees with the `μ_N`-action, so that a symplectic
level structure can exist at all.

### Lemmas (in order)

- **G1.L1** (leaf, mathlib + project): `exists_isPrimitiveRoot_algClosureQ`
  - Statement: `∃ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ N`
  - Source: standard; the repo already performs this extraction inside
    `card_rootsOfUnity_algClosureQ` (YRho.lean:56–66) using
    `IsAlgClosed.exists_root` on `Polynomial.cyclotomic N` and
    `Polynomial.isRoot_cyclotomic_iff`.
  - Discharged by: the same three-line chain, factored out.

- **G1.L2** (leaf, mathlib): `mulEquiv_of_isPrimitiveRoot`
  - Statement: for `ζ` a primitive `N`-th root in a field `K`,
    `Multiplicative (ZMod N) ≃* rootsOfUnity N K`.
  - Discharged by: `IsPrimitiveRoot.zmodEquivZPowers` (`ZMod k ≃+ Additive (zpowers ζ)`)
    composed with `IsPrimitiveRoot.zpowers_eq` (`zpowers ζ = rootsOfUnity N K`), then
    `Multiplicative`/`Additive` transport. Verified present in
    `Mathlib/RingTheory/RootsOfUnity/Basic.lean`.

- **G1.L3** (leaf, mathlib): `pow_val_eq_galois_action`
  - Statement: for `g : L ≃+* L` and `t : rootsOfUnity n L`,
    `g t = t ^ (modularCyclotomicCharacter … g).val`.
  - Source claim (verbatim, `Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean:130`):
    > "/-- The formula which characterises the output of `modularCyclotomicCharacter g n`. -/
    > theorem toFun_spec (g : L ≃+* L) {n : ℕ} [NeZero n] (t : rootsOfUnity n L) :
    >     g (t : Lˣ) = (t ^ (χ₀ n g).val : Lˣ)"
  - Lean ↔ source match: this *is* the equivariance clause of `GaloisRepData.p_equivariant`,
    after transporting `χ₀` along `card_rootsOfUnity_algClosureQ`.

- **G1.MAIN** (assembly): `GaloisRepData.ofDetCyclo`
  - Statement: given `ρ`, `ker_open`, `det_cyclo`, produce a `GaloisRepData N` whose
    `ρ`/`ker_open`/`det_cyclo` are the given ones.
  - Plus `exists_galoisRepData_of_detCyclo`: the `∃`-form, and simp lemmas pinning the
    three transported fields.

### Attacks attempted (G1)

1. *Counterexample search*: is there an obstruction to `Λ²ρ̄ ≅ μ_N` when `N` is composite?
   No — both sides are free rank-one `ℤ/N`-modules with the same action; the iso is a
   choice of generator. Searched for `rootsOfUnity` non-cyclic in char 0: cyclic by
   `IsCyclic` instance for finite subgroups of a field's units.
2. *Edge cases*: `N = 1` (both sides trivial ✓), `N = 2` (`ζ = -1` ✓), `N` composite
   (the `zmodEquivZPowers` route is stated for arbitrary `k`, no primality ✓).
3. *Hypothesis test*: is `det_cyclo` needed for `p` to exist? **No** — this is the
   substantive finding: `p` exists unconditionally; `det_cyclo` is what makes the pair
   `(ρ̄, p)` symplectically coherent. So the corrected design is: `p` is derived, and
   `det_cyclo` stays a hypothesis (it is used at YRho:1476/1840/6237/6272 in the
   equivariance of the pairing map on `V_ρ`).
4. *Source-drift*: `toFun_spec` is about `g (t) = t ^ χ.val` for `t` in `rootsOfUnity`;
   the repo's `p_equivariant` says `σ (p x) = p (x ^ χ.val)`. These match after
   `MulEquiv.map_pow`. No drift.
5. *Discharge*: `IsPrimitiveRoot.zmodEquivZPowers` and `IsPrimitiveRoot.zpowers_eq`
   both verified present; `card_rootsOfUnity_algClosureQ` is in-repo and sorry-free.

Verdict: SURVIVED. G1 is READY.

---

## G2 — DS4: the Weil pairing over a base (stream C)

**Source of record (already transcribed):** Hida, *Geometric Modular Forms and Elliptic
Curves*, §2.6.4 pp. 152–153 — see `decomposition-gme2.md` §"Chain C", steps C.1–C.5,
where the proof was read and transcribed by an earlier `/develop --decompose` pass. The
KM 2.8 gate was lifted there ("T-C1's construction of record; KM-gate LIFTED").

**What already exists (verified this pass):**
- The descent engine is **complete and gate-free**: `weilPairingCharZero` +
  `weilPairingCharZero_restrict/_over/_unique` (`WeilPairing/CharZeroDescent.lean:193–255`)
  descend a local pairing along any fppf cover.
- The constant symplectic model is complete: `detFun`, `detConstMor`,
  `detConstMor_gl2Both`, `detConstMor_sl2` (same file, lines 57–160).
- A **sorry-free field-level Weil pairing** exists in the monorepo:
  `projects/HasseWeil/HasseWeil/HasseBound/WeilPairing/Pairing.lean` (Silverman III.8
  route: `weilFunction`, `weilPairing`, `weilPairing_mul_left`, `weilPairing_ne_zero`,
  `weilPairing_translate`, …; `grep -c sorry` = 0). CLAUDE.md's one-workspace rule makes
  this importable.

**The gap.** `weilPairingCharZero` needs `(p, ζ', hcocyc)`. The naive choice — trivialise
`E[N]` by the full-level cover and take the constant determinant pairing — **fails the
cocycle condition**: two trivialisations differ by `g ∈ GL₂(ℤ/N)` and `detFun` transforms
by `det g` (`detConstMor_gl2Both`), so the local pairings do not agree on the double
overlap unless the transitions are symplectic — which presupposes the pairing. This is a
genuine obstruction, not a technicality: the Weil pairing is geometric data (divisors /
autoduality), not something readable off a trivialisation.

**Consequences for the plan.** Two milestones, in order:

- **G2.M1 (field base, tractable):** `E/K` over a char-0 field. `E[N]×E[N]` and `μ_N` are
  finite étale over `K`; HasseWeil's pairing gives the values on `K̄`-points and the
  Galois-equivariance of those values; the repo's
  `exists_finiteEtaleHom_of_galoisEquivariant` (WeilPairing/EtaleDescent.lean) converts a
  Galois-equivariant map of geometric points into a `K`-morphism. This discharges DS4 and
  the T-C2/T-C3/T-C4 specs **over field bases**, and pins the normalisation (T-C4).
- **G2.M2 (general `ℚ`-scheme, MAJOR):** the GME 2.6.4 construction C.1–C.5 — relative
  `Pic`, the isogeny transpose, the gluing-units computation. Prerequisites: the repo's
  `Picard/RelativePic.lean` plus the A6/A7 chains. Multi-session; the honest estimate from
  the transcription is that C.1–C.5 is a chapter-scale development.

Neither milestone is skippable if "no shortcuts" is to be honoured; M1 is the first
increment and is what the `RhoLevelStructure` fibre clauses actually consume.

---

## G3 — the three Legendre registers

- **G3.a `legendreDelta_surjective_of`** (LegendreTorsor.lean:316). Content: every
  elliptic curve over an algebraically closed field with `2` invertible admits a Legendre
  datum. Source: Silverman AEC III.1 Prop 1.7(b) (Legendre form after adjoining the
  2-torsion abscissae and a square root); KM 4.6.2 for the moduli formulation. In-repo
  ingredients: `universalLegendre_generation`, `exists_projModelIso_of_field`
  (KeystoneGeometricPoint), the `fullLevelLocus 2` machinery.
- **G3.b `legendreDelta_exists_naturalFamily`** ([T-E14-NAT], LegendreTorsor.lean:230–239).
  Content: naturality in `T` of the Legendre representing bijections. The bijections
  themselves are built in `SqrtCoverGlue.lean:848`; naturality must be threaded through
  that construction (the same shape as the ρ-side `rhoOfSection_pull`, which is proven).
- **G3.c `legendreDeltaGAction`** ([T-E14-ACT'], LegendreTorsor.lean:290). Content: the
  coupled `GL₂(𝔽₂) × {±1}`-action on `δ` (re-mark the pair *and* rescale `ω`).
  Source: KM 4.6.2 ("|G| = 12"). Independent of G3.a/G3.b.

Each is medium (in-repo geometry, no absent mathlib infrastructure identified).

---

## G4 — geometric irreducibility

Already decomposed in `decomposition-km10.md` (2026-07-08). Verbatim finding recorded
there: **KM's "algebraic route" is not analytic-free** — KM 10.9.2 p. 303 reduces to the
transcendental description "the underlying complex manifold to `M(𝒫)⊗ℂ` is isomorphic to
the quotient of the upper half plane by `Γ̃ ⊂ SL(2,ℤ)`".

- **Shell (buildable now)**: `T-IRR1` `irreducibleSpace_of_connectedSpace_of_smooth`,
  `T-IRR2` `connectedSpace_quotient_orbitRel`, `T-IRR3`
  `yRho_geometricallyIrreducible_of_connected` — the reduction of the target to geometric
  *connectedness*, plus the two general topology/geometry leaves. Skeleton file already
  exists: `ModularCurve/IrreducibilityScoping.lean`.
- **Core (MAJOR-INFRA)**: `T-IRR-L3` `(Y⊗ℂ)^an ≅ ℍ/Γ̃` needs a scheme-analytification
  functor and a LeanModularForms bridge; `T-IRR-L5` needs GAGA-connectedness. Both are
  absent from mathlib *and* AINTLIB. The prior pass's recommendation stands: land the
  shell, keep the analytic input as a labelled hypothesis (`hconn`) until the
  analytification stream exists.

With the shell landed, `yRho_geometricallyIrreducible` becomes: "conditional on geometric
connectedness of `Y ⊗ ℚ̄`" — a one-hypothesis theorem rather than a `sorry`.

---

## Execution order (tickets in `tickets.md`)

1. **G1** — READY, no dependencies. Land `ofDetCyclo`, then thread it (the datum keeps
   `det_cyclo`; `p` stops being user-supplied).
2. **G4 shell** — READY (T-IRR1/2/3 already stated in `IrreducibilityScoping.lean`).
3. **G3.c → G3.a → G3.b** — in-repo geometry.
4. **G2.M1** — field-base DS4 + T-C4 normalisation pin.
5. **G2.M2**, **G4 core** — the two chapter-scale streams; ticketed, sourced, not
   promised on a short horizon.

---

# EXECUTION LOG — 2026-07-25 (beastmode, "address the caveats, no shortcuts")

## G1 — DONE, axiom-clean
`GaloisRepData.ofDetCyclo` + `exists_galoisRepData_of_detCyclo` (YRho.lean): the pairing
normalisation `p` is now *derived* from `det_cyclo` via
`exists_isPrimitiveRoot_algClosureQ` / `pairingNormalisationOfPrimitiveRoot` /
`pairingNormalisation_equivariant`. `p` is no longer user-supplied data.

## G3.a — DONE (`legendreDelta_surjective_of` PROVEN)
Chain landed this session:
* `EllipticCurve/LegendreNormalForm.lean` (sorry-free): `scale_translate_smul_eq_legendreCurve`,
  `completeSquareVC_a₁/₃`, `two_torsion_coords_of_charNeTwoNF`, `two_torsion_abscissa_injective`,
  `exists_third_root_vieta` (ring-level: two roots with a **unit** difference),
  `exists_legendre_variableChange_of_two_torsion`.
* `Moduli/LegendreChart.lean` (new, sorry-free): `negY_marked_eq_of_two_torsion`
  (the N = 2 mirror of `hdbl_of_marked_three_torsion`), `isLegendreChart` (the N = 2 mirror
  of `isE3Chart`), `exists_marked_charNeTwo_chart`, `exists_unit_sq_eq_of_isAlgClosed`,
  **`exists_isLegendreDatum_of_isAlgClosed`** (axioms: propext/choice/Quot.sound only).
* `isUnit_x_diff_of_marked_pair` promoted out of the quarantined `SqrtCoverGlue` into
  `E3DatumAssembly` (public; no duplication).
* `legendreDelta_surjective_of` proved by anchored geometric point + `E.eqv` classification,
  mirroring `levelThree_surjective`.
* **B2 (logged)**: the register was FALSE as stated — it omitted `IsUnit (2 : R)`. Over `𝔽₂`
  the Legendre problem is empty on nonempty bases (a Legendre chart forces `Δ = 16λ²(λ−1)²`
  to be a unit), so the empty scheme is a valid equivariant relRepData with a non-surjective
  structure map. Hypothesis added; all call sites already had it in scope.

## G3.b — NOT PROVABLE AS STATED (interface artifact; precise fix recorded)
`legendreDelta_exists_naturalFamily` is stated for `legendreDeltaZ`/`legendreDeltaF`, which
are `Exists.choose` of `legendreDelta_relRep_finiteEtale`. That existential only ships a
`Nonempty`-per-`g` family (because `ScaleTorsorData.spec` is `Nonempty`-valued), and
`Exists.choose` is opaque — so **no naturality statement about the chosen `Z`/`f` is
derivable**. This is not a proof gap but an interface defect.

**Fix (the only honest route)**: strengthen `ScaleTorsorData.spec` to a `Nonempty` of a
*bundled* family (equivs + naturality square), thread naturality through the four steps of
`legendreDelta_relRep_finiteEtale_of_scaleTorsor`
(`sectionsCompSigmaEquiv`, `sigmaCongrRight spec`, `sigmaCongrLeft fullLevelLocusPointsEquiv`,
`sigmaSubtypePairEquiv`), and re-extract `legendreDeltaData` as a genuine `RelRepData`;
`legendreDelta_exists_naturalFamily` then disappears. Sub-blocker: naturality of
`fullLevelLocusPointsEquiv` (`LevelStructure/CombinationLevel.lean:538`) in `T`, best done by
the *pinning* pattern used on the level-3 leg (`YFull.exists_pointsEquiv_family`, via
`dictPoint₁/₂` + `dict_lift_eq`), not by an abstract naturality chase.
Net effect: removes a leaf but does **not** reduce the cone's `sorryAx` — the content sits in
`exists_scaleTorsorData`, which stays sorried (quarantined subtree, documented non-goal).

## G3.c — retired (B2, earlier this session)
`legendreDeltaGAction` is not constructible over a general base (√λ exists only
étale-locally); the main theorem now runs on the genuine `{±1}` package
(`legendreDeltaSignEquivariantData`).

## G2 — partial: the point-level naturality is now PROVED from one clean register spec
`weilPairingEval_mapPoint` (YRho.lean) is no longer a `sorry`. It is derived from the new
DS4 register entry **`weilPairing_torsionMapOfEllHom`** (the Weil pairing commutes with the
cartesian torsion square of an `Ell/ℚ`-morphism = KM 2.8.4.2, the *curve*-direction companion
of the registered `weilPairingEval_restrict`), via `pointToTorsion_mapPoint` +
`muNPointsEquiv_mapAlong`. The yRho cone's Weil-pairing dependency is now exactly the DS4
register (data + specs), as the design intends.
**Still open (chapter-scale)**: the DS4 construction itself. Assessment unchanged — mathlib
has no Weil pairing at all; HasseWeil's `weilPairing` (`HasseBound/WeilPairing/Pairing.lean`,
sorry-free) is function-field-theoretic over an *algebraically closed field* for
`WeierstrassCurve.Affine.Point`, so even M1 (field bases) needs: Weierstrass-model dictionary
(`modelPointAddEquiv`/`affineSectionSpecPoint`, present) + Galois equivariance + finite-étale
descent to a `k`-morphism `E[N]×E[N] ⟶ μ_N`, and it would still not discharge the register,
which is stated over an arbitrary base.

## G4 — shell complete; the remaining algebraic gap is mathlib-absent regular-local theory
`yRho_geometricallyIrreducible_of_connected` (T-G4c) and `connectedSpace_quotient_orbitRel`
(T-G4b) are proved; `irreducibleSpace_of_connected_of_disjoint_irreducibleComponents`
(T-G4a-SUB3, `ForMathlib/IrreducibleConnected.lean`) is proved. The single remaining
algebraic leaf `irreducibleSpace_of_connectedSpace_of_smooth` needs
**smooth ⟹ regular local ⟹ domain**. Mathlib status checked this session:
`Mathlib/RingTheory/RegularLocalRing/Defs.lean` is the *only* file — it has the definition,
`iff_finrank_cotangentSpace`, `of_ringEquiv`, and nothing else. "Regular local ⟹ domain"
(Matsumura 14.3: induction on `dim`, prime avoidance for `x ∈ 𝔪 \ (𝔪² ∪ ⋃ minimal primes)`,
`dim R/xR = dim R − 1`, then `xR` prime + Nakayama on `𝔭 = x𝔭`) and "smooth over a field ⟹
regular local" are both from-scratch developments here. Ticket them as their own stream
(`T-REG-*`) — they are the honest prerequisite, not a leaf.

## T-REG — the regular-local stream (started this session)

New file `ForMathlib/RegularLocalDomain.lean` (sorry-free). Landed:
* **T-REG-1** `isField_of_isRegularLocalRing_of_ringKrullDim_eq_zero` (+ the `IsDomain`
  corollary) — the base case.
* **T-REG-2** `exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes` — the regular
  parameter, by prime avoidance against `𝔪²` and the (finitely many) minimal primes.
* **T-REG-3a** `ringKrullDim_le_ringKrullDim_quotient_span_singleton_succ` — the dimension
  half of the `R/xR` step.
* **T-REG-4** `isDomain_of_isPrime_span_singleton` — the closing Nakayama step.

**T-REG-3b LANDED** (`spanFinrank_map_maximalIdeal_succ_le`), by an elementary generator
count rather than the cotangent space: write `x = ∑ c_g g` over a minimal generating set
`G` of `𝔪`; some `c_{g₀}` is a unit (else `x ∈ 𝔪²`), so `𝔪 = span (x ∷ G \ {g₀})` and the
image of `G \ {g₀}` generates modulo `x`.

**T-REG COMPLETE**: `ModularCurves.IsRegularLocalRing.isDomain` (axioms
propext/choice/Quot.sound only) — the full Matsumura 14.3 induction, assembled from
T-REG-1/2/3a/3b/4 via the sandwich `d − 1 ≤ dim (R/xR) ≤ spanFinrank 𝔪̄ ≤ d − 1`.

**Remaining for T-G4a**: the other half — *smooth over a field ⟹ the local rings are
regular* (Jacobian criterion from `IsStandardSmoothOfRelativeDimension`), then
`IsRegularLocalRing.isDomain` gives unique minimal primes, hence disjoint irreducible
components (`hdisj`) and — with local noetherianity — `hlf`, discharging
`irreducibleSpace_of_connectedSpace_of_smooth`. Superseded plan (kept for reference): (`spanFinrank (maximalIdeal (R ⧸ span{x})) ≤ dim R − 1` for
`x ∈ 𝔪 \ 𝔪²`), i.e. *x is part of a minimal generating set of `𝔪`*: choose a `k`-basis of
`𝔪/𝔪²` containing `x̄ ≠ 0` (`Basis.extend`), lift it (Nakayama: spanning mod `𝔪` ⟹
spanning), and drop `x`; the images of the other `d − 1` generate `𝔪̄`. Then the sandwich
`d − 1 ≤ dim (R/xR) ≤ spanFinrank 𝔪̄ ≤ d − 1` (T-REG-3a +
`ringKrullDim_le_spanFinrank_maximalIdeal`) gives both `IsRegularLocalRing (R/xR)` and
`dim (R/xR) = d − 1`, and T-REG-1/2/4 close the induction:
`IsRegularLocalRing R → IsDomain R`. After that, T-G4a needs the second half
(smooth over a field ⟹ the local rings are regular — Jacobian criterion via
`IsStandardSmoothOfRelativeDimension`), which is a separate stream.

## T-G3b — progress this session (bricks 1–4 landed; 5 blocked on elaboration, not on math)

* **Brick 1–2** (`Moduli/LevelLocusNatural.lean`, sorry-free): pinning of
  `fullLevelLocusPointsEquiv` (`_fst/_snd_comp_fst`), its naturality in `T`
  (`_natural_fst/_snd`), `section_ext_comp_fst`, `pullSection_pullbackAlongMap_comp_fst`,
  and the **level component of the funnel naturality square**
  (`fullLevelLocusPointsEquiv_pullSection_fst/snd`).
* **Brick 3** (`Moduli/LegendreDeltaRelRep.lean`): `legendreFunnelEquiv` — the classifying
  family as a standalone `def` (inside a `RelRepData` literal it overflows `whnf`) — with
  its pinning lemma `legendreFunnelEquiv_apply` (`rfl`).
* **Brick 4**: `gammaFullNaiveProblem_map_apply`, `legendreDeltaProblem_map_apply` (both
  `rfl`) so the naturality proof never has to `whnf` through the `↾`-coerced functor maps.
* **Brick 5 (open)**: with the above, funnel naturality is *exactly* the level square
  (proved) plus the `ω` square (`spec_nat`, the strengthened `ScaleTorsorData` field).
  Assembling them via `Subtype.ext`/`Prod.ext` currently overflows `whnf` at 200k
  heartbeats; heartbeat bumps are forbidden here, so the fix is the stall-playbook route:
  one fully-explicit top-level lemma per component, then `Prod.ext`.
* **Brick 6 (open)**: change `ScaleTorsorData.spec` to `Nonempty (bundled family)` (equiv +
  `spec_nat`), keep `scaleTorsor_spec`'s Prop-`sorry` with the stronger shape, re-found
  `legendreDeltaData` on the resulting `RelRepData`, and delete
  `legendreDelta_exists_naturalFamily`.

### T-G3b RESOLVED (2026-07-25, same session)

`legendreDelta_exists_naturalFamily` **no longer exists**. The interface fix was carried
out in full:

* `ScaleTorsorSpec` (new, `Moduli/SqrtCoverGlue.lean`) bundles the classifying family with
  its naturality square (congr-friendly form: the restricted locus point and section are
  passed with the equations identifying them, so no dependent rewrite across
  `(k ≫ h) ≫ q = k ≫ (h ≫ q)` is ever needed);
  `ScaleTorsorData.spec : Nonempty (ScaleTorsorSpec …)`; `scaleTorsor_spec` keeps its
  Prop-`sorry` in the stronger shape (still the single geometric residual of this leg).
* `legendreFunnelEquiv` + `legendreFunnelEquiv_apply/_apply_fst/_apply_snd` (all `rfl`),
  `legendreFunnelEquiv_nat_level` (from `Moduli/LevelLocusNatural`),
  `legendreFunnelEquiv_nat_omega` (from `ScaleTorsorSpec.nat`), and
  `legendreFunnelEquiv_nat` — all sorry-free, no heartbeat bumps.
* `legendreDelta_relRepData_of_scaleTorsor` / `legendreDelta_relRepData_finiteEtale`
  produce a genuine `RelRepData` (with `nat`); `legendreDeltaData` is its `.choose`, and
  `legendreDeltaZ/F/isFinite/etale/eqv` are re-founded on it.
* Bootstrap's `legendreDelta_relativelyRepresentable_finiteEtale` re-derived.

Remaining sorries on the Legendre leg: `exists_scaleTorsorData` (the honest geometric
input, quarantined subtree) and the two documented non-goals `legendreDeltaGAction`,
`legendreDelta_torsor_of`.

## ★ DISCOVERY (2026-07-26): the yRho cone can be re-plumbed off the quarantined Legendre leg

`#print axioms` checks run this session:

* `exists_levelThreeTorsorData` — **axiom-clean** (propext/choice/Quot.sound only).
* `exists_levelFourTorsorData` — **axiom-clean**.

So both the level-3 and the level-4 rigidifiers are *fully proved*, while the Legendre
rigidifier still rests on `exists_scaleTorsorData` (quarantined subtree). The smoothness
leaf `rhoProblem_smoothOfRelativeDimension_one` consumes the cover only through

* `rL : (cover problem).RepresentableBy (universal object)`,
* `dL : RelRepData (cover problem) X` + finite + étale + **surjective**,
* `dρ : RelRepData (rhoProblem D) (universal object)` + finite + étale
  (`rhoProblem_exists_relRepData_finiteEtale`, generic in the object), and
* `ModuliProblem.prodUniqueUpToIso` (generic), plus the ONE base-specific input
  `<base> is standard smooth of relative dimension 1 over ℚ`
  (`legendreModuliRing_isStandardSmoothOfRelativeDimension`).

**Therefore**: swapping the Legendre cover for the level-3 cover removes
`exists_scaleTorsorData` — and the whole quarantined subtree — from the `yRho_representable'`
cone, leaving **DS4 as the only register**. The single missing brick is

> `Algebra.IsStandardSmoothOfRelativeDimension 1 R (E3ModuliRing R)` (for `3` invertible).

`E3ModuliRing R = Localization.Away (e3Delta) of R[β,γ]/(β³ − (β+γ)³)` — a **hypersurface**,
which is exactly the shape of `ForMathlib/StandardSmoothHypersurface.lean`
(`isStandardSmoothOfRelativeDimension_away_pderiv`). The Jacobian computation:

* `f = β³ − (β+γ)³`, so `∂f/∂γ = −3(β+γ)²`;
* the flex relation gives `γ·(3β² + 3βγ + γ²) = 0`, i.e. with `s := β + γ`,
  `γ² = s·(3γ − 3s)`, so **`s ∣ γ²`**; since `γ ∣ e3Delta`, `s ∣ e3Delta²`, hence `s` — and
  therefore `∂f/∂γ = −3s²` — is a **unit** in `E3ModuliRing` (`3` invertible).

Assembly: `IsLocalization.Away (e3Delta · ∂f/∂γ) (E3ModuliRing)` (by
`IsLocalization.Away.mk`, using that `∂f/∂γ` is a unit there), hence `E3ModuliRing` is
`IsLocalization.Away (algebraMap _ _ e3Delta)` over `Localization.Away (∂f/∂γ)` up to a
canonical `A`-algebra iso (`IsLocalization.algEquiv` + `IsLocalization.Away.mul`), and
`IsStandardSmoothOfRelativeDimension.trans` (`0 + 1`) with
`isStandardSmoothOfRelativeDimension_away_pderiv` finishes it. Then mirror
`rhoLegendre_total_isStandardSmooth` at level 3 and re-point `exists_representsYRho`.

### RE-PLUMBING DONE (2026-07-26)

`yRho_representable'` now runs on the **level-3** rigidifier:

* `Moduli/LevelThreeSmooth.lean` (new, sorry-free, axiom-clean):
  `e3S_mul_eq_gamma_cube`, `e3S_dvd_e3Delta_pow`, `isUnit_e3S_map`, `pderiv_one_e3Rel`,
  `isUnit_pderiv_e3Rel_map`, `isLocalization_away_e3Delta_mul_pderiv`, and
  **`e3ModuliRing_isStandardSmoothOfRelativeDimension`**.
* `ModularCurve/RhoSmooth.lean`: `rhoLevelThree_total_isStandardSmooth`,
  `levelThreeCover_isStandardSmooth`,
  `rhoProblem_smoothOfRelativeDimension_one_levelThree`.
* `ModularCurve/RhoPoints.lean`: `exists_representsYRho_levelThree`, and
  `yRho_representable'` re-pointed at it.

Consequence: **the quarantined Legendre subtree (`exists_scaleTorsorData`) is no longer in
the cone of the main theorem.** The Legendre route (`exists_representsYRho`) is kept as an
alternative. The remaining `sorryAx` in `yRho_representable'` comes from the **DS4
Weil-pairing register**, which is inherent to the *definition* of `rhoProblem` (its
`RhoLevelStructure` objects carry the pairing clauses) — i.e. the only unproven input is
now the deliberate construction-of-record.

Board after this session: DS4 construction (chapter-scale), T-SMOOTH-REG (blocked behind
dimension theory of f.g. algebras — its reusable core
`isRegularLocalRing_of_flat_of_map_maximalIdeal` is landed), and T-G4-CORE (MAJOR-INFRA).

### DS4 M1a DONE (2026-07-26)

`ModularCurves/WeilPairing/FieldPairing.lean` (new, sorry-free, **axiom-clean**) exposes
AINTLIB's own HasseWeil pairing in the DS4 specification shape:

* `fieldWeilPairing W N hN P Q hP hQ : {u : F // u ^ N = 1}` for `F` algebraically closed,
* `fieldWeilPairing_mul_left` / `_mul_right` (T-C2 shape), `_self` / `_antisymm` (T-C3
  shape), `_eq_zero_of_forall` (nondegeneracy).

So **over algebraically closed fields the Weil pairing is not a register at all** — the
DS4 gap is exactly the passage from geometric fibres to a morphism of schemes over a
general base. Remaining M1 bricks:

* **M1b** — Galois equivariance of `fieldWeilPairing` under `Gal(k̄/k)` (transport of the
  construction along field automorphisms; the HasseWeil side has
  `FrobeniusDivisorGalois`/`DivisorGalois` material to reuse).
* **M1c** — descend to a `k`-morphism `E[N] ×_k E[N] ⟶ μ_{N,k}` (finite étale descent;
  the project has `exists_finiteEtaleHom_of_galoisEquivariant`), then compare with the
  register (`T-C4`, `WeilPairing/FibreComparison.lean`).
* **M2** — the general base (KM 2.8 / GME 2.6.4 chain).

**M1b/M1c gating (checked 2026-07-26)**: `WeilPairing/EtaleDescent.lean` already contains the
descent packaging `exists_pairingAlgebraHom_of_galoisEquivariant` (input: a
`Gal(k̄/k)`-equivariant map on fibre-functor values; output: the scheme morphism
`E[N] ×_k E[N] ⟶ μ_N`), and its own note records that `tensorAlgHomPairEquiv` and
`exists_finiteEtaleHom_of_galoisEquivariant` are axiom-clean while `sorryAx` enters only
through **`torsionAlgebra`**. So feeding `fieldWeilPairing` into it needs, first, the
`torsionAlgebra` ↔ affine-Weierstrass-points dictionary at `k̄`-fibres — that (not the
pairing) is the next real leaf of the field-level DS4 construction.

### DS4 M1b progress (2026-07-26, later)

Landed, all sorry-free and axiom-clean:

* `WeilPairing/FieldPairing.lean` — `fieldWeilPairing` + the DS4-shaped specs (M1a) and
  `fieldWeilPairing_congr`.
* `WeilPairing/FibrePointDict.lean` — `chartAffinePointEquiv` (scheme points at a
  geometric fibre ↔ affine Weierstrass points, via `chartPointsEquiv` ∘
  `modelPointAddEquiv`) and `fibreWeilPairing` with bilinearity / alternation /
  nondegeneracy (M1b-1/2).
* `WeilPairing/GaloisFunctionField.lean` — the Galois transport chain for an **arbitrary**
  base field and an **arbitrary** `σ : L ≃ₐ[k] L` (HasseWeil proves only the Frobenius case
  and only over finite fields): `coordRingMap_surjective/bijective_of_ringEquiv`,
  `map_algEquiv_baseChange_eq`, `galoisCoordRingEquiv`, `galoisFunctionFieldEquiv`,
  `map_maximalIdealAt_galoisCoordRingEquiv` (3b-i), `pointOnMappedGal`,
  `pointValuation_galoisFunctionFieldEquiv` (3b-ii).

Remaining chain to the field-level DS4 pairing:

* **3b-iii** `ordAtInfty` transport — port `ordAtInfty_ffFrobEquivRaw` /
  `ordAtInfty_frobeniusFunctionFieldEquiv`. *Shortcut worth trying first*: principal
  divisors have degree `0`, so once the affine part of `div(Φ_σ g)` matches
  `div(g_{σ·})`, the `∞`-order is forced — this avoids porting the ~60-line
  `ordAtInfty` computation.
* **3b-iv/v** `ord_P` and `projectiveDivisorOf` transport ⟹ `div(Φ_σ g_T) = div(g_{σT})`.
* **3b-vi** the pairing equivariance `e(σS, σT) = σ(e(S,T))`, from
  `Constancy.pairing_const_of_transport` (`Φ_σ g_T = c·g_{σT}`), `Φ_σ ∘ τ_S = τ_{σS} ∘ Φ_σ`,
  and uniqueness of the pairing constant.
* **M1c** — feed the result into `exists_pairingAlgebraHom_of_galoisEquivariant`
  (`WeilPairing/EtaleDescent.lean:440`) through `torsionAlgebraPointsEquiv`; note that
  equivalence is currently only `Nonempty`-valued, so its Galois equivariance has to be
  exposed as part of this step.
