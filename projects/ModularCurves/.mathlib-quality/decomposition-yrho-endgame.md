# Decomposition: the Y(ρ̄) endgame (existence + geometric irreducibility, N composite)

Date: 2026-08-10. Goal restated by the owner: Y(ρ̄) for ρ̄ : Gal(ℚ̄/ℚ) → GL₂(ℤ/N)
continuous, N ≥ 3 (composite allowed), det ρ̄ = mod-N cyclotomic χ (⟹ the pairing datum
on V_ρ̄), parametrising E/S with a Weil-pairing-compatible iso E[N] ≅ V_ρ̄; geometrically
irreducible over ℚ; plus the N = 3 case. ChatGPT 5.6-sol (max) validation: consultation
#4 (E5-ℚ route + irreducibility routes), recorded below.

## R1 scan verdict (2026-08-10)

**The statement layer is DONE and matches the owner's formulation exactly.**
`GaloisRepData N` (YRho.lean:122) = continuous ρ + `det_cyclo` (det = χ via mathlib's
`modularCyclotomicCharacter`) + the pairing normalisation `p` (DERIVED from det = χ,
`GaloisRepData.ofDetCyclo`, T-G1 proven). `RepresentsYRho` is the pairing-compatible
moduli predicate (Buzzard Lecture 8 p. 33 verbatim in the module docstring). N is
arbitrary `[NeZero N]` with `hN : 3 ≤ N` only where representability needs it. Nothing
assumes N prime. **N = 3 is included in every general statement** (the level-three
rigidifier `exists_representsYRho_levelThree` is proven and consumed at `hN : 3 ≤ N`).

**Leg 1 (representability).** `yRho_representable` (RhoPoints.lean:321) — full
sorry-carrier walk (108663 constants): rests on EXACTLY THREE sorried decls:
1. `ModularCurves.weilPairing_torsionMapOfEllHom` (YRho.lean:2489) — KM 2.8.4.2
   curve-direction base-change compat. `EllHom` IS a cartesian square + zero-compat
   (EllCategory.lean:64), and the base-direction engine `weilPairingKM_restrictBase`
   (KMNaturality.lean:873) is PROVEN — this is a wiring ticket, not new mathematics.
2. `EllipticCurve.weilPairingEval_self` (E4a) — in progress on the validated U5 plan
   (see `decomposition-e4a-self.md` + U5 subsection; bridge `functionFieldMap_translateBy`
   axiom-clean 2026-08-10; L2a/L2b/L2c proven; remaining: L1 divisor dictionary + L3–L6
   + assembly).
3. `EllipticCurve.weilPairingEval_nondegenerate` (E5) — see the ℚ-route below.

**Leg 2 (geometric irreducibility).** `yRho_geometricallyIrreducible` (YRho.lean:8744,
sorry). The T-IRR0 shell is PROVEN (IrreducibilityScoping.lean: L1
`irreducibleSpace_of_connectedSpace_of_smooth`, L4, and the MASTER reductions
`yRho_geometricallyIrreducible_of_connected(')` — conditional on `hconn`). The core =
`hconn`: geometric connectedness of Y ⊗ ℚ̄.

**Bonus finding.** `FibrewiseElliptic.locallyWeierstrass` AND
`locallyWeierstrass_iff_abstractConditions` are **PROVEN, AXIOM-CLEAN** — the
fibrewise-⟺-LocallyWeierstrass comparison strand (T-W-cmp/T-A7-cmp) is COMPLETE; no
planning needed.

## Decision points for the owner (blocking ticket creation)

**D1 — register re-clothing (the board's own flagged statement decision, 2026-08-04).**
Restate the two remaining register entries (`weilPairingEval_self`,
`weilPairingEval_nondegenerate`) over ℚ-algebra bases (equivalently `NIsInvertible S N`),
matching every consumer on the Y(ρ̄) path. RECOMMENDED: yes. Effect: E5 drops from
Cartier-duality-gated (AG-CD, multi-month) to the validated finite-étale route below;
E4a's universal-base leg simplifies (the ℚ-atlas is smooth over ℚ hence reduced — no
ℤ-flatness/B↪B[1/N] step). Full-generality versions can return later as a separate
AG-CD stream without blocking Y(ρ̄).

**D2 — irreducibility route.** (a) Minimal-analytic (RECOMMENDED, validated): no GAGA,
no analytification functor — see the shrunken tree below. (b) Igusa 1959 algebraic
(generic division fields, Gal(K_N/k(j)·Ku) ≅ SL₂(ℤ/N)/±1) — genuinely algebraic, also
major-stream-sized; kept as the recorded alternative.

**D3 — "3 done".** N = 3 is already covered by the general statements. If the owner
means an explicit worked instance (a concrete mod-3 ρ̄ with its Y(ρ̄), e.g. from the
3-torsion of a given curve — the FLT-adjacent use), that is one small additional
instantiation ticket [YR-5]; please confirm the intent.

## Leg-1 tickets

- **[YR-1] `weilPairing_torsionMapOfEllHom`** (wiring, MEDIUM). Route: an `EllHom` g is
  a cartesian square, so `A.curve ≅ (B.curve).baseChange g.baseHom` as records
  (pullback-transport already used by RhoSmooth/EllCategory machinery); push
  `weilPairingKM_restrictBase` (proven) through `weilPairingEval_eq_weilPairingKM`
  (proven) on both sides; the μ_N-leg is `muNMapAlong`-naturality (`muNPointsEquiv`
  naturality lemmas exist — `muNPointsEquiv_mapAlong` cited at YRho:2495 as proven).
  Source: KM 2.8.4.2 "the pairing commutes with base change".
- **[YR-2] E4a per the standing validated plan** (`decomposition-e4a-self.md` U5
  subsection). Under D1 = yes: U4 simplifies to the ℚ-atlas (smooth ⟹ reduced; N
  invertible globally); the U5 field-leaf comparison (in progress) is unchanged and
  load-bearing.
- **[YR-3] E5 over ℚ-algebras** (validated route, consultation #4 Q1):
  - YR-3a: the restricted internal Hom `G^{∨N} := Hom-gp-scheme(E[N], μ_N)` as a finite
    étale S-group scheme, étale-locally `μ_N × μ_N`, rank N². Infra: internal Mor of
    finite étale schemes is finite étale (Stacks 58.5.2/58.5.4) + equalizers for the
    hom-condition. THE one genuinely new piece.
  - YR-3b: the pairing-induced map `E[N] → G^{∨N}` (functorial from `weilPairingEval`).
  - YR-3c: fibrewise-iso ⟹ iso for finite locally free (Stacks 10.79.4(3); in Lean:
    `Scheme.Hom.isIso_iff_finrank_eq` (mathlib FlatRank.lean:273) + our
    `natCard_sections_eq_finrank` (ForMathlib/EtaleSectionsCount.lean:143);
    template: Moduli/LevelThreeTorsor.lean:607).
  - YR-3d: the geometric-fibre case = classical nondegeneracy over an algebraically
    closed char-0 field: import via `fieldWeilPairing_eq_zero_of_forall`
    (FieldPairing.lean:103) + the T-C4 comparison (= the SAME comparison the E4a-U5
    work is building — shared substrate, do E4a first). Injective + equal orders N²
    ⟹ bijective on fibres.
- **[YR-4] assembly**: re-clothed register entries discharged; `yRho_representable`
  goes axiom-clean end-to-end.

## Leg-2 tickets (route D2a — the shrunken analytic core)

Validated shrinkage (consultation #4 Q2): NO general analytification functor, NO GAGA,
NO π₀-base-change. The tree:
- **[IRR-1] Euclidean topology on X(ℂ)** for finite-type ℂ-schemes (affine: closed
  subspace of ℂⁿ; glue along opens) + "nonempty finite-type ℂ-scheme has a ℂ-point"
  (Nullstellensatz, in mathlib). Check mathlib-current for existing complex-points
  topology before building.
- **[IRR-2] Euclidean-connected ⟹ Zariski-connected** for finite-type ℂ-schemes:
  a nontrivial clopen decomposition Y = U ⊔ V gives Y(ℂ) = U(ℂ) ⊔ V(ℂ) Euclidean-clopen
  with both pieces nonempty (IRR-1). Small.
- **[IRR-3] THE CORE: a continuous surjection ℍ → Y(N)^ζ(ℂ)** (Euclidean topologies):
  the classical parametrisation τ ↦ (ℂ/⟨1,τ⟩, basis (τ/N, 1/N) of N-torsion, ζ-pinned
  pairing). This is the LeanModularForms-bridge item — the only genuinely analytic
  brick. Sub-develop before execution (needs: Weierstrass-℘ ↦ the plane-curve ℂ-point,
  continuity in τ, surjectivity = every (E, level structure)/ℂ arises — uniformisation
  of complex elliptic curves).
- **[IRR-4] descent ℂ → ℚ̄**: Y_ℂ → Y_ℚ̄ surjective + continuous image of connected.
  Trivial given IRR-1.
- **[IRR-5] twist transfer**: over ℚ̄ a symplectic trivialisation of V_ρ̄ identifies
  Y(ρ̄)_ℚ̄ ≅ Y(N)^ζ_ℚ̄ (the RhoDescent/RhoSections machinery already holds the
  torsor-transport; check what exists at execution). Then `hconn` feeds the PROVEN
  master reduction and [IRR-6] closes `yRho_geometricallyIrreducible`.

## Execution order

YR-1 (unblocks nothing but is quick + de-risks the register wiring) → E4a completion
(YR-2, in progress) → YR-3 (E5-ℚ; reuses E4a's T-C4 comparison) → YR-4. In parallel:
IRR-1/2 (mathlib-adjacent, independent) and the IRR-3 sub-develop. D1/D2/D3 answers
gate the board update.

## YR-3a design recon (2026-08-11)
Objects: `E.torsion N` (Torsion.lean:61, over S via torsionpi, group structure via the
kernel square) and `muNGrpObj` (MuN.lean:289). Internal-Hom target: a finite etale
S-scheme representing T -> Hom-gp-sch(E[N]_T, muN_T). Stacks route: 58.5.2 (Mor-scheme of
finite etale is finite etale) + 58.5.4 + equalizers for the hom-condition (finite limits
of finite etale stay finite etale). Statement-draft belongs in a new
WeilPairing/EtaleDual.lean; FIRST grep MorScheme/internalHom in ForMathlib
FiniteEtaleFundamentalGroup + EtaleDescent + GaloisFibre for an existing internal-Mor
constructor before building.

YR-3a reuse-check NEGATIVE (2026-08-11): no internal-Mor/Hom-scheme constructor in
ForMathlib/{FiniteEtaleGalois,FiniteEtaleFundamentalGroup,FiniteEtaleFiberFunctor} or the
WeilPairing Galois layer — YR-3a builds it fresh per the Stacks 58.5.2/58.5.4 route, as
the endgame plan anticipated. Available substrate: the fiber-functor equivalence
(FiniteEtaleFiberFunctor) for the geometric-fibre computations of YR-3c/d.

YR-3a design insight (2026-08-11, final): the tree's finite-etale layer is ALGEBRA-side
(CommAlgCat + mathlib CategoryTheory.Galois). Better than scheme-side Stacks 58.5: build
the restricted dual as the Hom-object of finite G-SETS through the fiber-functor
equivalence (FiniteEtaleFiberFunctor) — Hom-objects of finite G-sets are elementary
(conjugation action on function-sets), and the equivalence transports representability +
rank + the pairing map. The YR-3 statement should be clothed over the base field/its
etale site accordingly (matching the D1 re-clothing). Cut on next execution: (i) G-set
Hom-object + its rank; (ii) transport across the equivalence; (iii) the pairing-induced
map and fibrewise-iso (existing isIso_iff_finrank_eq route); (iv) the field-nondegeneracy
import.

YR-3a substrate detail: FiniteEtaleFiberFunctor.lean carries the limit-preservation
kit (isLimitMapConeProductFan, isColimitMapCoconeSpanPushout, isLimitMapConeFixedPoints,
injective_of_mono) — the transport toolkit for the G-set Hom-object; the equivalence
itself rides mathlib's PreGaloisCategory framework (Galois.Basic imports in
FiniteEtaleGalois). Execution starts from mathlib's `CategoryTheory.Galois` fiber-functor
essentially-surjective/full-faithful theorems.

YR-3a entry CONFIRMED LIVE: `instance : PreGaloisCategory (CommAlgCat.FiniteEtale k)op`
already PROVEN in-tree (FiniteEtaleGalois:694, AG-GG-1). The Hom-object construction
starts directly on this instance + mathlib GaloisCategory.getFiberFunctor. All YR-3a
prerequisites verified present; execution is unblocked.
