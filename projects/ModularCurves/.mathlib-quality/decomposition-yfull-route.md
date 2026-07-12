# STREAM-YFULL — the Y(N) representability route (T-E9): decomposition + ROUTE DECISION

*(/develop --decompose Phase 1e, adversarial; 2026-07-08. Worker: STREAM-YFULL.)*

**Target**: `gammaFullNaive_representable` (`Moduli/Representability.lean:264`, HELD): for
`N ≥ 3`, `N` invertible in `R`, the naive full-level problem `[Γ(N)]` is **rigid** and
**representable**, and every representing object has **smooth affine** base over `Spec R`.

**Skeleton**: `ModularCurves/ModularCurve/YFullRoute.lean` — **builds green**
(`lake build ModularCurves.ModularCurve.YFullRoute`, 2026-07-08): 13 sorried leaves,
5 real wirings, 2 real defs; registered in `ModularCurves.lean`.

**Sources read in full**: [Loe] = `refs/ModularCurves/modcurvesnotes.pdf` §3.7–3.8 (p. 18–19;
extraction lines 1060–1160); [KM] = `refs/ModularCurves/katz-mazur-arithmetic-moduli-FULL.pdf`
(PDF page = print + 11): SCHOLIE 4.7.0 + engine, print pp. 111–116 (PDF 122–127); Cor 4.7.1
pp. 116–117; Cor 4.7.2 p. 117; Cor 2.7.2 pp. 85–86 (PDF 96–97); Thm 3.7.1 pp. 104–105
(PDF 115–116); 3.6.0 p. 102; First Main Theorem 5.1.1 + 5.2 p. 129 (PDF 140).

---

## 1. The two routes, in prose

### 1.1 ROUTE A — via the (freshly amended, ⇐-affine) T-E5 = KM SCHOLIE 4.7.0

This is KM's own proof of Cor 4.7.2 and Loeffler's proof of §3.8's representability claim.

**KM 4.7.2** (print p. 117, verbatim):
> "COROLLARY 4.7.2. For N ≥ 3, the naive level N moduli problem of 4.6 is representable, by a
> smooth affine curve Y(N) over Z[1/N].
> Proof. This results from 4.7.1 above, thanks to the rigidity 2.7.2 and the relative
> representability 3.7.1 of naive level N structures. Q.E.D."

So the route has exactly three inputs, each a chapter-level citation in KM:

**(i) Relative representability, affine (and étale) over (Ell).**
KM 3.6.0 (print p. 102): *"Each of these functors is represented by a finite S-scheme."*
KM 3.7.1 (print p. 104): *"Let N ≥ 1 … S a scheme on which N is invertible … Each is
represented by a finite etale S-scheme"*, proved by étale-local constancy (p. 105: *"reduce to
the case when E[N] is the constant group-scheme (Z/NZ)²"*). Loeffler Prop 3.8.2 (verbatim):
> "PH is relatively representable and étale over Ell/Z[1/N] … For H = {1} … it is an open
> subscheme of E[N] ×_S E[N] given by non-vanishing of Weil pairings."

**In-repo realization**: the project already owns the *closed* presentation — `levelSpaceΓ`
(`Moduli/LevelSpaces.lean`, T-D16/T-D18 chain, `exists_fullLevelLocus`,
`LevelStructure/Incidence.lean:2569`, file sorry-free) — KM's divisor-equality register
(KM 3.1). Its factorizations are **Drinfeld** structures (`levelSpaceΓ_spec`); the **naive**
problem is reached through T-D8 (`isFullLevel_iff_naive`, real modulo the T-D8-bridge box
`fullLevel_divisor_iff_naive_gen`). Affineness of the presentation is free
(closed immersion ≫ pullback-of-finite ≫ finite, `torsionπ_isFinite` PROVEN); étaleness needs
`torsionπ_etale` (⟸ BB-DIFF, sorried) **plus the one genuinely new geometric leaf of this
stream**: the full-level locus is *clopen* in `E[N] ×_S E[N]` ([YF-CLOPEN] below — Loeffler
cuts it open by Weil pairings; KM cuts it closed and proves openness by étale constancy).

**(ii) Rigidity.** KM 2.7.2 (print p. 85, verbatim):
> "COROLLARY 2.7.2 (Rigidity of level N structures). Let ε: E → E be an automorphism of an
> elliptic curve over a connected base S. Let N ≥ 2 be an integer, E[N] the scheme-theoretic
> kernel of N. Suppose that ε induces the identity automorphism of E[N]. (1) If N ≥ 3, then
> ε = id."
Proof (pp. 85–86): ε − 1 kills E[N] ⟹ ε = 1 + gN; then trace(ε) = 2 + N·tr(g),
deg(ε) = 1 + N·tr(g) + N²·deg(g); deg(ε) = 1 and |tr(ε)| ≤ 2 force |N²·deg(g)| ≤ 4, so N ≥ 3
gives deg(g) = 0, g = 0, ε = 1. Loeffler Prop 3.8.3 states the criterion for general H over
`Ell/R[1/6]` (H = {1}: the preimage is Γ(N) ⊂ SL₂(ℤ), torsion-free and −1-free for N ≥ 3);
KM 2.7.2 has **no characteristic restriction** (connected base only), which is what T-E9's
`R ⊇ ℤ[1/N]` statement needs in residue characteristics 2, 3.
**In-repo realization**: the linchpin `aut_trivial_of_fullLevel` (`Moduli/Groupoid.lean:161`,
GME 2.6.4 register = the same computation) — proven modulo `torsionFixed_of_fixesLevel`
(:96, E[N] finite-étale descent) and the `aut_endo_eq_one` degree engine
(`EllipticCurve/EndomorphismDegree.lean`, deg/trace boxes sorried) — CHARTER-P3B3 milestone 2
territory. Delta: the linchpin carries `[IsLocallyNoetherian S]`, absent from both KM 2.7.2
and the moduli statement ⟹ isolated gate [YF-NOETH].

**(iii) The engine.** KM SCHOLIE 4.7.0 (print p. 111, verbatim):
> "Let 𝒫 be relatively representable and affine over (Ell); then a necessary and sufficient
> condition that 𝒫 be representable is that 𝒫 be rigid."
Proof (pp. 111–116, read in full): ⇒ is 4.4 (= T-E5a, PROVEN in-repo). ⇐: it suffices to
represent 𝒫 over ℤ[1/2] and ℤ[1/3] and glue by rigidity over ℤ[1/6] ("recollement");
axiomatized claim (p. 112): for δ relatively representable, affine, representable by an affine
ℤ[1/N]-scheme, with G-action making each δ_{E/S} a finite étale G-torsor, *"over Z[1/N], 𝒫 is
represented by the affine Z[1/N]-scheme 𝕸(𝒫,δ)/G"* — applied at
(2, Legendre, GL(2,ℤ/2)×{±1}) and (3, naive level 3, GL₂(𝔽₃)). Engine steps: 𝕸(𝒫,δ) = 𝒫_{E/𝕸(δ)}
(simultaneous problem) is absolutely affine; rigidity ⟹ θ(g) unique ⟹ cocycle ⟹ free action;
affine ⟹ quotient exists, π_univ finite étale G-torsor (SGA III V 4.1); (E, α_univ) descends
(p. 114: *"Because E is projective, via I⁻¹(0), it descends, and because 𝒫 is relatively
affine, α_univ descends (SGA I, Exp VIII, 7.8, 1.2 and 1.7)"*); the descended pair represents 𝒫
by the torsor argument (pp. 114–116).
**In-repo realization**: `representable_iff` (`Moduli/EllCategory.lean:274`) is KM 4.7.0
**verbatim** after the B2 amendment (v10.27 decision (a): hypothesis `P.AffineOverEll`); its
single `sorry` (the ⇐) is **CHARTER-FP4's milestone**: engine `representable_of_rigid_of_torsor`
(T-Q6e; `simul_representable` + free action PROVEN; torsor half of A7.1.1 PROVEN; object
descent DISSOLVED by route (a) = quotient of the universal curve, [T-E5c-ROUTE-A] verdict)
+ T-E15 (ℤ[1/3] bootstrap) + T-E14 (Legendre, ⟸ T-E-OMEGA ⟸ T-W7.1b, CHARTER-A) + T-E5f
recollement. **This stream cites it and never rebuilds it.**

**(iv) The geometric conjuncts.** KM 4.7.1 (print p. 116, verbatim):
> "COROLLARY 4.7.1. Any relatively representable moduli problem 𝒫 which is affine and etale
> over (Ell), and rigid, is representable by a smooth affine curve over Z.
> Proof. By 4.7.0, 𝒫 is representable by an affine, and we have
> 𝕸(𝒫)⊗Z[1/2] = 𝕸(𝒫, Legendre)/(a finite group acting freely),
> 𝕸(𝒫)⊗Z[1/3] = 𝕸(𝒫, naive level 3)/(a finite group acting freely).
> Therefore it suffices to prove that 𝕸(𝒫, Legendre) is a smooth curve over Z[1/2], and that
> 𝕸(𝒫, naive level 3) is a smooth curve over Z[1/3]. By hypothesis, 𝒫 is etale over (Ell), so
> that the morphisms 𝕸(𝒫, Legendre) → 𝕸(Legendre), 𝕸(𝒫, naive level 3) → 𝕸(naive level 3)
> are etale. This reduces us to checking that 𝕸(Legendre) and 𝕸(naive level three) are both
> smooth curves over Z, a fact which is obvious by inspection of their explicit defining
> equations (2.2.9, 2.2.11). Q.E.D."
i.e. smooth-affineness is read off the **engine's constructed object** (étale over the explicit
bootstrap curves; free finite quotient). It is NOT an abstract consequence of representability;
the current engine statement returns bare `P.Representable`. Hence the transport principle
[YF-TRANS] (all representing objects are canonically Ell-isomorphic; `Smooth`/`IsAffineHom`
respect isomorphism) + the existence leaf [YF-GEOM] (SOME representing object is smooth affine
— the KM 4.7.1 computation, discharged against CHARTER-FP4's construction, with this file's
[YF-ETALE] at the bootstrap object and the étale-descent-of-smoothness helper [YF-QSM]).

### 1.2 ROUTE B — direct, T-E7-style (rejected)

The would-be construction avoiding the engine, assembled from the classical picture:

*For N ≥ 4*: let (Y₁, E₁, P₁) represent the naive Γ₁(N) problem (T-E7 = Loeffler Def 3.3.6 +
Thm 3.4.4 — the universal marked Tate curve over `Spec R[A,B][Δ⁻¹]`, exact-order-N locus cut
by division polynomials, lower-order loci removed; now being planned by STREAM-Y1 in
`ModularCurve/YOneAssembly.lean`). A naive full level structure (P, Q) has P of fibrewise
exact order N (a basis vector of (ℤ/N)² has order N — elementary fibre lemma), so (E, P)
classifies by a map s : S ⟶ Y₁ together with a **unique** isomorphism s*(E₁, P₁) ≅ (E, P)
(uniqueness = Tate-normal-form uniqueness, T-E1 PROVEN, no Aut-theory needed for N ≥ 4).
Transport Q across it; then Y(N) := the fibre of `levelSpaceΓ E₁ N` over the P₁-section of the
first `E₁[N]`-factor represents [Γ(N)]: Hom(S, Y(N)) ≅ {(E,(P,Q))}/≅. Smooth: Y(N) clopen in
E₁[N] (finite étale over Y₁ — the SAME [YF-CLOPEN]+BB-DIFF gates as route A) ≫ Y₁ smooth
(T-E7's own conjunct); affine likewise (closed in finite over affine).
*For N = 3*: exact order 3 admits no Tate normal form (P is a flex); the explicit KM Ex. 2.2.2 /
GME 2.2.10 model is T-E15a — the same object route A's bootstrap needs.
*Rigid conjunct*: route B provides **nothing** — T-E9 asserts `Rigid ∧ Representable`, so the
entire rigidity chain (linchpin + [YF-NOETH]) is needed identically on both routes.

### 1.3 ROUTE RECOMMENDATION: **ROUTE A** — with the explicit gate comparison

| Gate | Route A | Route B | Owner today |
|---|---|---|---|
| Rigidity linchpin boxes (`torsionFixed_of_fixesLevel`, deg-engine) | needed (rigid conjunct + engine freeness) | needed (rigid conjunct) | CHARTER-P3B3 m.2 (active) |
| [YF-NOETH] locally-noetherian mismatch | needed | needed | NEW (this stream names it) |
| T-D8-bridge (`fullLevel_divisor_iff_naive_gen`) | needed | needed | CHARTER-P3B3 item 4 (active) |
| BB-DIFF ⟹ `torsionπ_etale` | needed (étale + 4.7.1) | needed (clopen + T-E7 3.4.4) | CHARTER-P3B3 m.1 (active) |
| [YF-CLOPEN] full-level locus clopen | needed | needed | NEW (this stream; 2 routes, one Weil-free) |
| T-E5 ⇐ engine (T-Q6e rt (a) + A711 + T-W7.1b) | **needed** | not needed | CHARTER-FP4 + CHARTER-A (active, own milestones) |
| T-E14 Legendre (⟸ T-E-OMEGA ⟸ T-W7.1b) | **needed** | not needed | CHARTER-A items 2–3 (active) |
| T-E15a explicit level-3 model | needed (bootstrap + 4.7.1) | needed (N = 3 case) | CHARTER-FP4 item 4 |
| T-E5f recollement | **needed** | not needed | CHARTER-FP4 |
| [YF-GEOM] geometric handle on the representing object | needed (engine object) | needed (T-E7 object — same problem) | NEW; discharge co-located with the construction owner |
| T-E7 full backbone (Tate atlas, div-poly loci, **[T-A6b] Abel enrichment**, T-W7 comparison) | not needed | **needed** | STREAM-Y1 skeleton (planned; T-A6b explicitly *deferred* on the board) |
| Γ₁-refinement wiring + N=3/N≥4 case split | not needed | **needed** | would be NEW |
| Reuse for T-H6 (general H) / T-E15b / KM 5.1.1 clauses | direct template ×3 | dead end | — |

**Verdict.** Both routes share every genuinely NEW leaf this stream must own ([YF-CLOPEN],
[YF-NOETH], the rigidity bridge, the D8 consumption, the points dictionary). They differ in
the backbone: route A rides the KM engine, **whose every gate is an active charter's own
milestone and lands with or without T-E9** (T-E5 is CHARTER-FP4's milestone; T-W7.1b/T-E-OMEGA
drive the W7 endgame in CHARTER-A); route B rides the T-E7 stack, which — even now that
STREAM-Y1 has planned it — passes through **[T-A6b] `abelEnrichment_exists`, the 7-box
Abel/Pic⁰ canonicity project the board explicitly defers**, plus new Γ(N)-specific wiring that
serves no other consumer. Route A's two inputs are, additionally, exactly (a) the **T-E15b
shape** (instantiate `fullLevelSpace` at the bootstrap ℰ₃ — feeds the engine's own axiom 2),
(b) the **T-H4/T-H6 template** (Loeffler proves general-H representability only through
Thm 3.7.4 = the engine; there is no direct route for general H), and (c) KM 5.1.1's
Γ(N)-relative clause ([YF-FIN] + [YF-ETALE]) for free. Route B under-produces all three and
still needs the whole rigidity chain. **Recommendation: ROUTE A**, executed in
`YFullRoute.lean`.

**Plan-improvement finding for the coordinator**: the board's T-E9 dependency line lists
"T-C1 (Weil-pairing open locus per Loeffler 3.8.2)". On the recommended route **T-C1 is NOT on
the critical path**: relative representability uses the PROVEN closed locus `levelSpaceΓ`; the
open half is the single leaf [YF-CLOPEN], which has a Weil-pairing-free discharge (KM 3.7.1's
étale-local constancy, route (β) below). T-C1 remains an *alternative* discharge (route (α)).

---

## 2. The decomposition tree (recommended route, as built in `YFullRoute.lean`)

```
gammaFullNaive_representable_assembly  (T-E9 statement, byte-mirrors the held target) [REAL ✓]
├─ Rigid conjunct: gammaFullNaive_rigid                     [sorry; GATE YF-NOETH]
│   └─ gammaFullNaive_rigid_of_locallyNoetherian            [sorry; GATE linchpin boxes]
│       ├─ (fixed-point extraction: pullSection lift_fst)   [inside proof]
│       ├─ (EllHom-iso ⟶ HomOver-iso repackaging)           [inside proof]
│       ├─ aut_trivial_of_fullLevel        Groupoid.lean:161 [CHARTER-P3B3 m.2]
│       └─ nIsInvertible_over_spec                          [sorry leaf, provable now]
├─ Representable conjunct: gammaFullNaive_representable_of_engine [REAL ✓]
│   ├─ representable_iff (T-E5 ⇐)          EllCategory.lean:274 [GATE: CHARTER-FP4]
│   ├─ gammaFullNaive_affineOverEll                         [REAL ✓]
│   │   ├─ isAffineHom_fullLevelSpaceStruct                 [sorry, provable now]
│   │   └─ exists_pointsEquiv_family                        [sorry]
│   │       └─ exists_pointsEquiv_naive                     [REAL ✓]
│   │           ├─ exists_pointsEquiv_drinfeld              [sorry, provable now]
│   │           │   ├─ levelSpaceΓ_spec    LevelSpaces.lean:68 [PROVEN]
│   │           │   ├─ point_killed_iff                     [sorry leaf, provable now]
│   │           │   └─ Point.baseChangeEquiv GroupLaw.lean:392 [PROVEN]
│   │           ├─ isFullLevel_iff_naive   Basic.lean:130   [GATE: T-D8-bridge box]
│   │           └─ nIsInvertible_over_spec                  [sorry leaf, provable now]
│   └─ gammaFullNaive_relativelyRepresentable               [REAL ✓]
└─ Geometric conjuncts: ∀ representing X, Smooth ∧ IsAffineHom
    ├─ smooth_affine_of_representableBy  ([YF-TRANS])       [sorry, provable now]
    └─ exists_representing_smooth_affine ([YF-GEOM])        [sorry; GATE: engine construction]
        ├─ etale_fullLevelSpaceStruct    ([YF-ETALE])       [sorry; GATE BB-DIFF]
        │   ├─ isOpenImmersion_levelSpaceΓι ([YF-CLOPEN])   [sorry; GATE: route α T-C1 / route β étale toolkit]
        │   ├─ torsionπ_etale            Torsion.lean:247   [⟸ BB-DIFF, CHARTER-P3B3]
        │   └─ isFinite_fullLevelSpaceStruct ([YF-FIN])     [sorry, provable now]
        ├─ smooth_of_etale_surjective    ([YF-QSM])         [sorry; Stacks 02K5/036U]
        ├─ T-E15a explicit smooth model  Bootstrap.lean     [GATE: CHARTER-FP4 item 4]
        └─ T-Q3 affine quotient          (PROVEN)           [cited]
```

Ordering for execution: L1 `nIsInvertible_over_spec` → L2 `point_killed_iff` → L3
`isAffineHom_…` → L4 `isFinite_…` → L5 `exists_pointsEquiv_drinfeld` → L6 `…_family` →
(gates land) → rigidity pair → clopen/étale → [YF-GEOM] last.

---

## 3. Leaves: quotes, Lean ↔ source match, attacks, provability

Format per leaf: **source quote** (verbatim, with print-page LOC) · **match** · **attacks
(≥3, adversarial)** · **provability**.

### L1 `nIsInvertible_over_spec` [YF-NINV]
**Quote**: KM p. 114: *"Let S be a Z[1/N]-scheme, and (E/S, α ∈ 𝒫(E/S))…"*; [Loe] Fact 3.8.1
works on `Ell/ℤ[1/N]`. **Match**: our base category is `EllObj R` with `IsUnit (N : R)`; a
`T ⟶ Spec R` then makes `T` a "ℤ[1/N]-scheme" in the only sense used (N a global unit) —
`NIsInvertible T N` (`Torsion.lean:47`, `IsUnit (N : Γ(T,⊤))`). **Attacks**: (1) N = 0 edge:
`IsUnit (0 : R)` ⟹ R trivial ⟹ Γ(X,⊤) trivial for X over Spec R…? Γ(∅-scheme) is trivial ring,
`IsUnit 0` holds there; no counterexample — statement survives. (2) global-sections vs
stalkwise invertibility: the def of record is global (`NIsInvertible`), and ring maps preserve
units — no gap. (3) name check: `Scheme.Hom.appTop`, `Scheme.ΓSpecIso`, `IsUnit.map`,
`map_natCast` all in current mathlib (repo uses the same route in
`EllObj.exists_geometricPoint`, GammaH.lean:853, via `Spec.preimage` — a second viable route).
**Provable now** (no gates).

### L2 `point_killed_iff` [YF-KILL]
**Quote**: KM 3.1 (print p. 98): *"a group homomorphism φ: (Z/NZ)² → E[N](S)"* (torsion-scheme
register) vs [Loe] Fact 3.8.1: *"pairs of sections P, Q ∈ E[S] generating E[N] in every
fibre"* (section register). **Match**: `levelSpaceΓ_spec` speaks raw (`P.1 ≫ [N] = zero`);
`IsNaiveFullLevel`/`IsFullLevel` speak group (`(N:ℤ) • P = 0` on sections of the base change);
the leaf is the iff tying them, through `point_smul_eq_comp_mulBy` (GroupLaw.lean:133 area,
PROVEN) and `Point.asSection_zsmul` (PROVEN). **Attacks**: (1) zero-object mismatch: group `0`
of `pointAddCommGroup` vs `zeroPoint` vs `g ≫ E.zero` — the transport is via `Hom.commGroup`'s
unit; the eventual proof must pin `(0 : Point) = zeroPoint` (check `zeroPoint` API; if absent,
prove via the `pointEquivOverHom` unit — recorded as the leaf's first move). (2) direction:
both directions needed (spec-side ⟸ group-side for surjectivity of the dictionary; ⟹ for
membership) — iff stated. (3) coercion `(N : ℕ)` into `mulByHom : ℤ → _`: `E.mulByHom N`
elaborates `((N : ℕ) : ℤ)` — matches `levelSpaceΓ_spec`'s literal shape (build-verified).
**Provable now**.

### L3 `isAffineHom_fullLevelSpaceStruct` [YF-AFF]
**Quote**: KM 4.7.0 (p. 111): *"relatively representable and **affine over** (Ell)"*; KM p. 112
uses it: *"Because 𝕸(δ) is affine, and 𝒫 is affine over (Ell), the scheme 𝕸(𝒫,δ) is affine
over 𝕸(δ), hence absolutely affine."* **Match**: `AffineOverEll` (EllCategory.lean:177) asks
`IsAffineHom f` for the relative presentation; our `f = levelSpaceΓι ≫ pullback.fst ≫ torsionπ`.
**Attacks**: (1) instance-chain audit (done in-session): `IsClosedImmersion I.subschemeι`
(mathlib ClosedImmersion.lean:93) → `IsAffineHom` (id.:149); `IsFinite extends IsAffineHom`
(Finite.lean:39); `IsFinite (pullback.fst f g)` for finite g (Finite.lean:80); composition
instance (Affine.lean:61). (2) `torsionπ_isFinite` (Torsion.lean:165) sorry-audit: proven via
ZMT from properness/quasi-finiteness — BUT its quasi-finiteness input
`mulByHom_locallyQuasiFinite` (Torsion.lean:141) is `sorry` ⟹ **the finiteness of `E[N]` is
itself box-gated (BB-QF)**; leaf stays honest: cite `torsionπ_isFinite` as the input and NOTE
it is done-modulo-BB-boxes (board: T-B4 "done-mod-boxes"). (3) `[NeZero N]` required by
`torsionπ_isFinite` — carried. **Provable now** modulo the cited T-B4 boxes (no new gate).

### L4 `isFinite_fullLevelSpaceStruct` [YF-FIN]
**Quote**: KM 3.6.0 (p. 102): *"Each of these functors is represented by a **finite**
S-scheme."* KM 5.1.1 (p. 129): *"Each is finite and flat over (Ell) of constant rank ≥ 1."*
**Match**: finiteness of the presentation morphism = the Γ(N) case of 3.6.0; our statement is
the composite's `IsFinite`. **Attacks**: (1) closed-immersion→IsFinite instance: verify name
(`IsClosedImmersion.isFinite`?) at discharge; fallback `IsFinite.iff_isIntegralHom_and_…` +
closed immersions are integral + lft. (2) rank clause of 5.1.1 deliberately NOT stated (needs
flatness = KM's Ch. 5 regularity work; out of T-E9 scope — recorded delta). (3) same T-B4
box-note as L3. **Provable now** modulo T-B4 boxes.

### L5 `isOpenImmersion_levelSpaceΓι` [YF-CLOPEN] — *the stream's one new geometric leaf*
**Quote (route α)**: [Loe] Prop 3.8.2 proof (p. 19, extraction l. 1121): *"we can find an
explicit S-scheme representing PH on Sch/S; it is an **open subscheme of E[N] ×_S E[N] given
by non-vanishing of Weil pairings**."* **Quote (route β)**: KM 3.7.1 proof (p. 105): *"the
notion … is local for the … etale topology … **reduce to the case when E[N] is the constant
group-scheme (Z/NZ)²**"* — over the constant scheme the full-level locus is the union of the
components indexed by bases of (ℤ/N)², hence clopen; clopen-ness descends along the étale
cover. **Match**: `levelSpaceΓι` is the (proven-closed) inclusion; the leaf asserts it is ALSO
an open immersion for N invertible — exactly "the locus is clopen". **Attacks**: (1)
**hypothesis necessity**: in char p ∣ N the statement is FALSE-ish (E[N]² non-reduced; the
divisor-equality locus is a proper closed non-open subscheme in general) — `hinv` is carried;
sharp. (2) N = 1: E[1] ≅ S, locus = everything, ι an iso — consistent. (3) route-α dependency
honesty: `weilPairing` today is a **data-sorried def** (WeilPairing/Basic.lean:42) — building
on it now would consume a data sorry; route β consumes `torsionπ_etale` (BB-DIFF) + the
étale-local trivialization of E[N] (T-B6 family, CHARTER-P3B3's toolkit) — both owned; leaf
therefore GATED, not provable today. (4) descent step of route β: "clopen after surjective
étale base change ⟹ clopen" — open immersions descend along fppf (mathlib
`IsOpenImmersion` fppf-descent — verify name at discharge; fallback: |image| open via
`Etale`+open map argument). **GATE [YF-CLOPEN]** (α: T-C1/CHARTER-P2 ∨ β: CHARTER-P3B3 étale
toolkit).

### L6 `etale_fullLevelSpaceStruct` [YF-ETALE]
**Quote**: KM 3.7.1 (p. 104): *"Each is represented by a **finite etale** S-scheme."* [Loe]
3.8.2: *"relatively representable and **étale**."* **Match**: étaleness of the presentation
morphism; T-E9 needs it only through [YF-GEOM] (KM 4.7.1's étale step), and the engine's
bootstrap axiom 2 (T-E15b) needs exactly this statement at X = ℰ₃. **Attacks**: (1) gate
honesty: `torsionπ_etale` (Torsion.lean:247) is real but consumes BB-DIFF
(`mulByHom_formallyUnramified`, :229 sorry) — named. (2) composition/stability instances:
`Etale` composition (mathlib Etale.lean:69), `IsOpenImmersion → Etale` (:77), base-change
stability — present. (3) pullback-of-étale leg: `pullback.fst (torsionπ) (torsionπ)` étale
needs `MorphismProperty.pullback_fst` for Etale — instance present (same pattern as
torsionπ_etale's own proof). **Gated on BB-DIFF + [YF-CLOPEN]**.

### L7 `exists_pointsEquiv_drinfeld` [YF-EQV-D]
**Quote**: KM 3.1 (p. 98): *"an equality of effective Cartier divisors E[N] = Σ [φ(a,b)] …
the N² sections φ(a,b) form a 'full set of sections'"*; T-D18's `exists_fullLevelLocus`
(Incidence.lean:2565 docstring): *"There is a closed subscheme of E[N] ×_S E[N] universal for
'the pair is a Drinfeld full level-N structure'."* **Match**: factorizations of g through
`fullLevelSpace` ≃ Drinfeld structures on the pullback curve — the equiv is `levelSpaceΓ_spec`
upgraded from an iff-per-pair to a pinned bijection; the PIN (the factorization classifying
(P,Q) maps to (asSection P, asSection Q)) rules out cardinality-only discharges (the
`tateRing_homEquiv` adversarial precedent, Representability.lean:116). **Attacks**: (1)
injectivity: h is determined by its (P,Q) — `levelSpaceΓι` mono (closed immersion) +
`pullback.hom_ext` + `pointToTorsion_torsionι` recover h's legs; verified these lemmas exist
and are proven. (2) surjectivity: an arbitrary member of the Drinfeld obj is a pair of
SECTIONS of the base-changed curve; `Point.baseChangeEquiv` (PROVEN, GroupLaw.lean:392) turns
them into points over g, `point_killed_iff` (L2) supplies the killing hypotheses, spec's ⟸
produces h. (3) type-defeq risk (`(X.pullbackAlong g).curve` vs `X.curve.baseChange g`):
build-verified — the statement elaborates (iota on the structure literal). (4) empty T edge:
both sides may be empty/singleton — an Equiv exists either way; no hidden inhabitation claim.
**Provable now** (levelSpaceΓ_spec chain is sorry-free; only L2's leaf feeds it).

### L8 `exists_pointsEquiv_naive` [YF-EQV-N] — REAL, compiled
**Quote**: KM 3.7.1 heading (p. 104: the "situation when N is invertible" register change);
KM 1.4.4-for-Γ(N) = T-D8's docstring quote (Basic.lean:108). **Match**:
`Equiv.subtypeEquivRight` along `isFullLevel_iff_naive` — literally the register change.
**Attacks**: (1) the bridge's own gate is honest: `isFullLevel_iff_naive` is real modulo
`fullLevel_divisor_iff_naive_gen` (Basic.lean:125 `sorry` = T-D8-bridge box, CHARTER-P3B3
item 4) — inherited, named. (2) `NIsInvertible T N` obligation discharged by L1 at
`(X.pullbackAlong g).structMap` — compiled. (3) pin transport through `subtypeEquivRight` is
definitional (`.1`-preserving) — compiled (`exact hpin …`). **Real wiring ✓** (gates: T-D8-bridge, L1, L7).

### L9 `exists_pointsEquiv_family` [YF-NAT]
**Quote**: [Loe] Def 3.7.1(3) (p. 18): *"it is relatively representable if, for every
E/S ∈ Ob(Ell/R), the functor Sch/S → Set, T ↦ P(E ×_S T/T) is representable"* — a functor
statement, i.e. the bijections commute with restriction; KM 4.2 same. **Match**: the ∃-family
+ naturality clause is `AffineOverEll`'s inner datum **verbatim** (byte-mirrored so L10's
anonymous constructor closes). **Attacks**: (1) family-choice soundness: per-g equivs from L8
are pinned, and the pin determines each equiv uniquely (mono + leg-recovery, as in L7 attack
1), so the AC-chosen family automatically satisfies naturality — the naturality proof reduces
to the pin plus `pullbackAlongMap`'s proven `lift_fst/lift_snd` equations
(EllCategory.lean:110–144). (2) direction convention: restriction-then-eqv vs
eqv-then-`P.map` — mirrored from `AffineOverEll` exactly; a flipped convention would fail
L10's `exact` (build guards it). (3) the inner subtype proof term `by rw [Category.assoc,
h.2]` — proof-irrelevant; compiled. **Provable now modulo L8's gates** (pure diagram algebra).

### L10 `gammaFullNaive_affineOverEll` — REAL, compiled (T-E5 input 1)
**Quote**: KM 4.7.0 hypothesis (p. 111) + KM 5.1.1 (p. 129): *"Each of the four moduli
problems … is relatively representable over (Ell)"*. **Match**: `AffineOverEll
(gammaFullNaiveProblem R N)`; assembly ⟨fullLevelSpace, struct, L3, L9⟩. Compiled ✓.

### L11 `gammaFullNaive_relativelyRepresentable` — REAL, compiled
**Quote**: KM 5.1.1 as above; [Loe] 3.8.2 first half. Via `AffineOverEll.relativelyRepresentable`
(PROVEN). Compiled ✓.

### L12 `gammaFullNaive_rigid_of_locallyNoetherian` [YF-RIG-NOETH]
**Quote**: KM 2.7.2(1) (p. 85, full quote in §1.1(ii) above; proof pp. 85–86). GME 2.6.4 is
the project's register of the same computation (Groupoid.lean docstrings). **Match**: the
moduli-problem fixed-point statement reduces to the linchpin: `P.map e.hom.op a = a` unpacks
(via `pullSection`'s `IsPullback.lift_fst` and `hbase`) to `P.1 ≫ e.hom.top = P.1`,
`Q.1 ≫ e.hom.top = Q.1`; repackage e as a `HomOver`-iso (over_w from `e.hom.isPullback.w` +
hbase; zero_w from `e.hom.zero_w` + hbase; inverse from `congrArg EllHom.baseHom e.hom_inv_id`);
apply `aut_trivial_of_fullLevel`; conclude `e.hom.top = 𝟙`, then `EllHom.ext` forces
`e = Iso.refl X`, contradicting `hne`. **Attacks**: (1) connectedness delta: KM 2.7.2 assumes
a CONNECTED base; the linchpin doesn't — legitimate (morphism equality `ε = 𝟙` is checkable
per connected component; the lin's own proof routes through per-component degree theory) —
recorded, no statement bug. (2) the endomorphism trap (banked on the board): the FALSE
endomorphism form (`[1+N]` fixes level points) — our statement quantifies over ISO `e : X ≅ X`
only ✓ (matches the linchpin's adversarial fix). (3) non-vacuity/sharpness witnesses, both
PROVEN in-repo: `gammaFullNaiveProblem_map_negIso_ne_of_three_le` (GammaH.lean:925 — [-1]
moves structures, so the conclusion is non-trivially attained) and
`gammaFullNaive_not_rigid_of_le_two` (:898 — N ≤ 2 fails, bound sharp). (4) gate honesty: the
linchpin is proven modulo `torsionFixed_of_fixesLevel` (Groupoid.lean:96 sorry) and the
EndomorphismDegree data boxes (`endDeg := sorry` etc.) — CHARTER-P3B3 milestone 2; named.
**Gated (linchpin boxes)**; the reduction itself is provable now.

### L13 `gammaFullNaive_rigid` [YF-RIG; GATE YF-NOETH]
**Quote**: [Loe] Prop 3.8.3 (p. 19): *"PH is rigid on Ell/R[1/6] if and only if the preimage
in SL₂(Z) of H ∩ SL₂(Z/N) contains no elements of finite order"* — H = {1}: preimage = Γ(N),
torsion-free ∌ −1 for N ≥ 3; KM 2.7.2 lifts the 1/6 restriction. **Match**: `Rigid` for the
naive problem, all X : EllObj R. **Attacks**: (1) the noetherian mismatch is REAL: the linchpin
carries `[IsLocallyNoetherian S]` (an artifact of the project's degree engine — KM Ch. 2 needs
only connectedness, NO noetherian hypothesis: verified against the full 2.6–2.7 text) while
`Rigid` quantifies over all bases ⟹ named gate **[YF-NOETH]**, discharge routes: (α)
noetherian-free End(E/S) theory (KM-faithful) — likely the linchpin's hypothesis simply drops
when the degree boxes are built KM-style; (β) spreading out (EGA IV 8; same machinery as
CartierDivisor.lean's remaining EGA 11.2.6 box). (2) sharpness: N ≤ 2 counterexample proven
(above) — the hN : 3 ≤ N is necessary. (3) vacuity probe: over R = 0 every problem is
trivially rigid; no false strength. **Gated [YF-NOETH] + L12's gates.**

### L14 `gammaFullNaive_representable_of_engine` — REAL, compiled (the route decision executed)
**Quote**: KM 4.7.2 proof (p. 117): *"This results from 4.7.1 above, thanks to the rigidity
2.7.2 and the relative representability 3.7.1."* **Match**: `representable_iff …).mpr
⟨relRep, rigid⟩` — KM's three citations become the three in-repo inputs (engine, L10/L11,
L13). Delta recorded: we take representability from 4.7.0's ⇐ and geometry separately from
4.7.1 — KM's own layering. **Gate**: `representable_iff`'s ⇐ sorry (CHARTER-FP4). Compiled ✓.

### L15 `smooth_affine_of_representableBy` [YF-TRANS]
**Quote**: KM p. 111: *"the rigidity of 𝒫 will then provide a **unique isomorphism** between
the restrictions…"* — the operative principle (representing objects are canonically
isomorphic). **Match**: transport of `Smooth`/`IsAffineHom` across `Ell/R`-isomorphic
representing objects. **Attacks**: (1) `Functor.RepresentableBy.uniqueUpToIso` VERIFIED in
mathlib (Yoneda.lean:343) — gives X ≅ X₀ in EllObj R. (2) `baseHom` of an Ell-iso is a scheme
iso (inverse = `e.inv.baseHom`, roundtrips by `congrArg EllHom.baseHom` on `hom_inv_id`/
`inv_hom_id`); `base_w` gives `X.structMap = e.hom.baseHom ≫ X₀.structMap`; conclude by
`MorphismProperty.cancel_left_of_respectsIso` — Smooth and IsAffineHom both `RespectsIso`
(mathlib instances). (3) Nonempty-vs-data: hypothesis takes `r₀` as data but `hX :
Nonempty …` — matches the held statement's Nonempty form; no choice issue (Prop target).
**Provable now.**

### L16 `smooth_of_etale_surjective` [YF-QSM]
**Quote**: KM 4.7.1 proof (pp. 116–117, §1.1(iv) above) — the smooth-curve property is checked
on 𝕸(𝒫,δ) and transferred to the quotient 𝕸(𝒫,δ)/G along the finite étale torsor π_univ;
Stacks 02K5/036U ("smooth is étale-local on the source"). **Match**: `[Etale π]`, surjective,
`Smooth (π ≫ f)` ⟹ `Smooth f`. **Attacks**: (1) truth: classical (étale surjective covers in
the source topology; smoothness source-local) — checked against Stacks 036U. (2) mathlib
availability UNVERIFIED for the exact lemma: `Smooth` has `IsLocalAtSource`? — research item;
fallbacks: fibrewise-smooth + flat + lfp characterization, or `MorphismProperty` descent API.
(3) generality: no finiteness of π needed (KM's π is finite étale — stronger); stated at the
honest minimum. **Self-contained leaf; possibly ForMathlib.**

### L17 `exists_representing_smooth_affine` [YF-GEOM]
**Quote**: KM 4.7.1 (p. 116, full quote §1.1(iv)); KM 4.7.2 conclusion: *"a smooth affine
curve Y(N) over Z[1/N]."* **Match**: ∃ a representing object with smooth affine base — the
KM 4.7.1 computation over R (the recollement charts R[1/2], R[1/3] cover Spec R for ANY R
since (2,3) = (1)). **Attacks**: (1) statement-shape honesty: the engine's current conclusion
(`P.Representable`) forgets the object; this leaf is the honest extra content, and its
discharge belongs WITH the engine construction (CHARTER-FP4) — boarded as the [YF-GEOM]
handoff, consuming this file's [YF-ETALE] at ℰ₃ + T-E15a explicitness + [YF-QSM] + T-Q3
(affine quotient, PROVEN). (2) "curve" (relative dimension 1) clause: KM asserts it; the held
T-E9 statement does NOT — no drift on our side; delta recorded (dimension = KM Ch. 5 regularity
work, out of scope). (3) cheap-discharge probe: the ∃ cannot be satisfied vacuously (it
requires an actual representing object — which for N ≥ 3 exists only through the engine);
no wrong-model risk. **Gated (engine construction + T-E15a + T-E14 + BB-DIFF).**

### L18 `gammaFullNaive_representable_assembly` — REAL, compiled (the T-E9 bridge)
Statement byte-mirrors the held `gammaFullNaive_representable`; discharge of T-E9 = one
`exact YFull.gammaFullNaive_representable_assembly R N hN hinv` by the holder of
Representability.lean. Compiled ✓ from L13 + L14 + L15 + L17.

---

## 4. Gate register (named, with owners)

| Gate | Consumed by | Owner / discharge |
|---|---|---|
| **T-E5 ⇐ engine** (T-Q6e route (a), A711-DESC, A711-étale-noeth, T-W7.1b, T-E14/15, T-E5f) | L14 | CHARTER-FP4 (+CHARTER-A for T-W7.1b/T-E-OMEGA) |
| **T-D8-bridge** `fullLevel_divisor_iff_naive_gen` | L8 | CHARTER-P3B3 item 4 |
| **BB-DIFF** ⟹ `torsionπ_etale` (+ T-B4 BB-QF/flat boxes for `torsionπ_isFinite`) | L3, L4, L6 | CHARTER-P3B3 items 1–2 |
| **Rigidity linchpin boxes** (`torsionFixed_of_fixesLevel`, EndomorphismDegree data) | L12 | CHARTER-P3B3 milestone 2 |
| **[YF-NOETH]** noetherian removal (new) | L13 | this stream (routes α/β in L13) |
| **[YF-CLOPEN]** full-level locus clopen (new) | L5 → L6 | this stream (route α = T-C1/CHARTER-P2; route β = étale toolkit, Weil-free) |
| **[YF-GEOM]** geometric handle on the engine's object (new) | L17 | handoff to CHARTER-FP4 (leaf parked here; [YF-QSM] helper provided) |

**Provable-now set** (no gates; first acts): L1, L2, L3*, L4*, L7, L9, L15 (* = modulo the
already-boarded T-B4 boxes inside `torsionπ_isFinite`, no new gate).

**Coordination flags**: (a) T-C1 dropped off T-E9's critical path (route β of [YF-CLOPEN]) —
board's T-E9 dep line should be updated; (b) [YF-ETALE]+L10 instantiated at ℰ₃ IS the T-E15b
shape — CHARTER-FP4 should consume `YFull.fullLevelSpace`/`…Struct` rather than re-derive;
(c) STREAM-Y1's clopen split (killed loci in the Tate base) and [YF-CLOPEN] should share the
étale-constancy toolkit when CHARTER-P3B3 lands it; (d) the L10 family is the T-H4/T-H6
template (general H = quotient of this presentation by H, Loe 3.8.2's last line).
