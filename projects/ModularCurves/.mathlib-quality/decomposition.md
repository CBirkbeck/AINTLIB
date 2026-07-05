# Decomposition — ModularCurves (Katz–Mazur programme), Phase 1

*/develop Phase 1e artifact, 2026-07-05. Companion to `plan.md` (registers) and
`tickets.md` (board).*

## Skeleton location

Every statement below exists as a Lean declaration (`:= by sorry` for proofs; data-sorries
only per the DS register in `plan.md`) in:

```
ModularCurves/EllipticCurve/{WeierstrassModel,Basic,GroupLaw,Torsion}.lean
ModularCurves/GroupScheme/MuN.lean
ModularCurves/LevelStructure/{CartierDivisor,ExactOrder,Basic}.lean
ModularCurves/WeilPairing/Basic.lean
ModularCurves/Moduli/{EllCategory,Representability,Stack}.lean
ModularCurves/ModularCurve/YRho.lean
```

`lake build ModularCurves` **passes** (73 sorries, no type errors, no non-`sorryAx`
axioms) — verified 2026-07-05, commit `b758179b`.

## Source-coverage statement (read first — honesty gate)

- **In hand with proofs**: KM Introduction + Ch. 1 §§1.1–1.9 (preview, book pp. 1–39);
  Loeffler, *Modular Curves*, complete (21 pp.); Buzzard L8 slides pp. 33–40; Hida GME
  (full, not yet mined); Katz Antwerp (full).
- **NOT in hand**: KM Ch. 2–14 (notably 2.1 group structure, 2.3 `[N]`, 2.8 pairings,
  Ch. 3 Γ-structures, Ch. 4 formalism, 4.7). Leaves whose *only* cited source is there
  are marked **PENDING-SOURCE(KM)** below; per the `/develop` confidence gate they are
  NOT ticket-ready until the full KM text lands and the verbatim-quote check reruns.
  Where Loeffler states the same result, his verbatim statement is quoted and the leaf
  is sourced by [Loe] with the KM locator recorded for later reconciliation.
- **Adversarial pass status: PARTIAL.** The definitional layer was attacked during
  skeleton construction (log below). Full ≥3-attack logs per leaf are an explicit
  obligation attached to each ticket (`/beastmode` must complete the attack block of a
  leaf before starting it — noted in every ticket). Statement-level attacks already
  performed and their outcomes:
  - *junk-statement kills*: three `True`-placeholder specification statements
    (Weil bilinear/alternating/perfect) and one `True`-field (`IsGammaZero` cyclicity)
    were found and replaced with real statements; a data-sorry smuggled inside a theorem
    statement (`Stack.lean` fppf-sheaf morphism) was found and replaced by the real
    `pullbackAlongMap`; a duplicate of mathlib's `fppfTopology` was caught and deleted.
  - *drift check on the fibre condition*: the primitive `FibrewiseElliptic` is
    NOT the literal KM/Loeffler "genus 1" (inexpressible today); the deviation +
    equivalence obligation is recorded as leaf A9 and review question Q2.
  - *hypothesis-strength check*: `NowhereOrderLEThree` via `IsUnit (ψ₂ψ₃)` was checked
    against "not order 1,2,3 in any fibre" — the affine-point form excludes order 1
    automatically; ψ₂ vanishing ⟺ 2-torsion, ψ₃ ⟺ 3-torsion fibrewise; unit ⟺ nowhere
    vanishing. Recorded as part of E1's Lean↔source paragraph.

---

## Result R-A: Elliptic curves over a base scheme (workstream A)

### Plain-English proof-substrate (definition layer)

An elliptic curve over `S` is a proper smooth relative curve `π : E → S` with a section
`0`, all of whose geometric fibres are connected genus-1 curves. By Riemann–Roch over a
field (black box BB-RR), a pointed smooth proper geometrically connected genus-1 curve
over a field is exactly a pointed plane Weierstrass cubic with unit discriminant; the
project's fibre condition uses this equivalent form so the definition exists before
coherent cohomology does. Zariski-locally on the base, an elliptic curve admits a
Weierstrass equation (KM 2.2.5–2.2.6 / Loeffler 3.3.2), and carries a unique commutative
group law with the section as identity, via Abel's theorem `E(T) ≅ Pic⁰(E_T/T)` (KM
2.1.2).

### Leaves

- **A1** (definition, leaf): `EllipticCurve` — `EllipticCurve/Basic.lean`
  - Source: Loeffler Def 3.3.1 (p. 12), verbatim:
    > "Let S be a scheme. An elliptic curve over S is a scheme ℰ with a morphism
    > π : ℰ → S (an S-scheme) such that π is proper and flat and all fibres are smooth
    > genus 1 curves, given with a section "0" : S → ℰ."
    KM locator: 2.1.1 (PENDING-SOURCE(KM) for reconciliation only — [Loe] suffices).
  - Lean ↔ source match: `smooth : SmoothOfRelativeDimension 1 π` + `proper` +
    `zero/zero_π` match "proper and flat … smooth … section" (smoothness ⟹ flat + lfp;
    Loeffler's own Def 3.4.1 remark: "Our definition of elliptic curves over S requires
    that ℰ → S be a smooth morphism"). "All fibres are smooth genus 1 curves" is encoded
    by `FibrewiseElliptic` — see A9 for the deliberate, flagged deviation.
- **A2** (API gap → construction ticket T-A2): `projModel` (DS1) —
  `WeierstrassModel.lean`. The plane projective model as a scheme; construction by
  gluing the charts `z = 1`, `y = 1` (KM 2.2; Loeffler Def 3.3.3 gives the display
  `Y²Z + αXYZ + βYZ² = X³ + βX²Z` as a "subscheme of P²_S"). Discharged-by target:
  mathlib `Scheme.GlueData`. Specification: `IsWeierstrassModel` (interface stated).
- **A3** (leaf, T-A3): `projModel_smooth` — smooth of rel. dim 1 iff `Δ` unit.
  - Source: Loeffler Def 3.3.3 (p. 13), verbatim: "If `Δ(α,β) ∈ Γ(S,O_S)ˣ`, this is an
    elliptic curve over S." (+ Silverman III.1.4(a) fibrewise.)
- **A4** (leaf, T-A4): `isWeierstrassModel_unique` — BB-RR consumer (KM 2.2.5).
  PENDING-SOURCE(KM); Hida GME to be mined as substitute quote.
- **A5** (leaf, T-A5): `EllipticCurve.baseChange` Prop-fields (smooth/proper/fibres
  stable under pullback). Discharged-by: mathlib base-change instances for
  `SmoothOfRelativeDimension`/`IsProper` + fibre transitivity. (The *data* is already
  real in the skeleton.)
- **A6** (API gap chain T-A6, DS2): the group law. Sub-tree (KM 2.1, PENDING-SOURCE(KM);
  Loeffler recalls the statement in §3.5.4's proof — "There exists a theory of relative
  Cartier divisors and a map {degree 0 divisors on E}/{pullbacks of ones on S} → E(S)"):
  - A6.1 rigidified line bundles / `I(P)` ideals (needs AG-LB or divisor route via D-tree)
  - A6.2 Abel bijection `E(T) ≅ Pic⁰` (BB-COHBC inputs stated as black boxes)
  - A6.3 transport of group structure = `grpObj` + `grpObj_one_eq_zero`
  - A6.4 uniqueness (`grpObj_unique`), commutativity (`grpObj_comm` — alt. route:
    mathlib `AlgebraicGeometry.Group.Abelian` fibrewise + rigidity)
  - A6.5 `pointAddCommGroup` + `point_smul_eq_comp_mulBy` (spec T-A6d)
- **A9** (deviation-recording leaf, T-A9): `FibrewiseElliptic ↔ genus-1` — statement
  deferred until AG-COH provides `genus`; the *deviation* (using the Weierstrass-fibre
  form as primitive) is **review question Q2**. Until discharged, every consumer of the
  definition factors through `FibrewiseElliptic` only.

## Result R-B: Torsion and basic group schemes (workstream B)

- **B1** (leaf, T-B4): `torsionπ_isFinite`/`flat`/`torsion_rank` = **KM 2.3.1**
  (`E[N]/S` finite locally free of rank `N²`). PENDING-SOURCE(KM). Proof substrate
  (standard, to be quote-checked): `[N]` fibrewise finite of degree `N²` (Silverman
  III.6.2(d), *available in-repo fibrewise via HasseWeil dual-isogeny work*), properness
  + quasi-finiteness ⟹ finite (mathlib ZMT `IsFinite.of_isProper_of_locallyQuasiFinite`
  ✓ verified present), flatness by fibres (BB-FLAT).
- **B2** (leaf, T-B5): `mulBy_etale` for `N` invertible.
  - Source: Loeffler Lemma 3.4.2(2) (p. 15), verbatim: "If E/S is an elliptic curve and
    N ≥ is invertible on S, then [N] : E → E is smooth. … The morphism [N] multiplies a
    global differential by N, so it induces an isomorphism of tangent space. In other
    words, it is an étale morphism, and étale morphisms are smooth."
- **B3** (leaves, T-B2): `μ_N` wiring (DS3): comultiplication via `Spec` of `T ↦ T ⊗ T`;
  points spec `muNPointsEquiv`.
  - Source: Loeffler §3.2 example (p. 12), verbatim: "F(R) = {n-th roots of unity in R}
    is represented by (Z[T]/(Tⁿ − 1), T)." KM locator 1.12 (preview does NOT reach 1.12
    — PENDING-SOURCE(KM) for the KM quote; [Loe] suffices for the statement).
- **B4** (leaf, T-B6): fibre comparison `E[N] ×_S Spec k̄ ≅ (ℤ/N)²` — discharged-by
  target: **HasseWeil `NTorsion/TorsionGeneralN.lean`** (in-repo, sorry-free; verified by
  the repo survey). Bridge work: identify scheme-fibre points with `W(k̄)`-points via
  `IsWeierstrassModel.points`.

## Result R-D: Drinfeld level structures (workstream D) — KM Ch. 1, source in hand

### Plain-English proof-substrate

KM define, for a smooth commutative group-curve `C/S`: a relative effective Cartier
divisor `D ⊆ C` is a *subgroup* if `D(T) ⊆ C(T)` is a subgroup for every `T`; `P ∈ C(S)`
has *exact order `N`* if `[P] + [2P] + ⋯ + [NP]` is a subgroup. Over a base where `N` is
invertible this recovers the naive fibrewise notion (KM 1.4.4, proved by: base change
preservation ⟹ (2); étale-ness of the divisor detected on geometric fibres via the
trace-discriminant; the `ℤ/N → C` closed-immersion reformulation).

### Leaves

- **D0** (definition, leaf): `RelEffCartierDiv` (working form) — KM 1.2.3-style;
  official invertible-ideal definition equivalence = T-D1, **blocked on AG-LB**;
  PENDING-SOURCE for the exact KM 1.2.x locator (preview *does* include §1.2 — quote to
  be pulled when T-D1 is cut; pages in hand).
- **D1** (definition, leaf): `IsSubgroup` — KM 1.3.6 (p. 15), verbatim:
  > "Let D be an effective Cartier divisor in C/S which is proper over S. We say that D
  > is a subgroup of C/S if for every S-scheme T the subset D(T) of the group C(T) is in
  > fact a sub-group."
  Lean ↔ source: the `AddSubgroup H` + factoring characterisation is precisely
  "`D(T) ⊆ C(T)` is a subgroup", with `D(T)` = points of `E` factoring through the
  closed subscheme.
- **D2** (definition, leaf): `Section.HasExactOrder` — KM 1.4.1 (p. 17), verbatim:
  > "We say that a point P ∈ C(S) has "exact order N" if the effective Cartier divisor
  > D in C/S of degree N defined by D := [P] + [2P] + ⋯ + [NP] is a subgroup of C/S."
  Lean ↔ source: `orderDivisor` is `Σ_{a=1}^{N} [aP]` via DS4a; `HasExactOrder` is its
  `IsSubgroup`. **Attack recorded**: KM Caution 1.4.3 (p. 17–18: over `𝔽_p` the zero
  section has exact order `pⁿ` for all `n` — "a given point can have many different
  'exact orders'") kills any temptation to define "the order" as a function; the
  skeleton never does.
- **D3** (API gap, DS4a → T-D3): `sectionsDivisor` — sums of section-divisors via ideal
  products (KM 1.1–1.2 in hand for quotes at ticket-cut time). Specs: degree (KM 1.2.2),
  base-change.
- **D4** (leaf, T-D5): `HasExactOrder.smul_eq_zero` — KM 1.4.2 (p. 17), verbatim:
  > "If P ∈ C(S) has "exact order N," then NP = 0. Proof. Any finite locally free
  > commutative group-scheme of rank N is known to be killed by N (cf. [Oort–Tate])."
  Black box BB-DELIGNE registered.
- **D5** (leaf, T-D6): `hasExactOrder_iff_geometric` — KM 1.4.4 (1)⇔(3) (p. 18),
  verbatim (statement):
  > "Suppose that N is invertible on S. Let P ∈ C(S) be a point killed by N. Then the
  > following conditions are equivalent. (1) P has "exact order N" in C/S. … (3) For
  > every geometric point Spec(k) → S, the induced point P_k ∈ C(k) has exact order N in
  > the usual sense that N is the least positive integer which kills P_k, i.e., the N
  > points {aP_k}, a = 1,…,N are all distinct in C(k)."
  Full proof in hand (preview pp. 18–19). NOTE the skeleton statement omits KM's
  standing hypothesis "killed by N" on the LHS by building `N•P_t = 0` into the RHS —
  attack pending at ticket time: verify the two forms are equivalent given 1.4.2
  (exact order ⟹ killed by N makes the forms agree); if not, add the hypothesis.
- **D6** (leaf, T-D7): `hasExactOrder_iff_etale` — KM 1.4.4 (1)⇔(4), verbatim:
  > "(4) The effective Cartier divisor Σ_{a=1}^{N} [aP] in C/S is finite etale over S."
  Proof in hand ("It is finite etale over S if and only if its discriminant …").
- **D7** (definition + leaf, T-D2): `IsFullSetOfSectionsAlg` + reduced-base criterion —
  KM 1.9.1/1.9.2 (pp. 38–39), verbatim (from 1.9.1's proof):
  > "The points P₁,…,P_N form a full set of sections of Spec(B)/R if and only if this
  > universal f satisfies Norm(f) = ∏ f(Pᵢ) in R[T₁,…,T_N]"
  and 1.9.2: "Then in order that P₁,…,P_N form a full set of sections of Z/S, it is
  necessary and sufficient that for every geometric point Spec(k) → S, the following
  condition be satisfied: For every function f in the affine algebra B ⊗ k of Z_k/k, we
  have the equality in k: Norm(f) = ∏_{i=1}^{N} f((Pᵢ)_k)."
  Lean ↔ source: quantifying over all `R`-algebras `A` replaces KM's single universal
  case (equivalent by base change, KM 1.8.4 — proof in hand p. 36–37).
- **D8** (definitions + leaves, T-D8/T-D9): `IsFullLevel`/`IsGammaOne` Drinfeld vs naive
  — Γ(N) naive form source: Loeffler Fact 3.8.1 (p. 19), verbatim:
  > "For H = ⟨(1 0; 0 1)⟩, this is Γ(N): E/S ↦ (pairs of sections P,Q ∈ E[S] generating
  > E[N] in every fibre)."
  Drinfeld Γ(N) (`Σ [aP+bQ] = E[N]` as divisors): KM 3.1 — PENDING-SOURCE(KM).
- **D9** (definition): `IsGammaZero` — KM 3.4 + 1.4.1 cyclic subgroups (verbatim 1.4.1
  in hand: "a closed subgroup-scheme G ⊆ C which is finite locally-free of rank N over S
  is cyclic if, locally f.p.p.f. (SGA III, Exp. IV, 6.3) on S, G admits a generator").
  Skeleton uses the geometric-fibre surrogate; literal fppf-local form = T-D10 (attack
  obligation recorded: the surrogate is weaker in general — equivalence only claimed at
  geometric points; T-D10's statement is the definition of record once stated).

## Result R-E: Moduli formalism + representability (workstream E)

- **E0** (definitions, leaves): `EllObj`/`EllHom`/`ModuliProblem`/`Representable`/
  `RelativelyRepresentable`/`Rigid` — Loeffler Def 3.7.1/3.7.3 (p. 18), verbatim quotes
  in the module docstring (transcribed there in full). KM 4.1–4.4 locators
  PENDING-SOURCE(KM) for reconciliation.
- **E1** (leaf, T-E1 — **PROVABLE NOW**): `exists_unique_variableChange_isTateNormal` —
  Loeffler Prop 3.3.4 (pp. 13–14), statement verbatim:
  > "For any scheme S, E/S an elliptic curve and P ∈ E(S) such that P, 2P, 3P ≠ 0 in any
  > fibre, there exist unique α, β ∈ Γ(S,O_S) such that Δ(α,β) ∈ Γ(S,O_S)ˣ and a unique
  > isomorphism E(α,β) ≅ E mapping (0:0:1) to P."
  Full proof in hand (p. 14: translate; "P does not have order 2 in any fibre, gradients
  of tangent line at P is in Γ(S,O_S)"; shear; "(0,0) is not an inflexion point, so
  a₂ ∈ Γ(S,O_S)ˣ"; scale; sheaf-property gluing: "local uniqueness gives global
  existence"). Lean ↔ source: ring-level restriction (affine S), order conditions via
  `IsUnit (ψ₂ψ₃)` — dictionary attack recorded above. Mathlib discharge candidates
  verified present: `WeierstrassCurve.VariableChange` (+ group action `vc • W`),
  division polynomials `WeierstrassCurve.Ψ`.
- **E2** (leaf, T-E2 — **PROVABLE NOW**): `tateRing_homEquiv` — Loeffler Cor 3.3.5
  (p. 14), verbatim:
  > "The pair (Spec Z[A,B,Δ(A,B)⁻¹], (E(A,B),(0:0:1))) represents the functor
  > Sch^opp → Set, S ↦ {eq. classes of pairs (E,P), E/S elliptic curve, P ∈ E(S) not of
  > order 1,2,3 in any fibre}."
  (Ring-level universal-property half; combined with E1 it gives the display.)
  Discharge: `MvPolynomial.eval₂Hom` universal property + `IsLocalization.Away`.
- **E3** (leaf, T-E7): `gammaOneNaive_representable` — Loeffler Def 3.3.6 + Thm 3.4.4
  (pp. 14–15), verbatim: "`Y₁(5)_{Z[1/5]} = Spec Z[1/5, B, Δ(1+B,B)⁻¹]`" …
  "By construction, this represents the functor S ↦ {elliptic curves E/S with point of
  exact order N} on the category of Z[1/N]-schemes" … "Theorem 3.4.4. Y₁(N)_{Z[1/N]} is
  smooth over Z[1/N]." Proof sketch in hand (formal smoothness via `[N]` étale).
  **Attack recorded**: Loeffler's supersingular counterexample (p. 14: "our definition
  of 'point of exact order 5' is too naive in characteristic 5: if E/F₅ is
  supersingular, E[5] is a single point with multiplicity 25") is exactly why the naive
  problem is stated only over `N`-invertible bases in the skeleton.
- **E4** (leaf, T-E5): `representable_iff` — Loeffler Thm 3.7.4 (p. 18), verbatim:
  > "(Katz–Mazur) P is representable if and only if it is relatively representable and
  > rigid."
  Proof sketch in hand (naive Γ(3)/ℤ[1/3] + Legendre/ℤ[1/2], quotients, glue over
  ℤ[1/6]). Depends on API gap **AG-QUOT** (Loeffler Prop 3.6.1, p. 17, verbatim in hand:
  "Let X be a quasiprojective S-scheme … a finite group acting … there exists a unique
  S-scheme X/G … for X = Spec(A) affine, Spec(A^G) works"). KM 4.7 locator
  PENDING-SOURCE(KM).
- **E5** (leaf, T-E9): `gammaFullNaive_representable` — Loeffler Prop 3.8.2/3.8.3
  (p. 19), verbatim: "P_H is relatively representable and étale over Ell/Z[1/N] … it is
  an open subscheme of E[N] ×_S E[N] given by non-vanishing of Weil pairings" and
  "P_H is rigid on Ell/R[1/6] if and only if the preimage in SL₂(Z) of H ∩ SL₂(Z/N)
  contains no elements of finite order (i.e. has no elliptic points and does not
  contain −1)." Note the relative-representability proof route CONSUMES the Weil pairing
  (workstream C) — dependency recorded on the board.
- **E6** (leaves, T-E10/T-E11): fppf statements — BB-DESC black box (SGA 1 VIII);
  stack-bridge packaging T-E8 (mathlib `Pseudofunctor.IsStack` verified present).

## Result R-F: Y(ρ̄_N) (workstream F)

- **F0** (leaf, T-F0): `card_rootsOfUnity_algClosureQ` — char-0 alg. closed roots count
  (standard; mathlib `IsAlgClosed` + cyclotomic polynomial separability — discharge
  candidates to verify at ticket time).
- **F1** (API gap, DS5 → T-F1): `vRho` — Grothendieck–Galois / AG-GG. Loeffler §3.6
  (p. 17) provides the descent mechanism quote ("By a scary lemma (étale descent of
  morphisms) this gives an S-point…"). Specs: finite étale (T-F1a), equivariant points
  (T-F1b).
- **F2** (definition, leaf): `GaloisRepData` — Buzzard L8 p. 33, verbatim:
  > "We have ρ̄_N : Gal(Q̄/Q) → Aut_{Z/NZ}(V) equipped with an alternating
  > Gal(Q̄/Q)-equivariant perfect pairing to μ_N(Q̄)."
  Lean ↔ source: cyclotomic determinant via mathlib `modularCyclotomicCharacter`
  (uniquely characterised by `g(ζ) = ζ^{χ(g)}` — matches "equivariant pairing to μ_N"
  through `p_equivariant`). **Attack pending (review Q6)**: sign/inverse convention of
  the equivariance equation vs the two pairing normalisations.
- **F3** (leaf, T-F4): `yRho_representable` — Buzzard L8 p. 33, verbatim:
  > "Now we can look at the functor on Q-schemes S parametrising elliptic curves E/S
  > such that E[N] ≅ ρ̄_N as representations-with-pairing. This functor is representable
  > by a smooth, geometrically irreducible curve Y(ρ̄_N) over Q."
  Proof route (phase 3): Galois-descent twist of `Y(N)_ℚ` by the `GL₂(ℤ/N)`-cocycle of
  ρ (affine Galois descent = invariants; consumes E5 + AG-QUOT-for-twists).
- **F4** (leaf, T-F5): `yRho_geometricallyIrreducible` — BB-IRR, Buzzard verbatim: "NB
  irreducibility is proved complex-analytically by uniformising the C-points of the
  curve by the upper half plane." (Slide p. 34: "Proof: See 1980s.")

## Confidence-gate summary

| Subtree | Lean skeleton | Verbatim quotes | Attack log | Gate |
|---|---|---|---|---|
| A1, A3, A5 | ✓ | ✓ [Loe] | partial | **ticket-ready** |
| A2, A4, A6* | ✓ | A2 ✓ / A4, A6 pending KM | partial | A2 ready; A4/A6 statements ready, discharge PENDING-SOURCE(KM) |
| B1 | ✓ | PENDING-SOURCE(KM) | — | statement-ready; quote-gate open |
| B2, B3, B4 | ✓ | ✓ [Loe] | partial | **ticket-ready** |
| D0–D9 | ✓ | ✓ KM Ch.1 (in hand) except D8-Drinfeld/D9-fppf | partial | **ticket-ready** (D8/D10 quote-gate open) |
| E0–E3 | ✓ | ✓ [Loe] | partial | **ticket-ready** (E1/E2 provable now) |
| E4–E6 | ✓ | ✓ [Loe] (+KM pending) | partial | ready modulo AG-QUOT |
| F0–F4 | ✓ | ✓ [Buz-L8] | partial | statement-ready; T-F1 is the gate |

**Owner actions requested**: (1) full KM PDF into `refs/ModularCurves/` (unblocks the
PENDING-SOURCE(KM) quote-gates); (2) Faltings–Chai as PDF only if/when Phase 4 starts.


---

## Amendment (2026-07-05, expert-review integration)

- DS2 deleted (group law now a field of the working record `EllipticCurve`;
  `EllipticCurveGeom` carries the geometry). Leaves A6.* re-scoped to the deferred
  canonicity project (`abelEnrichment_exists/unique`) with the reviewer's seven named
  black boxes; **nothing in streams B/C/D/E depends on it anymore**.
- New result block **R-D0 (Cartier incidence, KM 1.3)** — leaves T-D11–T-D21 with
  verbatim KM 1.3.5/1.3.7 quotes (recorded in `Incidence.lean`'s module docstring;
  both passages in hand with proofs). `exists_subgroupLocus` supersedes the direct
  route to exact-order representability; D2 (`HasExactOrder`) is unchanged as the
  definition.
- Fibre condition (leaf A1) restated as pointed scheme isomorphism with `projModel`
  (reviewer Q2); the functor-of-points interface remains only inside
  `IsWeierstrassModel` (T-A2's spec).
- Pairing leaves gain the three pinning specs (naturality/divisibility/symplectic,
  Silverman convention — reviewer Q4/Q5/Q6); construction re-routed (duality API,
  KM 2.8 as backend; char-0 étale-descent construction T-C0 as first milestone).
- New leaves: groupoid layer (T-G1–T-G3, reviewer Q7); quotient stream (T-Q1–T-Q7);
  fppf-cyclicity gate (T-SG2) — **no Γ₀ representability statement may use the
  geometric-fibre surrogate**.
- Source gate hardened: KM 2.3/2.8/4.7/5–7/8–10/12–13 are do-not-formalize-from-memory.

---

## Adversarial pass (`/develop --decompose`), 2026-07-05/06 — adjudication record (v2)

**Method.** Five independent red-team agents, one per file cluster, each attacking every
public declaration in ≥3 of five categories — [FALSITY] truth/counterexample,
[HYP] hypothesis strength & degenerate bases, [SRC] fidelity to quoted sources,
[TYPE] types/universes/mathlib conventions (verified against the pinned mathlib
*source*, not memory), [DEP] dischargeability of sorries & hidden dependencies.
Coverage: all 18 skeleton files, ~105 public declarations. **Full per-leaf attack
logs** (the mode's "Attacks attempted" blocks): `decompose-attacks-2026-07-06/`
`{foundations,level-structures,moduli-core,levels-stack,pairing-yrho}.md`.
Every fix below is applied in the skeleton; `lake build` green after each round
(final: 3297 jobs, 117 sorries, 0 axioms, 0 maxHeartbeats).

### Defect register (all REJECTED/NEEDS-FIX findings, adjudicated + fixed)

| # | Where | Defect (counterexample) | Fix applied |
|---|---|---|---|
| DEF-1 | `gammaFullNaive_not_rigid_of_le_two` | vacuous over 𝔽₂-algebras / empty objects | + `hinv`, + nonempty-base `hR` (re-verified adequate by agent 4) |
| DEF-2 | Stack descent | cocycle-free fppf effectivity FALSE (sextic twist, H¹(G,μ₆)≠0) | replaced by GME 2.6.7 torsor form `levelledCurve_descent_of_torsor` (re-verified: θ(g)-orientation correct; `G : Type u`) |
| DEF-3 | incidence loci | sections not closed immersions without separatedness | `[IsSeparated π]` on T-D14/T-D15 |
| DEF-4 | `yRho_representable` | quotient compared bare schemes — relation far too coarse | pointed-over-T iso + coord-transport relation (`RepresentsYRho`) |
| DEF-5 | `coord` (YRho) | missing `over_T`; inner obligation unprovable | + `hOver`; obligation now a REAL proof (rw-chain) |
| DEF-6 | `yRho_geometricallyIrreducible` | false as universally quantified (ℙ¹⊔ℙ¹) | conditional on `RepresentsYRho` |
| DEF-7 | `IsWeierstrassModel` + T-A2/T-A4 | `points` was unpointed per-field `Nonempty(≃)` vs *nonsingular-only* `Affine.Point`: T-A2 spec FALSE for singular W (cusp /𝔽₅: 6≠5); T-A4 FALSE outright (V(F) vs V(F²) thickening) | points clause IsElliptic-guarded + pointed (x₀ ↦ 0); T-A4 gains `[W.IsElliptic]` + smoothness of both models (KM 2.2.5's actual scope) |
| DEF-8 | `glSmul_mul` | left-action law for a right action ⇒ asserts `(g*h)•L=(h*g)•L`; refuted on a basis of E[N](ℂ) via `Matrix.mul_apply` | law flipped to `(g*h)•L = h•(g•L)` |
| DEF-9 | `isIso_homOver` (T-G1) | FALSE — `[2]` is a pointed S-endo of degree 4; no source can exist | DELETED; groupoid semantics = core, documented |
| DEF-10 | `aut_trivial_of_fullLevel` (T-G3) | endo form FALSE — `[1+N]` fixes all level points | endo → iso (`e : E ≅ E`), matching GME p. 151's `deg ε = 1` |
| DEF-11 | T-H8/T-H9 (Drinfeld representability) | FALSE over arbitrary R: supersingular `(0,0)` in char p∣N is a Drinfeld structure (`Norm(f)=f(0)^{N²}` on `k[t]/(t^{N²})` — independently re-verified) fixed by `[-1]`; T-H9 refuted by in-hand KM Caution 1.4.3 | + `IsUnit (N : R)` (GME 2.6.8 scope); over-ℤ forms ⧗KM with GME's coprime-`m,n≥3` caveat recorded |
| DEF-12 | `GammaHClasses` | non-iso `HomOver`s collapse odd-isogenous curves; zero morphism collapses everything at N=1 | + `IsIso f.hom` in the relation; + real `GammaHClasses.mk` |
| DEF-13 | `exists_coarse_gammaH` (T-M2) | junk: unconstrained `∃Y` + `Nonempty(≃)` = cardinality claim satisfied by 𝔸¹ | pinned: jY to the j-line, `jY ≫ Spec C = σ`, `IsAffineHom jY`, equiv j-compatible on every class (mirrors T-M1a); full natural-transformation pin stays T-Q7 |
| DEF-14 | T-D6/T-D7 iffs + `sectionsDivisor_degree` | KM standing hypotheses dropped in transcription: "killed by N" (ℚ̄[ε]-lift counterexamples, both directions) and KM 1.2.1's separated+smooth (𝟙-Spec k n=2 unsatisfiable; nodal length 3≠2) | + `hkill : (N:ℤ)•P = 0`; + `[IsSeparated π]` + `SmoothOfRelativeDimension 1 π`; DS4a pin scoped to KM 1.2.1 |
| DEF-15 | `IsFullSetOfSectionsAlg` | mathlib `Algebra.norm` ≡ 1 without a finite basis ⇒ definition falsely strong on the flf-non-free stratum | + `[Module.Free R B] [Module.Finite R B]`; projective case via trivialising cover only (T-D4) |
| DEF-16 | `IsNaiveGammaOne` (3 agents converged) | missing global `(N:ℤ)•P = 0` (KM 1.4.4 standing hyp; Loeffler's closed condition `N·(0:0:1)=(0:1:0)`) ⇒ `gammaOneNaive_representable` FALSE (ℚ̄[[t,s]] pro-representation vs smooth∧quasi-finite-over-j), `isGammaOne_iff_naive` FALSE | global kill clause added; repairs T-E7, T-D9 and the Γ₁ functor simultaneously |
| DEF-17 | `sectionVanishingIdeal_spec` (T-D13) | hypothesis-free tautology (`Ideal.span_le` unfolds to itself) — dischargeable without the load-bearing content | restated as `sectionVanishingIdeal_eq_span_coord` (`Module.Basis`, the deg-D′-equations engine) |
| DEF-18 | `tateRing_homEquiv` (T-E2) | `Nonempty(≃)` = cardinality-only (dischargeable for A=ℂ by counting) | pinned existential: the equiv IS `φ ↦ (φ A, φ B)` |
| DEF-19 | `IsGammaZero.geometricallyCyclic` | naive-order surrogate wrong in char p∣N: excludes `Ker F` (KM-cyclic via Drinfeld generator 0, KM 1.4.3) | field upgraded to geometric *Drinfeld* form: `Σ_{a≤N}[a·P₀] = G_t` as divisors (uses `orderDivisor` + `baseChange`, moved to `CartierDivisor.lean`); fppf-local record stays T-D10 |
| DEF-20 | `torsionIdeal` | **unregistered** data-sorry (register rule (iii) violation), leaving `IsFullLevel` unconstrained | constructive kill: `:= (E.torsionι N).ker` (REAL, mathlib `Scheme.Hom.ker`); pin `torsionIdeal_subscheme` stated |
| DEF-21 | under-statements vs own docstrings | T-H4 étale half, T-H6 & `gammaFullNaive_representable` smooth∧affine, missing `[Nontrivial R]` on T-H5 (zero-ring), `Representable` duplicating mathlib `Functor.IsRepresentable` | statements strengthened to match docstrings; `Nontrivial R` added; `Representable := P.IsRepresentable` (abbrev) |
| DEF-22 | hidden dependency (agents 3+4) | `pullSection`-additivity silently consumes group-law uniqueness (A6.δ) — contradicting the "nothing depends on canonicity" amendment | surfaced as sorried spec `EllHom.pullSection_add` with the dependency edge documented; the amendment is hereby CORRECTED: streams E/H functor-laws depend on A6.δ through this single lemma |

Bonus verifications that SURVIVED hard attack (see archives for the full ~80): the
convention spine (`ad−bc` symplectic pin ↔ `det_cyclo` ↔ `p_equivariant`, same χ, no
hidden inverse; `e_{NM}=e_N^M` exponent recomputed); `mulBy = (𝟙)^n` is the pointwise
Hom-group power (mathlib source: `Hom.monoid` convolution, `GrpObj.comp_zpow`);
`grpObjMkPullbackSnd` orientation; `IsFullLevel`'s `Fin (N²)` enumeration (exhaustively
`decide`-checked, includes `(0,0)`); `glSmul` index convention (= `φ∘g`, mathlib
column-vector `mulVec`); `NowhereOrderLEThree` (`Ψ 2` is the y-involving ψ₂; `evalEval`
order pinned by mathlib's own `evalEval_polynomialY`); DEF-1/DEF-2 fixes re-verified
adequate by an independent agent.

### Consolidated QUOTE-MISSING list (per the do-not-formalize-from-memory gate)

Statement-level quote-gaps, all flagged in-file; none blocks stating, all block *closing*:

- **KM 2.2.5** (T-A4 uniqueness), **KM 2.1.2 / GME 2.2.5 statement** (abelEnrichment_*) —
  proofs transcribed in gme2, verbatim statements pending.
- **KM 2.3.1** (T-B3/B4 finite-flat-rank family: `torsionι_isClosedImmersion`,
  `torsionπ_isFinite/flat`, `torsion_rank`, `torsionπ_etale`), **KM 1.12**
  (`muNπ_isFinite/flat/finrank/etale_iff`).
- **KM 3.1/3.2/3.4/3.7** (Drinfeld level definitions of record + naive-iff),
  **KM 1.10.x** (full-sets ⟺ divisor-equality bridge asserted as "i.e." in
  `IsFullLevel`), **KM 1.6.2/1.6.3/1.6.5, 1.3.4 statements** (incidence corollaries),
  **KM 1.2.2/1.2.5 statements**.
- **KM Ch. 4** (4.1 morphism convention incl. `zero_w` reconciliation; 4.2–4.4; 4.7
  for `representable_iff`), **KM 4.7.2/5.1** (over-ℤ representability — now correctly
  NOT stated), **KM Ch. 8** (coarse), **KM 2.8** (pairing specs
  `weilPairingEval_add_left/self/mul` — C-stream gate as planned).
- Rigidity of Γ(N) in residue chars 2,3: GME B9 quote in hand covers "`N ≥ 3`
  invertible"; KM verbatim pending. Affineness of Y₁(N) for general N: QUOTE-PARTIAL
  (Loeffler `Spec`-display verbatim only for N = 5). `moduliProblem_fppf_separated`:
  formal lemma, PENDING-SOURCE marker added in-file.

**The cure for ~70% of this list is one owner action: the full KM PDF into
`refs/ModularCurves/`** (standing request).

### Confidence gate (honest, per subtree)

Binding conditions: (i) every leaf survived ≥3 recorded attacks; (ii) accepted leaves
carry verbatim quotes or an explicit PENDING-SOURCE gate; (iii) mathlib discharge
claims verified against the pinned source.

| Subtree | (i) | (ii) | (iii) | Verdict |
|---|---|---|---|---|
| A (curves/models) | ✓ | partial (KM 2.2.5 pending; Loe/Sil/GME quotes in hand) | ✓ (GlueData/Proj, smooth-base-change, ZMT, finrank all source-checked) | **PASS with quote-gate** |
| B (torsion, μ_N) | ✓ | partial (KM 2.3.1/1.12 pending; Loe 3.4.2 verbatim [sic]) | ✓ | **PASS with quote-gate** |
| D0/D (divisors, exact order, levels) | ✓ | strong (KM Ch. 1 §§1.1–1.9 in hand with proofs) — Ch. 3 defs pending | ✓ (`Scheme.Hom.ker`, `IdealSheafData`, norm API at source) | **PASS**; strongest subtree |
| C (pairing) | ✓ | C-stream gated on KM 2.8 as designed; GME 2.6.4 chain in hand | ✓ | **PASS within the declared gate** |
| E (Ell/R, representability) | ✓ | Loeffler 3.7.x verbatim re-extracted from the PDF; KM Ch. 4 pending | ✓ (`IsPullback` conventions, `Ψ`/`evalEval`, `VariableChange` action at source) | **PASS with quote-gate** |
| H (P_H, Drinfeld) | ✓ | Loe 3.8.1–3.8.3 verbatim; KM 3/5/7 pending; over-ℤ forms correctly withheld | ✓ | **PASS after DEF-8/11 repairs** |
| G/M (groupoid, coarse) | ✓ | Loe §3.6/3.8 Rem 1 verbatim; KM 8 ⧗ | ✓ | **PASS after DEF-9/10/12/13** |
| F (Y(ρ̄,p)) | ✓ | Buzzard L8 in hand | ✓ (`modularCyclotomicCharacter` hn-shape at source) | **PASS after DEF-4/5/6** |

No subtree FAILS. The pass found no defect it could not repair at statement level, and
every repair traces to a source hypothesis the transcription had dropped or a junk
pattern the project's own kill-list names.
