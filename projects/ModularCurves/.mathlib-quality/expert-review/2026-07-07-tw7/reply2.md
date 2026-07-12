# Second reply received 2026-07-07 (verbatim) — NOTE: assessed as a ROUND-1 DIGEST, not an answer to F1'/F2/F3

[Assessment at integration time: this text re-digests the first reply (same 7-step order, same
5-piece m_U pattern, same rigidity sketch incl. the incomplete shrinking step) and cross-reads the
whole-programme brief. It does not engage the round-2 follow-up (no mention of GIT §6.1
transcription, Bosma–Lenstra, comparison theorem, noetherian scope). Its one new claim — the
"urgent Γ₁(N) drift" — was verified FALSE against the current code and brief; see integration.md.]

I'm reading this as the **T-W7 reviewer reply**. It does not derail the programme; it sharpens the implementation order. The key message is: **construct the group law explicitly by Weierstrass descent, postpone canonicity, and do not use coherent cohomology on the critical path.** The reply's three headline refinements are exactly that: prove `Γ(ProjModel(W), O) = R` uniformly over every ring rather than by base-changing only from the universal curve; use rigidity for canonicity over nonreduced bases; and build multiplication by open-cover/gluing or graph closure, not by a field-style case split.

## How to integrate it into the board

Split T-W7 into two tickets:

    T-W7a: existence
      Construct the group law on every locally-Weierstrass family by
      universal Weierstrass multiplication + base change + atlas gluing.

    T-W7b: canonicity
      Prove π_*O_E = O_S universally, prove rigidity, and deduce uniqueness
      of the group law with given zero section.

Only **T-W7a** should be on the critical path to torsion, Drinfeld level structures, `Y₁(N)`, and `Y(N)`. [...] The revised local order should be:

    1. Build m_U and inverse on the universal Weierstrass model.
    2. Prove group identities over U by generic fibre + separatedness.
    3. Descend existence to locally-Weierstrass families.
    4. Prove Γ(ProjModel(W), O) = R by chart computation.
    5. Deduce π_*O_E = O_S for locally-Weierstrass families.
    6. Prove rigidity.
    7. Deduce canonicity.

## The multiplication morphism

The recommended first implementation is **explicit open-cover-and-glue**, not a single total resultant formula. The cover should be formulated by **projective open subschemes**, not by decidable point cases. [5-piece pattern: addOnSecantOpen / addOnTangentOpen / addOnAntiDiagonal / addOnLeftInfinity / addOnRightInfinity; add_pieces_cover; add_pieces_agree_on_overlaps; m_U := glue add_pieces.] The important formal point is that `m_U` must be a **global morphism** before using the generic-fibre argument. [...] coordinate-change invariance must become a global equivariance theorem m_U(gP, gQ) = g·m_U(P,Q), not merely an affine formula lemma.

## `π_* O_E = O_S`

Do **not** prove this only for the universal curve and then invoke base change. [...] Instead prove, for every ring `R` and every elliptic Weierstrass equation `W/R`, Γ(ProjModel(W), O) ≅ R. Then the sheaf statement follows Zariski-locally. Three-chart Čech/equalizer computation on D_+(X), D_+(Y), D_+(Z). [...] I would rename the ticket from `properPushforwardStructureSheaf` to an implementation-driven pair:

    projModel_globalSections_eq_baseRing
    locallyWeierstrass_pushforward_O_eq_O

## Rigidity

Dense-open uniqueness is not enough over nonreduced bases. [...] narrow lemma: properness gives closed images; π_*O = O gives affine factorisation. Choose an affine open V around the constant value; properness shows the bad locus in the base is closed; after shrinking the morphism lands in V; maps into affine V factor through the base because Γ(X ×_S Y, O) = Γ(Y, O).

## The global programme remains correctly staged

[v8 staging endorsed: LocallyWeierstrass definition of record; [U/G]; Cartier/Drinfeld; V_ρ̄ real.] Implementation spine: m_U by explicit open-cover/glue; axioms over U by generic fibre; existence over S by base change and atlas gluing; Γ(ProjModel(W),O)=R by chart computation; rigidity from π_*O=O; canonicity from rigidity.

## One urgent drift still needs fixing

The full-programme brief still contains a dangerous `Γ₁(N)` drift: it says a Drinfeld `Γ₁(N)`-structure is a section `P` of `E[N]` such that `(aP)_{a ∈ ℤ/N}` is a full set of sections of `E[N]`, and adds a caveat that the code phrases it as `Σ_a [aP] = E[N]`. That is wrong for `Γ₁(N)`: `Σ_a [aP]` has degree `N`, while `E[N]` has degree `N²`. The Katz–Mazur/Drinfeld distinction is: Γ₁(N): Σ_{a mod N} [aP] is a subgroup divisor of rank N. Γ(N): Σ_{a,b mod N} [aP + bQ] = E[N] as Cartier divisors. [...] I would fix this before building more representability on top of `Γ₁(N)`.

## Why this still matches the classical sources

[Katz Antwerp notes: abstract definition as eventual comparison target; classical representability for full level n ≥ 3 over ℤ[1/n]. KM introduction supports the ordering. The older initial plan had the cohomological/fibrewise definition and Abel/Pic⁰ route; the current review confirms locally-Weierstrass + constructive descent was the right correction.]

## Recommended immediate worker allocation

    1. Fix Γ₁(N) definition/prose/code drift.
    2. Start T-W7a: explicit open-cover/glue construction of m_U.
    3. Prove global coordinate-change equivariance of m_U.
    4. Prove group identities over U by generic fibre and separatedness.
    5. Add bundled WeierstrassAtlas for gluing over arbitrary S.
    6. Prove Γ(ProjModel(W), O) = R by three-chart computation.
    7. Then do rigidity and canonicity as T-W7b.

I would not spend marginal effort on the coarse `j`-line or full coherent cohomology yet. The path to open fine modular curves still runs through T-W7a, Cartier incidence, torsion étaleness/rank boxes, and representability/rigidity.
