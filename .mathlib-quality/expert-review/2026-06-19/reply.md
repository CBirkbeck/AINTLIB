# Expert-review reply — 2026-06-19 (4-leaf decomposition of Thm 8.28(b))

Reviewer: adic-spaces expert. Brief: `REVIEW_BRIEF.md` (2026-06-19). Saved verbatim.

## Assessment

The four-leaf decomposition is close, but one leaf disappears and another becomes much smaller:

1. **Leaf #4 is already a theorem of Wedhorn 7.18(1)/7.52(1)** and needs no noetherian ring of definition.
2. **Leaf #1 can be proved directly from the already-formalized Theorem 6.16**, by corestricting the product restriction to the closed equalizer. Proposition 6.18 is unnecessary for this application.
3. **Leaf #2 is correctly isolated**; its openness hypothesis is automatic for the localized plus-ring.
4. **Leaf #3's general, non-noetherian case is exactly strong enough**. For maximal ideals, support containment becomes equality by maximality.

Thus the genuinely unresolved analytic/valuation content is essentially Leaf #2, Leaf #3, and a short equalizer/OMT assembly for Leaf #1.

## Mathematical idea

**Q1.** Let S = Spa(A,A⁺) = {v∈Cont(A): v(a)≤1 ∀a∈A⁺}. Wedhorn 7.18(1): for every open
integrally closed subring G⊆A, G = {a∈A : v(a)≤1 for every v∈σ(G)}. Taking G=A⁺ gives
x∈A⁺ ⟺ v(x)≤1 ∀v∈Spa(A,A⁺). Since "ring of integral elements" includes A⁺⊆A°, the desired
conclusion follows immediately: v(x)≤1 ∀v∈Spa ⟹ x∈A⁺⊆A°. Neither completeness, Tate, nor a
noetherian ring of definition is needed. Wedhorn restates this verbatim as Prop 7.52(1).
The noetherian hypothesis in Huber Lemma 3.3(iii) concerns a DIFFERENT converse (from
*density* of σ(G) in all of Cont(A), infer G⊆A°). Here A⁺⊆A° is already affinoid data, and
the assumption is pointwise boundedness on σ(A⁺), not density. Leaf #4 should be deleted as
an independent residual.

**Q2.** Put R=𝒪_X(U), P=∏ᵢ𝒪_X(Uᵢ), and let E⊆P be the equalizer of the two overlap maps.
Algebraic separation+gluing give a continuous bijection ρ̃: R→E. The equalizer is the kernel
of the continuous difference map from P to the finite overlap product, hence closed;
therefore Hausdorff, complete, countably based as a closed subspace of a finite product of
such spaces. Apply Wedhorn 6.16 with base ring R, source module R, target module E, map ρ̃:
source complete, target complete, map surjective ⟹ open. Continuous+injective+open ⟹
homeomorphism. Compose with E↪P. Theorem 6.16 explicitly: completeness of target +
surjectivity ⟹ openness; no finite-generation / uniqueness-of-module-topology needed.

**Q3.** The precompletion localized plus-ring is open. Choose ring of definition A₀, ideal of
definition I. Since A⁺ open in A, some Iⁿ⊆A⁺. In the rational localization topology,
A₀[T/s] is a ring of definition and IⁿA₀[T/s] is an open nbhd of 0; it lies in A⁺[T/s], so
A⁺[T/s] is open. Its integral closure G contains this open subring, hence is open. This is
the openness pattern in Wedhorn 7.19. The property G⊆(A[1/s])° is supplied by the
rational-localization analogue of 7.19–7.20. Once G is a ring of integral elements, Wedhorn
7.47(4) says its closure in the completion is again a ring of integral elements.

**Q4(a).** The general case of Lemma 7.45 suffices: for every non-open prime p, an analytic
height-1 point x∈Spa A with p⊆supp(x), without a noetherian ring of definition. The
noetherian refinement only improves this to discrete valuation + exact support. If p=𝔪 is
maximal, containment forces equality since supp(x) is a proper prime. For an open maximal
ideal, the trivial valuation with that support is continuous and bounded by 1 on A⁺. So
neither branch needs the noetherian-discrete refinement. Prop 7.41 is the step ensuring the
height-1 analytic valuation is bounded on every element of A°.

**Q4(b).** Distinguish core Laurent gluing from its prerequisites: Lemmas 8.33–8.34 + App-A
refinement chase are algebraic/combinatorial once the affinoid rational-localization
identifications are established; but relative use over 𝒪_X(U) needs Leaf #2; and the standard
proof of Lemma 7.54 uses Cor 7.53, whose proof uses maximal-ideal Spa points from Prop 7.51
— so Leaf #3 (or an equivalent maximal-point theorem) is generally UPSTREAM of the reduction
to standard covers. Gluing does not need Leaf #1 or the former Leaf #4, but it may depend
indirectly on Leaves #2 and #3.

## Lean-facing next steps

1. **Delete Leaf #4 as a residual**; replace with a short wrapper around Prop 7.52(1):
   `isPowerBounded_of_forall_spa_vle_one` (membership in genuine plus-subring + A⁺≤A°).
2. **Replace the Leaf #1 target** from full 6.18 to `productRestriction_isEmbedding_via_equalizer_omt`
   with sublemmas: `sectionEqualizer_isClosed`, `sectionEqualizer_complete`,
   `productRestriction_to_equalizer_continuous_bijective`,
   `productRestriction_to_equalizer_isOpen` (Theorem 6.16).
3. **Leaf #2**: A⁺[T/s] open → integral closure G open → G ring of integral elements in the
   uncompleted localization → closure(G) ring of integral elements in completion. Use 7.47(4),
   not a bespoke sequential power-boundedness argument.
4. **Leaf #3**: keep only the general branch of 7.45 (non-open prime → analytic continuous
   valuation with support ⊇ p → height-1 vertical generization → bounded on A° by 7.41 → Spa
   point). Add the one-line maximality lemma (support containment ⟹ equality).
5. **Re-audit the gluing dependency graph**: if Lemma 7.54 consumes Prop 7.51 / Cor 7.53,
   record Leaf #3 as an upstream gluing dependency (not "gluing is wholly independent").

## Risks

1. Continuing to treat Huber Lemma 3.3(iii) as relevant for Q1 — it is not; 7.18(1)/7.52(1)
   is stronger and hypothesis-free in the affinoid setting.
2. Applying Theorem 6.16 directly to the map into the full product — it is not surjective
   there; corestrict to the algebraic equalizer/image first.
3. Defining the localized plus-ring as only the closure of the image of A⁺ — before
   completion it must contain the rational generators (T/s) and be integrally closed.
4. Stating gluing is independent of Leaf #3 while using Cor 7.53 in the proof of Lemma 7.54
   (Cor 7.53 uses maximal-ideal Spa points).

## Manager message to worker

Leaf #4 is not a real gap. Replace it immediately by Wedhorn 7.52(1): all Spa values ≤ 1 ⟹
x∈A⁺ ⟹ x∈A°. The noetherian hypothesis in Huber 3.3(iii) concerns a different density
converse and is irrelevant here. For the embedding leaf, do not formalize all of 6.18:
corestrict the product restriction to the closed equalizer, prove that target complete, and
apply the already-formalized Theorem 6.16 to obtain openness; continuous bijective + open ⟹
homeomorphism onto the equalizer. For completion of plus-rings, prove A⁺[T/s] open by
exhibiting an open subgroup IⁿA₀[T/s] inside it; its integral closure is therefore open; then
apply 7.47(4). For non-open maximal ideals, the general 7.45 theorem is enough; support
containment + maximality gives equality; no noetherian/discrete refinement needed.
