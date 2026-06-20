# Expert-review #2 reply — 2026-06-20 (embedding/inducing route + soundness)

Reviewer: adic-spaces expert. Brief: `brief.md` (this folder). Saved verbatim.

## Assessment

**Q1.** Route (a) does NOT work from faithful flatness + completeness alone — a continuous injective
map from a complete space into a complete Hausdorff space can have dense nonclosed image; algebraic
faithful flatness adds no automatic topological strictness. Route (c) does NOT by itself solve it:
Prop 6.18 applies to f.g. modules with their canonical complete module topologies, whereas the
equalizer with the subspace topology is not known complete until its image is known closed — using
6.18 there would be CIRCULAR. Thm 6.16 becomes applicable only after the compatible-family subspace
is shown complete.

**The canonical route is Čech-style closedness, but you need NOT construct a single chosen datum for
every intersection.** Define compatibility using ALL rational common refinements of two cover pieces:
each equality condition is closed, so their intersection is closed. This uses only restriction maps
already defined for rational containments and completely avoids the heterogeneous-pair problem. If
the project's compatibility predicate is already of the form

    for every D₃ rationally contained in Dᵢ and Dⱼ, resᵢ₃(sᵢ) = resⱼ₃(sⱼ),

then the embedding proof needs no new pairwise-intersection API. The classical exact sequence in
Lemma 8.33 is written using O_X(U₁∩U₂), but that is not logically necessary for defining the closed
compatible-family locus of a general cover.

**Q2.** Completeness is ESSENTIAL to Lemma 7.45 as stated; the statement is FALSE for arbitrary
incomplete affinoid rings. Counterexample: A = 𝔽_p[x] with the (x)-adic topology, A⁺ = A, 𝔭 = (x-1).
This is an affinoid ring (A is a ring of definition, every element power-bounded). (x-1) is non-open
and dense because 1 = x + (1-x) ∈ (x) + (x-1). Any valuation with support (x-1) factors through 𝔽_p,
hence is trivial; a continuous height-zero valuation has open support, so no continuous valuation can
have support containing (x-1). In the completion 𝔽_p[[x]], the image of x-1 is a unit, so no prime of
the completion lies over this prime. Completion-invariance of Spa transports valuations, not every
prime ideal of the incomplete ring; dense primes can disappear after completion. Keep completeness.

**Q3.** No blow-up / Krull–Akizuki is needed for the height-one vertical generization (that is only
Wedhorn's noetherian refinement giving a DVR with exact support). The general height-one generization
is an ordered-group fact built into "microbial": a microbial valuation has a convex subgroup H with
Γ_v/H of height one.

## Mathematical idea

**Q1.** S = ∏ᵢ 𝒪_X(Uᵢ). Let E ⊆ S be families (sᵢ) with res_{Uᵢ,D}(sᵢ) = res_{Uⱼ,D}(sⱼ) for every
i,j and every rational datum D whose rational open ⊆ both Uᵢ and Uⱼ. For each fixed (i,j,D,hᵢ,hⱼ),
S → 𝒪_X(D)×𝒪_X(D), s ↦ (res_{i,D}(sᵢ), res_{j,D}(sⱼ)) is continuous; 𝒪_X(D) Hausdorff ⟹ diagonal
closed ⟹ the agreement locus E_{i,j,D} is closed. E = ⋂ E_{i,j,D} is closed in S. Then: (1) S finite
product of complete Hausdorff countably-based rings; (2) E closed ⟹ complete, Hausdorff, countably
based; (3) algebraic separation+gluing ⟹ ρ̃ : R → E continuous bijection; (4) E an R-module via ρ̃,
ρ̃ R-linear surjective; (5) Thm 6.16 (R Tate ⟹ units→0) ⟹ ρ̃ open; (6) continuous bijective open ⟹
homeomorphism; (7) compose with E ↪ S ⟹ ρ a topological embedding. NO topology on S⊗_R S; faithful
flatness used ONLY for the algebraic identity image ρ = E.

BRIDGE TO AUDIT: if the project proved only R = Eq(S ⇉ S⊗_R S), it must ALSO prove tensor-cocycle ⟺
common-refinement compatibility. Do NOT silently identify them. If gluing is already stated with
common refinements, use it directly.

FALLBACK (route b): choose a common pair of definition for the finite cover and re-encode every piece
using it; R(Tᵢ/sᵢ)∩R(Tⱼ/sⱼ) = R((sⱼTᵢ ∪ sᵢTⱼ)/(sᵢsⱼ)). But this needs a pair-independence/re-encoding
theorem for presheafValue; the "all common refinements" definition is likely less infrastructure.

**Q2.** Keep [CompleteSpace A]. A limited incomplete version is possible only under an extra hypothesis
ensuring 𝔭 survives completion (𝔭·Â proper, under a non-open prime), then apply 7.45 on Â and pull
back. No unconditional reduction from arbitrary incomplete A.

**Q3.** "microbial Γ ⟹ ∃ convex H, height(Γ/H)=1; v/H is a vertical generization with the same support
and height one." Proof-oriented: (1) microbiality ⟹ nontrivial order hom φ : Γ_v → ℝ (Wedhorn 5.46);
(2) H = ker φ; (3) kernel of an order hom is convex; (4) proper since φ nontrivial; (5) Γ_v/H ≅ im φ ⊆ ℝ;
(6) every nonzero ordered subgroup of ℝ is archimedean ⟹ height one; (7) x = v/H, supp(x)=supp(v);
(8) continuity of the vertical generization = Wedhorn Rem 7.42, so analytic+continuous v ⟹ x analytic
continuous. Avoids finite-rank assumptions; H is automatically a maximal proper convex subgroup.

## Lean-facing next steps

Q1: add a topological equalizer subring based on the common-refinement compatibility predicate (NOT
tensor products). Prove `sectionEqualizer_isClosed` (isClosed_iInter over the fixed refinement
conditions, each a preimage of a diagonal), `_complete`, `_countablyGenerated`. Define
`productRestrictionToEqualizer : presheafValue C.base →+* sectionEqualizer C`, prove `Bijective` from
the algebraic separation/gluing, apply the existing Thm-6.16 formalization to its R-linear map. 6.18 is
NOT the correct immediate theorem. If the compatibility type is only tensor descent, first prove
`tensorCocycle_iff_commonRefinementCompatible`. Do NOT topologize the algebraic tensor product.

Q2: add `[CompleteSpace A]` explicitly to every Lemma-7.45-style point theorem; do not derive it from
IsTateRing. Record the counterexample (𝔽_p[x], (x)-adic, p=(x-1)) as a regression note.

Q3: isolate the ordered-group theorem independently of valuations
(`exists_convexSubgroup_quotient_height_one_of_microbial`, output H.IsProper + height(Γ⧸H)=1), then the
valuation wrapper `Valuation.exists_heightOne_verticalGenerization` (same support, vertical generization,
height one), then Wedhorn's continuity-under-vertical-generization. No blow-ups/normalization/Krull–Akizuki.

## Risks
- Q1: conflating the tensor descent equalizer with the rational Čech compatibility locus without
  proving equivalence (a theorem, not definitional). Give E the R-module structure via R→S and verify
  the subspace topology makes scalar mult continuous. Closed-subspace/finite-product countable-basis
  instances likely need explicit Lean instances.
- Q2: assuming completion invariance of Spa transports arbitrary primes — it transports valuations, not
  primes; dense primes can disappear.
- Q3: formalizing "largest proper convex subgroup" by an unnecessary Zorn argument — use the microbial
  witness H = ker(order hom to ℝ).

## Manager message to worker
Do NOT topologize S⊗[R]S, and do NOT get closed image from faithful flatness alone. Define the
compatible-family subring by ALL common rational refinements (s compatible iff every pair of
coordinates restricts equally to every rational datum contained in both pieces) — that subset is closed
(intersection of diagonal-preimages). Algebraic gluing ⟹ continuous bijection O(U) → compatible-family
subring; apply Thm 6.16 (target complete = closed in finite product) ⟹ homeomorphism ⟹ embedding.
Keep completeness in 7.45 (𝔽_p[x], p=(x-1) is a counterexample). For height-one, use microbial Γ ⟹
∃ convex H, height(Γ/H)=1; v/H is the generization with the same support. No finite-rank/blow-up.
