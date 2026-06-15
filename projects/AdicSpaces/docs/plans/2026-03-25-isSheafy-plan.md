# Plan: Fill the IsSheafy sorry

## The sorry

`StructureSheaf.lean:513` in `separation_ofStronglyNoetherianTate`:
```lean
∀ (C : RationalCovering A), Function.Injective (productRestriction A C)
```

## Analysis of approaches

### Approach 1: Via structureSheaf (HARD)
Show `productRestriction` agrees with `structureSheaf` restriction maps.
Requires: isomorphism between stalk-based sections and completion-based presheafValue.
This is the "presheaf comparison" — a substantial theorem in its own right.
NOT practical for immediate use.

### Approach 2: Via faithful flatness (MEDIUM)
1. Show each `restrictionMap C.base D h` is flat
2. Show the product is faithfully flat
3. Faithful flat → injective

Problem: flatness of `restrictionMap` is Prop 8.30, which requires identifying
presheafValue with Tate quotients AND that the base ring is strongly noetherian.
We have the quotient flatness but not the full chain for arbitrary C.base.

### Approach 3: Via the discrete proof generalization (SIMPLEST)

The existing discrete proof `productRestriction_injective_discrete` works by
constructing trivial valuations at primes and using radical ideal arguments.
This proof is ALGEBRAIC and doesn't depend on the topology per se — it depends
on the ring structure of presheafValue.

Key insight: `presheafValue D` for discrete A = `Localization.Away D.s` (no
completion needed since everything is already complete). For non-discrete A,
`presheafValue D` = completion of `Localization.Away D.s`. The injectivity
argument uses that: if x restricts to 0 on all covering pieces, then at every
stalk x_p = 0, hence x = 0 (since presheafValue is a subring of the stalk product).

Actually, the discrete proof doesn't use this stalk argument — it uses the
`subsheafToTypes` construction directly. Let me re-read.

### Approach 4: Reduction to discrete (CLEANEST)

**Key observation from Wedhorn:** "We may and do assume that A is complete"
(first line of the proof). And by Remark 8.18:
`(Spa(A, A⁺), O_{A,A⁺}) ≃ (Spa(Â, Â⁺), O_{Â,Â⁺})`

So the presheaf on Spa(A) is isomorphic to the presheaf on Spa(Â). If Â is
complete and has the same rational covering structure, then IsSheafy for A
follows from IsSheafy for Â.

For Â complete: the topology on Â is the I-adic completion. If A already had
the I-adic topology, Â carries the SAME topology (A was already complete).

Wait, the issue is: Â might have a different topology from A. For an arbitrary
non-complete A, Â is the completion and has the completed topology. IsSheafy
for Â is again the question we're trying to answer.

### Approach 5: Direct injectivity from completion theory (NEW)

For `presheafValue C.base` = `UniformSpace.Completion (Localization.Away base.s)`:

The restriction maps are built via `UniformSpace.Completion.extensionHom`.
The product restriction `presheafValue C.base → ∏ presheafValue Dᵢ` is the
product of these extension homs.

For injectivity: need kernel = 0. An element x ∈ presheafValue C.base is in
the kernel iff it restricts to 0 in every presheafValue Dᵢ.

Since `coeRingHom : Localization.Away base.s → presheafValue C.base` has dense
range, x = lim(xₙ) for some net in the localization. The restrictions
`restrictionMap(xₙ)` converge to `restrictionMap(x) = 0` in each presheafValue Dᵢ.

For injectivity: if lim(xₙ) restricts to 0 everywhere, then lim(xₙ) = 0.
This is because the localization maps
`algebraMap : Localization.Away base.s → Localization.Away Dᵢ.s` are
collectively injective (the covering condition ensures this algebraically).
And taking completions preserves this collective injectivity (because
completion is faithful: the kernel of `coeRingHom` is 0 for T2 spaces).

But "collective injectivity of localization maps" is exactly the ALGEBRAIC
sheaf condition, which IS the discrete case. So we reduce to the discrete case!

Concretely:
1. The algebraic maps `Localization.Away base.s → Localization.Away Dᵢ.s`
   are collectively injective (this is the discrete sheaf condition applied to
   the covering of Spec(Localization.Away base.s))
2. `coeRingHom` is injective (T2 completion)
3. `restrictionMap = completion extension of algebraic restriction`
4. If x ∈ ker(productRestriction), write x = lim(xₙ) with xₙ in localization
5. Each restrictionMap(x) = lim(restrictionMap_alg(xₙ)) = 0
6. By T2: restrictionMap_alg(xₙ) → 0 in each completion
7. Since the algebraic maps are collectively injective on a dense subset,
   and the completions are Hausdorff, x = 0

This is the right approach! It reduces to the ALGEBRAIC (discrete) sheaf
condition on the localization, which is already proved.

## Implementation plan for Approach 5

1. Prove: the algebraic restriction maps on localizations are collectively
   injective for a covering. This IS `productRestriction_injective_discrete`
   applied to the localization ring (with discrete topology).

2. Prove: if the algebraic product map on dense subring is injective, then
   the completed product map is injective (by T2 + density).

3. Conclude: `productRestriction` injective → IsSheafy.

Step 2 is the key new lemma:
```lean
-- If f : R → ∏ Sᵢ is injective and R ↪ R̂, Sᵢ ↪ Ŝᵢ are dense embeddings
-- into T2 completions, and f̂ : R̂ → ∏ Ŝᵢ is the extension, then f̂ is injective.
theorem injective_of_dense_injective ...
```

This follows from: if x ∈ ker(f̂), write x = lim(xₙ) with xₙ ∈ R. Then
f̂(x) = lim(f(xₙ)) = 0, so f(xₙ) → 0 in ∏ Ŝᵢ. Since each Ŝᵢ is T2 and
Sᵢ is dense, f(xₙ) → 0 in ∏ Sᵢ. By injectivity of f on R: xₙ → 0 in R
(if f is a topological embedding, or at least if f preserves convergence to 0).
Then x = lim(xₙ) = 0 in R̂.

Wait, this needs f to be a topological embedding (or at least: f(xₙ) → 0
implies xₙ → 0). For f = algebraic product restriction, this IS true because
f is an isometry for the adic topology (the restriction maps are adic hence
open for the localization topology).

Actually, this is getting complicated again. Let me try the simplest possible
version: just extend the discrete proof to work for non-discrete.
