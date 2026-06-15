# Plan: Fill the final sorry

## The sorry

`StructureSheaf.lean:664`: For `z ∈ presheafValue C.base` with all restrictions 0, prove z = 0.

## What Wedhorn does

Wedhorn DOESN'T prove productRestriction injective directly. He proves:
1. Every rational covering is O_X-acyclic (Lemma 8.34)
2. O_X is a sheaf by Prop A.4 (acyclicity on basis → sheaf)

For Lemma 8.34, the key is Example 6.38: presheaf values are again
strongly noetherian Tate rings. Then Lemma 8.33 applies to each localization.

## The simplest API that fills the sorry

We need ONE of:

### Option A: presheafValue D flat over A (~50 lines)

**What we need:**
```lean
theorem presheafValue_flat (D : RationalLocData A) [IsNoetherianRing A] :
    Module.Flat A (presheafValue D)
```

**How to prove:**
- `Localization.Away D.s` is flat over A (mathlib: `Localization.flat`)
- `presheafValue D` = completion of `Localization.Away D.s`
- Completion of flat noetherian algebra is flat

For the last step: need `UniformSpace.Completion` flat over the source.

**NEW APPROACH:** Don't use `AdicCompletion` at all. Instead, prove directly:

For a noetherian ring R with a finitely generated ideal J, the topology
defined by `{J^n}` as neighborhoods makes R into a topological ring, and
`UniformSpace.Completion R` is flat over R.

Actually, we DON'T need this general result. We just need:
`presheafValue D` is flat over A. And `presheafValue D = Completion(R)`
where R = Localization.Away s. And R is flat over A.

For `Completion(R)` flat over A: factor as `A → R → Completion(R)`.
Need: composition of flat is flat. Mathlib has this if BOTH are flat.
`R` flat over `A` ✓ (localization). `Completion(R)` flat over `R` ← THIS.

For `Completion(R)` flat over R: this is the general statement for
adic completions. If we can't use `AdicCompletion`, use the
equational criterion: for a relation `∑ fᵢ xᵢ = 0` with fᵢ ∈ R and
xᵢ ∈ Completion(R), find a trivial relation decomposition.

Since R ↪ Completion(R) (dense), each xᵢ = lim(xᵢₙ) for some net.
Then `∑ fᵢ xᵢₙ` is a net in R converging to 0 in Completion(R).
By the equational criterion on R (which is noetherian → coherent),
each relation `∑ fᵢ xᵢₙ = rₙ` (with rₙ → 0) decomposes...

This is getting complicated. Let me try a different route.

### Option B: Direct injectivity via the structure sheaf (~30 lines)

The `structureSheafInType A` is ALREADY a sheaf (built from subsheafToTypes).
It gives sections on ALL opens. For rational subsets, the sections are
elements of `∏_{x ∈ U} Localization.AtPrime(supp x)` satisfying the local
fraction condition.

If we can show: `presheafValue D` embeds injectively into
`∏_{x ∈ rationalOpen D.T D.s} Localization.AtPrime(supp x)`,
then the product restriction injectivity follows from the sheaf condition
of structureSheafInType.

The embedding: for each x ∈ rationalOpen D.T D.s, there's a natural map
`presheafValue D → Localization.AtPrime(supp x)` (the stalk map).
The product of these maps is injective if no nonzero element vanishes at
all stalks. For localization rings, this is true when the ring is reduced
(no nilpotents) — which it is for Tate rings (Hausdorff).

Actually, for ANY Hausdorff topological ring, the stalk product embedding
is injective: if x ≠ 0 in presheafValue D, then x doesn't vanish at some
prime (because Hausdorff + integral → nonzero elements have nonzero image
at some stalk).

Hmm, this requires presheafValue D to be an integral domain or at least
having trivial intersection of all primes. For noetherian Hausdorff rings,
the nilradical is 0 (intersection of all primes = nilradical, and the ring
is Hausdorff). So nonzero elements don't vanish at all primes.

### Option C: Factor through AdicCompletion (~100 lines)

Define an algebra hom `AdicCompletion J R → UniformSpace.Completion R`
and show it's an isomorphism. Then use `AdicCompletion.flat_of_isNoetherian`.

For noetherian R with fg J-adic topology:
- `AdicCompletion J R = lim R/J^n` (projective limit)
- `UniformSpace.Completion R` = Cauchy filters for J-adic uniformity
- These are canonically isomorphic (standard commutative algebra)

The map `AdicCompletion → Completion`: universal property of completion
applied to the canonical map `R → AdicCompletion J R` (which is continuous
for the J-adic topology since `R/J^n` is discrete).

The map `Completion → AdicCompletion`: for each n, the quotient
`R → R/J^n` extends to `Completion R → R/J^n` (continuous map to discrete
quotient, extends by continuity). These are compatible and give the projective
limit map.

For isomorphism: both are complete T2 with the same dense subring R.
By universality of completion: any continuous map from the dense subring to
a complete T2 space extends uniquely. So both are universal for the same
property, hence isomorphic.

## Recommendation

**Option B** is the simplest if we can establish the stalk embedding.
**Option C** is the most principled and gives useful reusable API.
**Option A** via equational criterion is possible but complex.

## For immediate progress

Try Option B: show presheafValue D embeds into the stalk product.
If that's too hard, try Option C.
