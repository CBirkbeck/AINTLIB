# Reviewer reply — 2026-05-27 round 5

## Overall verdict

Your current architecture is still the right one for the **Path α** theorem:

```lean
(P : PairOfDefinition A) [IsNoetherianRing P.A₀]
```

plus strongly noetherian Tate / completeness / Hausdorff / nonarch hypotheses. It is **not** yet a proof of Wedhorn 8.28(b) in the fully Wedhorn-clean setting, because the project is still explicitly relying on a noetherian ring of definition. That is acceptable if documented as the current theorem scope.

The two newly discovered defects are real:

1. The convex-subgroup ticket `T-WED-745-CONT-A` was mis-specified. The convex subgroup should **not** exclude all nonzero `P.I`-values. It should provide a cofinality/continuity bound.
2. The full `Presheaf.IsSheaf` Hom-presheaf theorem with discrete target topology is false for arbitrary open covers. It should be removed from the critical path.

Neither defect invalidates the main `IsSheafy` strategy. They are signature and scope errors in auxiliary tickets.

---

## Q1 — Wedhorn 7.45 continuity / convex subgroup defect

Choose **route (b)** as the formal decomposition, implemented by abstracting the already-working Lemma745 pattern.

Route (a) is mathematically safe if done carefully, but as a Lean task it is too broad: "generalize all of Lemma745" risks re-opening a 500-line proof. Route (b) gives the right local theorem boundaries and avoids the false "exclude `P.I` from `H`" condition.

The corrected structure should be:

```text
Given a valuation subring B and a finite set of ideal generators,
choose u_max < 1 bounding the nonzero values of the ideal generators.
Let H = convexGenerated(u_max⁻¹).

Then:
  (1) relevant A₀-values / T/s-values are bounded after restrictToConvex;
  (2) powers of u_max are cofinal at 0 inside WithZero(H);
  (3) this cofinality proves continuity of the restricted / extended valuation.
```

The important correction is:

```text
P.I-values are not meant to be outside H.
```

They are often inside `H`, and that is fine. What continuity needs is the cofinality statement:

```lean
exists_inv_pow_lt_of_mem_convexGenerated
```

or the corresponding "for every positive neighbourhood threshold in `H`, some power of `u_max` is smaller" lemma.

So I would decompose the new tickets as:

### T-WED-745-CONT-A′

Construct `u_max` and `H = convexGenerated(u_max⁻¹)` and prove:

```text
u_max ∈ H
u_max < 1
for every h ∈ H, ∃ n, u_max^n < h
```

in the value group / `WithZero(H)` form needed downstream.

### T-WED-745-CONT-B′

Prove `restrictToConvexBounded`:

```text
A₀ maps to ≤ 1,
T/s maps to ≤ 1,
a sufficiently deep power of I maps below every chosen threshold.
```

### T-WED-745-CONT-C′

Use the boundedness/cofinality to prove continuity of the valuation extension.

This is exactly the Lemma745 continuity proof with the Chevalley-produced valuation subring parameterized. So: **reuse Lemma745's proof pattern, but do not state the false exclusion condition.**

Route (c) is not recommended. This is on the critical Spa-point/valuation path, and parking it will keep poisoning downstream tickets.

---

## Q2 — Hom-presheaf / `Presheaf.IsSheaf` defect

Choose **route (c)** for the current project:

```text
Bypass the full Presheaf.IsSheaf formulation for now.
Use the project's IsSheafy typeclass directly.
```

The proposed `T-SP-SHEAF-B` statement over the full opens topology with the discrete placeholder topology is false for exactly the reason you identified: infinite intersections of open kernels need not be open.

Route (a), a rational-cover site, is mathematically reasonable, but it is additional site infrastructure. It is useful only if you need a mathlib `Presheaf.IsSheaf` object now. Your stated downstream consumers need `IsSheafy`, not the full `Presheaf.IsSheaf` theorem.

Route (b), replacing the discrete topology by the correct limit topology over rational covers, is the long-term mathematically clean construction, but it essentially redoes the full structure-sheaf topology. It should not block the current Wedhorn 8.28(b) route.

Recommended policy:

* Mark the current full-open Hom-presheaf theorem as **false under the placeholder discrete topology**.
* Do not try to prove it.
* Keep `IsSheafy` as the main target.
* Later, if needed, build:

  ```text
  rational-cover site sheaf
  → correct limit topology on arbitrary opens
  → full opens-site Presheaf.IsSheaf
  ```

  as a separate project.

---

## Q3 — Path α and noetherian `P.A₀`

Path α is the right current policy, but it should be documented as a **restricted theorem**, not Wedhorn's full strongly-noetherian theorem.

You should keep statements of the form:

```lean
(P : PairOfDefinition A) [IsNoetherianRing P.A₀]
```

for the current proof path.

You should **not** attempt to derive:

```lean
IsNoetherianRing P.A₀
```

from

```lean
[IsStronglyNoetherian A]
```

even for a principal pair. The `C_p`/dense-value-group issue remains decisive: natural rings of definition of strongly noetherian Tate fields need not be noetherian.

There may be partial recoveries under stronger hypotheses, for example:

* affinoid over a discretely valued field;
* Tate ring topologically of finite type over a noetherian adic ring;
* explicit noetherian pair of definition.

But those are additional hypotheses. They are not consequences of strong noetherianity alone.

So the long-term structure should be:

```lean
-- Current proven theorem:
isSheafy_ofStronglyNoetherianTate_with_noetherian_pair
  (P : PairOfDefinition A) [IsNoetherianRing P.A₀] : IsSheafy A

-- Future Wedhorn-clean theorem, if/when available:
isSheafy_ofStronglyNoetherianTate :
  [IsStronglyNoetherian A] → IsSheafy A
```

Do not keep retired "strong noetherian ⇒ noetherian `A₀`" helpers in active imports, even with `sorry`.

---

## Q4 — Overall architecture

The current architecture is still sound:

```text
Cor 8.32 + faithful flatness for separation
standard-cover / Hübner-Wedhorn reduction for gluing
Tate-absorbing OMT for topological embedding
Wedhorn 7.45 for Spa-point existence
Artin-Rees for localization-topology control
```

This is a Lean-heavy decomposition, but it is not obviously the wrong one.

I would **not** switch to Huber's original construction or a sheafification-first architecture now. Those routes would replace known local blockers with a much larger unformalized sheaf/topological-space infrastructure problem.

The correct strategic refinement is:

1. Keep `IsSheafy` as the main theorem.
2. Keep Path α as the current deliverable.
3. Bypass full `Presheaf.IsSheaf` for arbitrary opens.
4. Continue closing the two genuine root chains:

   * Wedhorn 7.45 continuity;
   * Artin-Rees / localization-topology witness extraction.
5. Treat the full Wedhorn-clean theorem as a later wrapper once noetherian-pair dependence is eliminated or replaced by a different proof.

---

## Q5 — Is the convex-subgroup route canonical?

For Lean, yes, the `restrictToConvex` pattern is a reasonable route.

Wedhorn's prose is shorter because it suppresses ordered-group and convex-subgroup bookkeeping. In Lean, those details must be made explicit. The existing Lemma745 proof already paid most of this cost, so reusing it is the best option.

A direct Chevalley valuation extension without convex restriction would still need to prove continuity and Spa-boundedness. The convex subgroup is exactly the mechanism that forces the value group into a controlled rank/height so that the continuity proof works. Avoiding it would likely reintroduce the same argument in a less modular form.

So I recommend:

```text
Do not search for a different valuation construction.
Generalize/reuse Lemma745's restrictToConvex continuity proof.
```

But do correct the sublemma semantics as described in Q1.

---

## Q6 — Where does strong noetherianity genuinely bite?

### 1. Local basis / standard-cover reduction

This is a genuine use. Hübner/Zavyalov/Wedhorn standard-cover arguments depend on noetherian/strongly noetherian behavior of rational localizations. This is not just a convenience.

### 2. Product faithful flatness / Cor 8.32

Strong noetherianity enters through:

```text
rational localizations are noetherian Tate;
Tate-algebra quotient descriptions are noetherian;
restriction maps are flat.
```

For Path α, the explicit noetherian pair handles much of the proof. For Wedhorn-clean strong-noetherian, you need the `presheafValue D` preservation results.

### 3. Banach OMT

The Tate-absorbing OMT itself does **not** need strong noetherianity. It needs:

```text
complete Tate-type additive group/ring
topologically nilpotent unit
countable/controlled neighborhood basis or absorbing lattice data
Baire/completeness
```

Strong noetherianity enters indirectly to prove the rings/section equalizers have the right topology and completeness properties, not in the core OMT proof.

So, yes, parts could be relaxed. A theorem for "complete Tate with noetherian pair of definition" is plausible and may be cleaner than strong-noetherian in some sub-lemmas. But the final Wedhorn theorem is naturally stated for strongly noetherian Tate rings, because rational-localization stability is built into that setting.

---

## Q7 — Other references

The references you have are the right ones. For the specific two defects:

### Wedhorn 7.45 / valuation continuity

Huber's *Continuous valuations* is the natural background, but it will not remove the need to formalize convex-subgroup/continuity details. Wedhorn's Lemma 7.45 is still the right guide.

### Sheaf/topological ring condition

Huber 1994 and Huber 1996 are useful context, but your Route C via Tate-absorbing OMT is a good Lean proof. Henkel is the right explicit OMT source.

### Standard-cover/gluing

Hübner and Zavyalov remain the right modern sources. I would not bring in Bhatt–Scholze or perfectoid literature for this formalization step; their frameworks are higher-powered and will not simplify the Lean obligations here.

---

## Additional tactical advice

### Artin-Rees chain

Your T-AR-1 and T-AR-2 landing is good. For T-AR-3, isolate the algebraic statement as an ideal-containment lemma before proving the element witness version.

A better target is something like:

```text
(target smallness of α * e^k)
⇒ α ∈ I^(n + k*c) + kernel(A → A[1/D.s])
```

Then derive the existential `α'` form. This is usually easier than constructing `α'` directly.

### F12 / migration off false single-map injectivity

Prioritize this. False single-map injectivity/surjectivity should not remain load-bearing. If the two callers need per-`E` separation, thread that as an explicit cover-level product-injectivity hypothesis until the final Cor 8.32 path is wired.

### Structure sheaf

Do not continue full-open `Presheaf.IsSheaf` until the topology on arbitrary opens is corrected. Keep it as a separate future milestone.

---

## Recommended execution order

1. **Fix `T-WED-745-CONT-A/B/C` signatures** using the corrected convex/cofinality semantics.
2. **Finish Wedhorn 7.45 continuity** by abstracting Lemma745.
3. **Finish T-AR-3** as an ideal-containment lemma, then T-AR-4.
4. **Migrate legacy Tate acyclicity callers off false single-map injectivity.**
5. **Keep structure sheaf `Presheaf.IsSheaf` out of the critical path.**
6. **Continue Path α assembly with explicit noetherian-pair hypotheses.**

---

## Manager message to worker

For `T-WED-745-CONT-A`, the current signature is wrong. Do not try to prove that nonzero `P.I`-values are outside the convex subgroup. In Lemma745 they are inside the convex subgroup, and that is what gives the cofinality needed for continuity.

Replace the decomposition with:

```text
A′: choose u_max and H = convexGenerated(u_max⁻¹);
    prove u_max ∈ H and powers of u_max are cofinal at 0 in H.

B′: prove boundedness of A₀ and T/s after restrictToConvex.

C′: prove continuity of the valuation extension using that cofinality.
```

For `T-SP-SHEAF-B`, stop. The full-open Hom-presheaf theorem is false with the current discrete placeholder topology. Keep the project's `IsSheafy` typeclass as the target, and treat full `Presheaf.IsSheaf` as a later project after the correct limit topology on arbitrary opens is defined.

For the noetherian `P.A₀` issue, keep Path α: explicitly pass

```lean
(P : PairOfDefinition A) [IsNoetherianRing P.A₀]
```

through the current theorem. Do not attempt to recover it from strong noetherianity.

Next best work: fix the 7.45 continuity decomposition, finish the Artin-Rees witness extraction, and migrate remaining callers off false single-map injectivity.
