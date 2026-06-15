## Executive verdict

Route C should remain the main route. Do **not** add `[SigmaCompactSpace A]` or `[SeparableSpace A]` to the keystone theorem. Instead, prove the appropriate **Baire/open-mapping theorem in the Tate-module/ring setting**, using the pseudo-uniformizer absorption that is available for Tate rings.

The sigma-compactness obstruction is real: your example with `A = ℂ((t))` shows that `presheafValue_sigmaCompactSpace` is false under the stated keystone hypotheses, while the theorem you want remains true. The brief correctly identifies that this is a failure of the available **mathlib OMT route**, not of Wedhorn 8.28(b).

The best resolution is close to your option (c), but I would **not** formulate it as a general Bourbaki open mapping theorem for arbitrary topological abelian groups. That statement is too broad unless extra hypotheses are present. Formulate the theorem for **complete Tate additive groups/modules/rings with an absorbing countable lattice system**, or for exactly the `presheafValue`/equalizer situation.

## Q1 — Should sigma-compactness be added?

No.

Adding `[SigmaCompactSpace A]` would narrow the theorem well below Wedhorn 8.28(b). Your counterexample demonstrates the point: the trivial rational datum on `ℂ((t))` would make `O(C.base) = A`, and this need not be sigma-compact, even though the sheaf theorem should still hold.

So:

```lean
presheafValue_sigmaCompactSpace
```

should either be deleted, renamed as a lemma under an explicit sigma-compact/separable/local-compact hypothesis, or moved off the keystone path. It should not be a prerequisite for `IsSheafy`.

## Q2 — Is `[SeparableSpace A]` acceptable?

Also no, not for the final theorem.

It is less restrictive than sigma-compactness, and it may be a useful optional corollary for classical `ℚ_p`-affinoid applications. But it is still not part of Wedhorn 8.28(b), and the brief explicitly notes that it would exclude natural strongly noetherian Tate rings such as affinoids over uncountable coefficient fields.

Acceptable theorem layering:

```lean
-- optional shortcut theorem
isSheafy_ofStronglyNoetherianTate_of_separable :
  [SeparableSpace A] → ...

-- real target
isSheafy_ofStronglyNoetherianTate :
  ...
```

But do not make separability part of the main keystone.

## Q3 — Should the project prove the Baire/Bourbaki OMT?

Yes, but with the correct formulation.

Your Route C scaffold is already in good shape: you have the equalizer `E_C`, its closedness/completeness, and the continuous bijective/surjective map

```lean
O(C.base) → E_C
```

formalized at the keystone site. The only missing ingredient is an OMT strong enough to show this map is open.

However, be careful about the exact theorem. A bare statement like:

```text
Every continuous surjective homomorphism of complete Hausdorff topological abelian groups
with countable fundamental systems of neighbourhoods is open.
```

is not true in that generality. For example, the identity map from a group with the discrete topology to the same underlying group with a strictly coarser complete topology is continuous and surjective but need not be open. The missing ingredient in Banach/Tate settings is an **absorption** property: small neighbourhoods absorb every element after scaling by powers of a topologically nilpotent unit.

So prove a theorem closer to:

```lean
openMap_of_surjective_continuous_tate_absorbing
```

with hypotheses of the following shape:

* source and target are additive topological groups / modules;
* source has a countable neighbourhood basis by additive subgroups;
* source is complete;
* target is Baire and T2;
* there is a unit `π` acting continuously on source and target, with `π^n → 0`;
* every source element is eventually in a fixed open lattice after multiplication by a power of `π`;
* the map commutes with multiplication by `π`;
* the map is continuous and surjective.

For the actual application, `π` is the pseudo-uniformizer of the Tate ring, and the map is induced by a ring hom, so the equivariance is automatic.

This theorem avoids sigma-compactness and separability while still retaining the real reason the Banach open mapping proof works.

### Q3(i) — Existing formal proof?

I do not know of a current proof-assistant formalization of exactly this Tate/Bourbaki form from the materials here. The available mathlib theorem in the brief is the sigma-compact topological-group form, not the Tate-absorbing form you need.

So plan to formalize it locally.

### Q3(ii) — Is the Bourbaki form shakier?

The proof is standard, but the **overly general topological-group formulation is shaky**. The Tate-module/ring formulation is not.

The Baire proof should use the standard pattern:

1. Pick an open additive subgroup/lattice `U` in the source.
2. Use Tate absorption:

   ```text
   source = ⋃ n π^{-n} U.
   ```
3. Apply surjectivity:

   ```text
   target = ⋃ n π^{-n} f(U).
   ```
4. Since the target is Baire, some closure of `π^{-n} f(U)` has nonempty interior.
5. Hence the closure of `f(U)` has nonempty interior.
6. Use the standard symmetric-neighbourhood/Pettis-type argument to get a neighbourhood of `0` contained in `f(U')` for some smaller `U' ⊆ U`.
7. Conclude `f` is open.

This is a good Lean target because your project already has many of the sublemmas listed as sorry-free: symmetric absorption, interior addition, Baire nonempty interior, Cauchy builder, and translation.

## Q4 — Is there another OMT route?

There are alternatives, but none looks better than the Tate-absorbing Baire OMT.

### Direct metric proof

A direct metric proof is viable if your `presheafValue D` completions come with explicit complete metrics and countable bases. It would essentially be the same proof as the Tate-absorbing OMT, specialized to one metric/lattice basis. This might be easier in Lean if `UniformSpace.Completion.instMetricSpace` gives good APIs, but it is less reusable.

### Stacks-style quotient-topology comparison

This would amount to proving directly that the bijection

```lean
O(C.base) ≃ E_C
```

has continuous inverse. That is exactly what OMT gives. Without OMT, you would need a strictness/open-image theorem for the Čech equalizer complex. That pushes you back toward Route B or Wedhorn 6.18 strictness.

### Wedhorn 6.18 / unique finite-module topology

This is possible in principle but likely not simpler. You would need to show the equalizer `E_C` is the same finitely generated module as `O(C.base)` with a competing complete module topology. Algebraically it is cyclic over `O(C.base)`, but the module/topology bookkeeping may be comparable to OMT, and your earlier audits found Wedhorn 6.18 easy to misstate.

So my recommendation is:

```text
Use the Tate-absorbing Baire OMT.
Do not switch to Wedhorn 6.18 unless OMT hits a new hard blocker.
```

## Q5 — If Route C fails, what Route B residual first?

If Route C somehow fails after the correct OMT formulation, return to Route B and prioritize the **standard-cover / dominating-unit source side**, not downstream tree plumbing.

Specifically:

1. Prove the corrected finset form of Corollary 7.32 with compactness hypotheses.
2. Prove the local-basis / nonvanishing finite cover theorem in the strengthened form already recommended:

   ```text
   R(insert f C.base.T / C.base.s) ∩ R({f}/f)
   ```

   rather than the false L4 form.
3. Then return to the σ-walk/tree-existence pieces.

But I would not resume Route B now. Route C is much closer.

## Q6 — Faithful translation or clean Lean re-proof?

Use the clean Lean re-proof by OMT.

It is faithful enough to the mathematics: the topological strictness is analytic/open-mapping content, and Huber's setup uses topological ring machinery. But you do not need to reproduce Huber's proof line-by-line if the equalizer + OMT proof is shorter and clearer in Lean.

The important thing is to document the bridge:

```text
Wedhorn proves algebraic equalizer exactness.
The topological-ring sheaf condition follows because the bijection
O(C.base) → sectionEqualizer(C)
is a continuous surjective map between complete Tate objects,
hence open by Banach OMT.
```

This is mathematically standard and likely easier to maintain than the huge pointwise refinement/LocalBasisHyp Route B.

## Empty-cover edge case

The empty-cover residual looks harmless if the real upstream theorem never calls it. But I would avoid leaving a permanently impossible branch with missing `[CompleteSpace A]` / `[CompatiblePlusSubring A]`.

Either:

* make the empty-cover theorem carry the needed hypotheses locally, or
* mark it as an internal lemma with an explicit precondition excluding the impossible branch, e.g.

  ```lean
  C.covers.Nonempty
  ```

  if all real consumers have nonempty covers.

The brief says upstream consumers case-split before invoking the keystone and the impossible branch is unreached.  That is fine as a temporary engineering decision, but the final clean theorem should not have a hidden unprovable branch.

## Concrete theorem to prove

A good public-facing theorem for your `BanachOMT.lean` would be something like this, schematic:

```lean
theorem IsOpenMap.of_surjective_tate_absorbing
    {G H : Type*}
    [AddCommGroup G] [TopologicalSpace G] [UniformSpace G] [IsTopologicalAddGroup G]
    [AddCommGroup H] [TopologicalSpace H] [UniformSpace H] [IsTopologicalAddGroup H]
    [T2Space H] [BaireSpace H]
    (πG : G ≃+ G) (πH : H ≃+ H)
    (f : G →+ H)
    (hf_cont : Continuous f)
    (hf_surj : Function.Surjective f)
    (h_intertwine : ∀ x, f (πG x) = πH (f x))
    (h_absorb_G : ∀ U ∈ 𝓝 (0 : G), ∀ x : G, ∃ n, (πG^[n]) x ∈ U)
    (h_basis_G : countable / sequential neighbourhood basis)
    (h_complete_G : CompleteSpace G)
    ... :
    IsOpenMap f
```

But for implementation, start with a less general version tailored to your actual rings:

```lean
theorem openMap_of_surjective_presheafValue_to_closed_equalizer
```

Then generalize only if it becomes painless.

For the actual Route C proof:

1. Apply OMT to:

   ```lean
   tildeρ_C : O(C.base) → E_C
   ```
2. Get `IsOpenMap tildeρ_C`.
3. Since `tildeρ_C` is continuous bijective and open, get a homeomorphism.
4. Compose with the inclusion `E_C ↪ ∏ O(D)`.
5. Conclude:

   ```lean
   Topology.IsEmbedding (productRestrictionSub A C)
   ```

## Manager message to worker

Do **not** add `[SigmaCompactSpace A]` or `[SeparableSpace A]` to the keystone theorem.

Route C is still the best path, but replace the mathlib sigma-compact OMT dependency with a project-local Tate/Baire open mapping theorem. The theorem should use the Tate absorption property from a pseudo-uniformizer, not sigma-compactness. The naive "complete countably based topological abelian groups" version is too broad; prove the version for complete Tate additive groups/modules/rings or specialize it directly to:

```lean
O(C.base) → sectionEqualizer(C)
```

The equalizer scaffold is already right: closed, complete, Baire, and the restricted map is continuous and bijective/surjective. Now prove the OMT assembly and use it to show the restricted map is a homeomorphism, hence the original product restriction is a topological embedding.

Keep Route B as fallback only. Do not resume the LaurentTree σ-walk unless the Tate/Baire OMT proof fails for a precise reason.
