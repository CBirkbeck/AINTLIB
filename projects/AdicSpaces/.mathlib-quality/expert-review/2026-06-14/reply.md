# Reviewer reply — 2026-06-14

## Assessment

The obstruction in §8.1 is real, but it is not a flaw in Wedhorn's argument. It is a signal that the formalization has reached the point where it must prove the **stability of the structure-presheaf construction under rational localization** in case (b).

In Wedhorn's proof of Prop. 8.30, the reduction to `B := 𝒪_X(D)` really does treat `B` as a new affinoid Tate ring and applies the rational-localization machinery over `Spa B`. So the formal proof must know that `B` has the same "loc-lift / restriction maps are well-defined and continuous" infrastructure as `A`. Transporting the chain back to `A` changes the packaging, but not the mathematical content: it is still using the same relative rational-localization theorem.

So the next key theorem is not a workaround around `(LL)`; it is a faithful proof of `(LL)` for complete strongly noetherian Tate affinoids and their rational localizations.

The Nullstellensatz concern in §8.3 is also correctly spotted: the trivial valuation on `A/𝔪` is generally **not** the valuation Wedhorn uses. Wedhorn's proof uses Prop. 7.49 to assert `Spa(A/𝔪) ≠ ∅`, not the trivial valuation except in the open/discrete case.

## Q1 — Does the Remark 7.55 chain really need `(LL)` on `B = 𝒪_X(D)`?

Yes, in any honest formalization.

Wedhorn's proof says: By Example 6.38, O_X(V) is again a strongly noetherian Tate ring. Thus we may assume X = V. By Remark 7.55 reduce to basic Laurent steps.

That means that after replacing `A` by `B := O_X(V)`, the rational localization construction is applied **inside `Spa B`**. In Lean, that requires precisely the analogue of your `(LL)` for `B`.

You can transport the intermediate rational subsets back to the original `A` using the isomorphisms O_{Spa B}(X_i) ≅ O_X(E_i), but this does not remove the need for `(LL)`. It merely replaces "prove `(LL)` for `B`" by "prove the relative rational-localization comparison theorem for the corresponding transported data." Those are the same mathematical theorem.

So I would not try to avoid `(LL)`. The right target is `hasLocLiftPowerBounded_of_complete_stronglyNoetherianTate`, or a more explicit theorem `restrictionMap_exists_and_continuous_of_rationalContainment` (s_D a unit in O(D'); each t/s_D power-bounded in O(D'); hence restriction O(D) → O(D') exists and is continuous). Then instantiate at `A := presheafValue D`. This is exactly what makes "we may assume X = V" rigorous.

## Q2 — Clean proof of faithful `(LL)`

The clean route is valuative, using the Spa comparison and Prop. 7.52 / 7.18 style criteria. For D' ⊆ D = R(T/s):

### (LL-unit)
Show `s` maps to a unit in `𝒪_X(D')`. Use: for every y ∈ Spa(O(D')), y(s) ≠ 0. Under the comparison Spa(O(D')) ≃ rationalOpen(D') ⊆ Spa(A), this holds because rationalOpen(D') ⊆ rationalOpen(D) and points of D satisfy v(s) ≠ 0. Then apply Wedhorn 7.52(2): in a complete affinoid ring, f is a unit iff f has no zero on Spa. Avoids domain / A⁺ = A₀.

### (LL-bdd)
Show each lifted `t/s` is power-bounded in `𝒪_X(D')`. For every y ∈ Spa(O(D')), its image in Spa(A) lies in D' ⊆ D, so y(t/s) ≤ 1. Therefore t/s lies in the ring of integral elements of 𝒪_X(D') by Wedhorn 7.52(1) / 7.18. Since the plus ring is contained in the power-bounded subring, it is power-bounded.

This is the cleanest proof. Uses Spa(O(D')) ≃ rationalOpen(D') and the complete-affinoid Nullstellensatz/unit criterion. Does not require A⟨X⟩/I manipulation.

## Q3 — Prop. 7.51(2): which valuation over a maximal ideal?

The trivial valuation is not correct in general. Wedhorn's proof: (1) 𝔪 closed; (2) A/𝔪 Hausdorff; (3) identify {v ∈ Spa A | supp(v)=𝔪} = Spa(A/𝔪); (4) Prop. 7.49 ⟹ Spa(A/𝔪) ≠ ∅. So the valuation is SOME continuous valuation on the nonzero Hausdorff A/𝔪 whose existence is from Prop. 7.49. The trivial valuation is continuous only if the quotient topology is discrete; a maximal ideal in a complete affinoid need not be open. Formal route: maxIdeal_isClosed_of_complete_huber → quotient_affinoid_nonzero → spa_nonempty_of_nonzero_hausdorff_affinoid (Prop 7.49) → exists_spa_point_supp_eq_maxIdeal. Key input is Prop. 7.49, not a rank-one valuation constructor.

## Q4 — Pettis-lift / Prop. 6.18

If Theorem 5.5 already proves the correct OMT for the actual category of complete Tate-type groups/modules, you do NOT need a separate measurable-section lemma at the application site. The Pettis/Baire/measurable-lift work belongs inside the OMT.

Be careful about Theorem 5.5's statement. "continuous surjection of complete topological groups with countably generated uniformity is open" is too broad unless it has a Tate/absorption/Baire hypothesis built in. The correct Tate version uses a zero sequence of units / absorption. If proved via "units → 0 dilation cover," that is the right kind; just make sure it is visible in the statement or available from source/target.

For the sheaf embedding field: (1) E = equalizer subring of the product; (2) prove E closed, hence complete; (3) algebraic gluing/separation gives continuous surjective 𝒪_X(U) → E; (4) apply OMT to this map; (5) conclude homeomorphism; (6) therefore 𝒪_X(U) → ∏ 𝒪_X(Uᵢ) is a topological embedding. No separate Pettis lift once the OMT is established. Use Henkel/Bourbaki/Huber as the reference for the OMT package, but do not create an extra application-specific measurable-section task unless your OMT theorem is currently too weak.

## Q5 — Overall order and faithfulness

Decomposition is faithful. Order:
1. Finish Prop. 7.51 / 7.52 / Spa comparison tools (unit iff nonvanishing on Spa; bounded iff valuation ≤ 1; Spa(O(D)) ≃ rationalOpen(D)). Prerequisites for faithful (LL).
2. Prove faithful (LL) (valuative argument from Q2). Unlocks restriction maps over presheafValue D; removes Leaf A obstruction.
3. Fold the Remark 7.55 chain (basic Laurent flatness + transitivity finish Leaf A).
4. Finish Čech / Lemma 8.34 residuals (combinatorial grind, lower risk).
5. Topological embedding via equalizer + OMT.

```
Q3 Nullstellensatz / Spa comparison → faithful LL → Remark 7.55 chain / Leaf A → Leaf C → Leaf B
```

Adjustment: if Leaf B's equalizer infra is nearly done, develop it in parallel, but it should not block Leaf A.

## Risks / missing facts

1. Do not underestimate the Spa comparison theorem Spa(O(D)) ≃ rationalOpen(D). It does a lot: units, power-boundedness, relative rational localizations, the B = O(D) reduction. Central theorem, not a helper.
2. Do not use the trivial valuation in Prop. 7.51.
3. Do not have an overgeneral OMT (Theorem 5.5) whose statement is false without the Tate absorption structure. Make sure the zero-sequence-of-units / absorbing lattice mechanism is in the hypotheses.
4. Do not try to avoid (LL) by transporting back to A; it reintroduces the same theorem under another name.

## Manager message to worker

For Leaf A, do not dodge (LL) on B = O(D). Wedhorn treats B as a new affinoid ring and applies rational localization over Spa B. Prove (LL) faithfully for complete strongly noetherian Tate affinoids, via the valuative proof: Spa(O(D')) ≃ rationalOpen(D'); D' ⊆ D ⇒ s_D has no zeros on Spa(O(D')) ⇒ s_D a unit in O(D'); ⇒ t/s_D has value ≤ 1 on Spa(O(D')) ⇒ t/s_D power-bounded.

For Prop. 7.51(2), do not use the trivial valuation on A/𝔪. Use Prop. 7.49: A/𝔪 Hausdorff and nonzero ⇒ Spa(A/𝔪) nonempty. Pull a point back to Spa A.

For topological embedding, apply OMT to O(U) → equalizer subset of ∏ O(Uᵢ), not the full product. No separate Pettis-lift if the OMT is already the Tate/Baire theorem.

Order: Prop 7.51/7.52 + Spa(O(D)) ≃ rationalOpen(D) → faithful LL → Remark 7.55 chain / Leaf A → Čech gluing / Leaf C → equalizer + OMT embedding / Leaf B.
