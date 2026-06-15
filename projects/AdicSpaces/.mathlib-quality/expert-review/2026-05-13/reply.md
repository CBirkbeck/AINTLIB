# Reviewer reply — 2026-05-13

Received from ChatGPT Pro, integrated 2026-05-13.

---

## Assessment

There are two important corrections to the round-4 plan.

First, **`bivariate-example-638` is a genuine, well-posed critical-path blocker**. It should be attacked directly. It is the cleanest current blocker: the statement is true, local, Wedhorn-shaped, and the proof should be a finite topological quotient/evaluation argument. I would not try to sidestep it by redefining the overlap presheaf as a limit or pushout; that would only move the same topological identification problem elsewhere.

Second, the **closedness / Stacks 00MA lane is currently misframed**. In particular:

> "Adic completion of a noetherian ring is faithfully flat without a Jacobson hypothesis"

is false in general. For example, `ℤ → ℤ_p` is flat but not faithfully flat, since tensoring with `ℤ/ℓℤ` for `ℓ ≠ p` gives zero. Faithful flatness of `I`-adic completion needs `I ⊆ Jac(R)` or an equivalent hypothesis.

Similarly, the residual

> "proper ideals stay proper under the canonical map to completion"

is false if it is stated for arbitrary proper ideals of an uncompleted rational `locSubring`. Your own earlier example essentially shows this: in a non-complete locSubring, an element like `1 + X` may be nonunit before completion but become a unit after completion, so the proper ideal it generates extends to the unit ideal.

So §8.2 and §8.3 should not be treated as "just port Bourbaki / Stacks and finish." They need a statement audit first. The valid Bourbaki theorem is:

> finitely generated submodules of finitely generated modules over a complete separated noetherian adic ring are closed

under the relevant adic/Jacobson/separated hypotheses. That is useful, but it does **not** imply arbitrary proper-ideal preservation from a non-complete dense ring into its completion.

For Lane C arbitrary covers: Theorem 5.10 is a good single-step closer, but **a single Laurent pair at the base is not enough for an arbitrary rational cover**. The right route is a topological refinement induction mirroring Wedhorn 8.34, not a claim that every cover refinement-equivalently contains one Laurent pair at the base.

## Mathematical idea

The corrected picture is:

```
Bivariate Example 6.38
→ Laurent two-cover strict/topological exactness
→ topological refinement induction
→ IsSheafy embedding/gluing
```

and separately:

```
flatness of rational restrictions
+ genuine cover-level Spec/Spa surjectivity
→ product faithful flatness
→ algebraic separation/descent
```

For **bivariate Example 6.38**, the mathematical object is clear. The overlap is modeled by a quotient of a bivariate/restricted Laurent Tate algebra. The forward map evaluates `ζ ↦ b` and `ζ⁻¹ ↦ b⁻¹`; the inverse/round-trip checks are generator computations plus continuity. This is exactly the kind of finite topological algebra calculation Wedhorn's proof expects.

Trying to replace it by a categorical limit definition would not avoid the issue. The existing presheaf value is already defined as a completion of a rational localization. To use a pushout/limit model, you would still need to prove that this model is topologically isomorphic to the current presheaf value on the overlap. That is essentially the same theorem.

For **closedness**, the correct principle is more limited. If `R` is complete, separated, noetherian, and `I`-adic, then elements of `I` are topologically nilpotent, hence `1 - x` is a unit for `x ∈ I`, so `I ⊆ Jac(R)`. Then Krull intersection / Artin–Rees gives closedness of finitely generated submodules. But this argument lives in a complete adic ring or module. It does not justify properness preservation for arbitrary ideals in a dense, non-complete ring of definition.

For **Stacks 00MA**, split the theorem into true components:

```
R noetherian ⇒ R̂_I noetherian
R noetherian ⇒ R → R̂_I flat
I ⊆ Jac(R) ⇒ R → R̂_I faithfully flat
```

The last implication is not unconditional.

For **Lane C**, the topological inducing statement is stronger than set-theoretic gluing. Wedhorn 8.34's ordinary gluing transfer does not automatically prove `Topology.IsInducing`. The topological proof should be a strict/refinement induction:

1. prove topological embedding for a Laurent two-cover;
2. prove a refinement-transfer theorem for inducing;
3. build a finite Laurent-refinement tree from a standard cover;
4. propagate inducing back through the refinement.

Faithful flatness alone is not enough to prove the topological inducing field.

## Lean-facing next steps

I would prioritize as follows.

First, finish:

```
bivariate-example-638
```

This is a true blocker and should close the Laurent overlap bridge. Proceed with the direct topological quotient/evaluation proof. Do not replace it by a limit/pushout definition.

Second, audit and likely retire or weaken the current `closedness-residual`.

If it says:

> ∀ proper ideal q of a non-complete locSubring, q · completion is proper

then it is false. Replace it with the exact statement actually needed for Cor 8.32. If the needed fact is spectrum surjectivity for the product restriction, state that directly:

> Spec(∏ O(D_i)) → Spec(O(D₀)) is surjective for a rational Spa-cover

and prove it by the Wedhorn/Spa-point argument, not by arbitrary proper-ideal preservation in `locSubring`.

If a closedness lemma is still needed, target the safe Bourbaki form:

```
-- schematic
fg_submodule_closed_of_complete_noetherian_adic
```

with hypotheses: `R` noetherian, complete, separated, `I`-adic, `M` finitely generated with the induced complete topology. Use Artin–Rees and the Jacobson/Krull intersection theorem under `I ⊆ Jac(R)`, deriving `I ⊆ Jac(R)` from completeness when appropriate.

Third, do not pursue:

```
stacks-00MA-full
```

as "faithfully flat without Jacobson." That theorem is false. You may still upstream:

> completion is noetherian;
> completion is flat;
> completion is faithfully flat under I ≤ Jac(R).

but this is not the immediate Tate acyclicity blocker unless the exact consumer needs it.

Fourth, for `lane-c-arbitrary-c`, use the single-Laurent closer as a **local induction step**, not as a global theorem that every cover contains one Laurent pair. The next theorem should be a topological refinement induction:

> if a cover has a Laurent-refinement tree whose leaves refine C, and every Laurent split in the tree is topologically inducing, then the diagonal for C is topologically inducing.

Use Aux 10.7 and Aux 10.8 as the core refinement-transfer tools.

## Answers to the specific questions

**Q1a.** `bivariate-example-638` is the cleanest true blocker. The closedness lane may close a lot only after its statement is corrected. `stacks-00MA-full` as stated is false in the faithful-flatness part.

**Q1b.** Do not sidestep the bivariate theorem by redefining overlap as a limit. It reintroduces the same topological comparison.

**Q1c.** For closedness, a direct Bourbaki/Artin–Rees port in the complete separated adic setting is better than trying to force it through completed tensor products. But first make sure the consumer statement is true.

**Q1d.** Full Stacks 00MA is realistic only if split into true pieces. Do not use it as an unconditional faithful-flatness theorem. For this project, avoid it unless noetherianity of iterated completed rings is truly missing.

**Q2a.** Neither C-α as "one Laurent pair at the base" nor C-β as "span-top plus pieces directly imply inducing" is quite right. Use a topological refinement induction mirroring Wedhorn 8.34.

**Q2b.** Faithful flatness does not imply topological inducing in general. Closedness may help prove strictness in specific exact sequences, but it will not short-circuit Lane C automatically.

**Q2c.** The equality of the base topology with the supremum of plus-piece pullback topologies is a genuine topological cover theorem. It does not follow formally from `Ideal.span S = ⊤` alone without the strict Laurent/refinement induction.

**Q3a.** Do not switch to Zavyalov now. The infrastructure is already Wedhorn-shaped, and the remaining true blocker is local.

**Q3b.** The Hübner non-domain obstruction sounds real; do not use it as the main route for strongly noetherian Tate sheafiness.

**Q3c.** The full strongly noetherian Tate theorem is still the right target. A narrower theorem may be useful as a release milestone, but it should not replace the current architecture unless the corrected closedness/spec-surjectivity audit exposes a genuine gap.

**Q4a.** No: arbitrary rational covers do not generally refine to a cover literally containing a single Laurent pair at the base.

**Q4b.** You can build Laurent-refined covers by iterated standard-cover/Laurent splitting, but keeping all new pieces refining the original cover is the content of Wedhorn 8.34, not a trivial extension.

**Q4c.** A single nonunit in `O(C.base)` is not enough to control an arbitrary finite rational cover. The correct object is a finite Laurent refinement tree, not one binary split.

## Risks or missing facts

The main risk is continuing the closedness lane under a false statement. The examples already show that proper ideals of a non-complete ring of definition can become the unit ideal after completion. This is not a Lean issue.

The second risk is expecting topological inducing from algebraic faithful flatness. This is not generally valid. The topological embedding field needs strictness/topological quotient/refinement arguments.

The third risk is treating Theorem 5.10 as if it solved arbitrary covers. It solves the Laurent-pair case and is very useful as an induction step, but arbitrary covers need a finite refinement argument.

The fourth risk is delaying the bivariate overlap theorem. It is a clean, true, local blocker; finishing it will simplify the rest of the dependency graph.

## Manager message to worker

Priority update:

1. **Attack `bivariate-example-638` first.** It is a real, true, local blocker. Use the direct bivariate quotient/evaluation proof. Do not replace the overlap by a limit/pushout construction.

2. **Pause the current `closedness-residual` until its exact statement is audited.** If it says that every proper ideal of a non-complete `locSubring` stays proper after completion, it is false. Replace it with the exact completed-ring closedness or Spec-surjectivity theorem actually needed.

3. **Do not build `stacks-00MA-full` as unconditional faithful flatness.** That theorem is false without `I ≤ Jac(R)`. Split it into noetherianity, flatness, and faithful flatness under Jacobson.

4. **For `lane-c-arbitrary-c`, do not search for one Laurent pair at the base.** Theorem 5.10 is a local induction step. Build a topological refinement induction mirroring Wedhorn 8.34: Laurent-pair inducing at each split plus refinement transfer gives inducing for the original cover.

5. **Do not expect Cor 8.32 faithful flatness to imply topological inducing.** Algebraic separation and topological embedding are separate outputs.
