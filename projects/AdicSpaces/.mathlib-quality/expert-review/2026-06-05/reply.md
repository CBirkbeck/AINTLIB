# Reviewer reply — 2026-06-05

## Executive verdict

Your route is now faithful to Wedhorn's proof, with one important refinement: the "topological embedding" part should be treated as **closed image/equalizer + open mapping**, not as a naive application of Prop. 6.18(2) to the full product. That is still exactly the Wedhorn/Huber analytic core, but it clarifies what has to be shown in Lean.

The no-height quasi-compactness route is also correctly identified: use Wedhorn's spectral `Spv(A,I·A)` machinery and Theorem 7.10, with the strict inequality quantified over the **ideal of definition `I ⊆ A₀`**, not over `I·A`. The uploaded brief's warning about the `I·A` bug is right. Wedhorn states `Cont(A) = {v ∈ Spv(A,I·A) : v(a) < 1 for all a ∈ I}`, where `I` is the ideal of definition of a ring of definition, while the ambient spectral space uses `I·A`.

The key hypothesis-hygiene point is also right: in case (b), section rings become **strongly noetherian** by Example 6.38, not by the false implication "noetherian Tate ⇒ strongly noetherian." Wedhorn explicitly says rational localizations of a strongly noetherian Tate ring are again strongly noetherian by representing them as quotients of noetherian restricted power series rings and using closedness of the ideal.

So: keep the route, but make the two external analytic inputs explicit:

```text
Prop. 6.17/6.18 = open-mapping / closed-ideal / finite-module-topology package;
Prop. 7.48 = completion/Spa comparison.
```

Do not add noetherian ring-of-definition, domain, sigma-compactness, or global height-1 assumptions.

---

## Q1 — Decomposition faithfulness

Yes, the top-level split is faithful.

Wedhorn's Remark 8.20 says a presheaf of topological rings is a sheaf of topological rings iff it is a sheaf of rings and for every covering the map to the product is a topological embedding; the uploaded theorem card quotes exactly that criterion. Your decomposition into:

```text
algebraic equalizer / gluing
+
topological embedding
```

is therefore the right formalization target.

The injectivity part through Corollary 8.32 is also Wedhorn's route. Corollary 8.32 states that for a finite rational covering the product restriction map is faithfully flat, hence injective. Proposition 8.30 supplies flatness of individual rational restrictions, again exactly as in the theorem card.

For the topological half, the right analytic input is indeed the Prop. 6.18 / open-mapping package, but use it in the precise way:

1. Algebraic acyclicity identifies the image of `O_X(base) → ∏ᵢ O_X(Uᵢ)` with the equalizer of two continuous maps to the overlap product.
2. That equalizer is a closed subobject of the finite product, hence complete.
3. The restricted map `O_X(base) → equalizer` is continuous and bijective.
4. Apply the Tate open mapping theorem / Prop. 6.18-style openness to show it is a homeomorphism.
5. Then the inclusion of the equalizer into the product gives the desired topological embedding.

This is often cleaner in Lean than trying to apply Prop. 6.18(2) directly to the map into the full product, because the full product is not generally a finitely generated module over `O_X(base)`, while the image/equalizer is cyclic as an `O_X(base)`-module after injectivity. This is the same analytic content, just packaged in the way the topology proof actually uses.

So Q1 answer: **yes**, faithful, with the above equalizer-corestriction refinement.

---

## Q2 — Quasi-compactness keystone without height 1

Yes, the correct route is the `Spv(A,I·A)` spectral route, not a global height-1 shortcut.

Wedhorn's Lemma 7.5 proves `Spv(A,I)` is spectral with a basis of quasi-compact rational opens stable under finite intersections, under the radical finite-generation condition. The uploaded PDF excerpt shows exactly this statement and the retraction `Spv A → Spv(A,I)`. Then Theorem 7.10 identifies continuous valuations as the subspace of `Spv(A,I·A)` satisfying `v(a) < 1` for all `a ∈ I`, with `I` the ideal of definition of a ring of definition. Wedhorn then proves `Spa A` is spectral and rational subsets form a quasi-compact basis in Theorem 7.35.

The quantifier distinction is essential:

```text
Ambient spectral condition: v ∈ Spv(A, I·A)
Strict continuity cut:     v(a) < 1 for all a ∈ I ⊆ A₀
```

Do **not** replace the second `I` by `I·A`. Your counterexample with a pseudo-uniformizer multiplying an element of `I` is exactly why.

One nuance: be careful with the word "closed cylinder." The subsets involved are best handled in the **spectral / constructible / patch topology** used in Wedhorn's proof, not necessarily as naive closed sets in the original `Spv A` topology. The proof of spectrality/quasi-compactness goes through the constructible retraction and the spectral-space theorem, not through a simple "closed subset of compact space" argument in ordinary topology. Your Lean Bool/cylinder encoding can model this, but it should track which topology is being used.

So Q2 answer: **yes, your route is the faithful one**, and the `A₀`-ideal quantifier is exactly right.

---

## Q3 — External inputs 6.17/6.18, 7.48, 7.54

### Prop. 6.17 / 6.18

Treat these as external analytic inputs unless you have already formalized the Henkel/BGR open-mapping package. Wedhorn literally marks their proofs as missing, and your brief correctly identifies them as the same open-mapping circle: closed ideals, finite-module topologies, and open maps between finitely generated modules.

A self-contained formalization via a "zero sequence of units" open mapping theorem is the right general tool. Classical sigma-compact Banach OMT is too restrictive for general Tate rings, as you note. BGR is a good conceptual source in normed/affinoid settings, but Henkel-style "rings with a zero sequence of units" is closer to the abstract Tate-ring generality. If your project already has a Tate-absorbing open mapping theorem, continue with that.

### Prop. 7.48

Treat Prop. 7.48 as an external Huber input or as a separate substantial theorem. Wedhorn cites Huber for the completion/Spa comparison; it is not a small corollary. For the immediate Cor. 8.32 maximal-ideal bridge, you can often use a relative point-lifting theorem rather than a monolithic full-homeomorphism theorem, but mathematically it is the same completion comparison package.

### Lemma 7.54

Treat Lemma 7.54 as an external Huber input if you do not want to formalize Huber's product trick. But it is also a very reasonable internal proof target: a normalized rational finite subcover plus Huber's product construction. Earlier discussion identified a self-contained route using Cor. 7.32 to normalize rational neighborhoods in the Tate case. So this is less "deep analytic external" than 6.17/6.18 and 7.48.

Thus:

```text
External/deep: 6.17/6.18, 7.48.
Buildable internally if desired: 7.54.
```

---

## Q4 — Hypothesis hygiene / `C_p` test / section rings strongly noetherian

You are right to insist that case (b) uses only:

```text
A strongly noetherian Tate
```

plus the affinoid/complete/Hausdorff/nonarch conventions built into the setting. No noetherian ring of definition, no domain, no global height-1, no sigma-compactness.

The `C_p⟨X⟩` test is exactly the right guardrail: `C_p`-type coefficient fields are strongly noetherian in the BGR height-one-field sense, but their natural valuation rings are not noetherian. Wedhorn's Remark 6.37 says every completely valued height-one field is strongly noetherian, and separately that every Tate ring with a noetherian ring of definition is strongly noetherian; the latter is a sufficient condition, not a converse.

For section rings:

```text
O_X(V) is strongly noetherian
```

must come from Example 6.38, not from "noetherian + Tate ⇒ strongly noetherian." Wedhorn's Example 6.38 states that if `A` is strongly noetherian Tate, then the completed rational localization is represented as a quotient of a restricted power series ring `C = A⟨X_i,t⟩`; since `C` is noetherian by strong noetherianity and the defining ideal is closed by Prop. 6.17, the rational localization satisfies the same universal property and is again strongly noetherian.

So Q4 answer:

* **Yes**, any noetherian-ring-of-definition hypothesis on the case-(b) path is a defect.
* **Yes**, section rings become strongly noetherian via Example 6.38.
* **No**, do not promote them via abstract noetherianity of the underlying ring.

One caveat: the formal proof of Example 6.38 still uses Prop. 6.17 to ensure the quotient by the defining ideal is the correct topological quotient and has the universal property. That is expected and faithful. It is not a hidden noetherian-ring-of-definition assumption; it is the open-mapping/closed-ideal input in complete noetherian Tate rings.

---

## Additional route notes

### Cor. 8.32 maximal-ideal proof

Your route avoiding exact prime-surjection is fine, but make sure the support inequality is enough. For a maximal ideal `m` of `O_X(base)`, producing a Spa point `w` with `m ≤ supp(w)` is enough to show the extension of `m` to a factor is proper if the point lifts to that factor: the support of the lifted point is a proper prime containing the image. Equality of support is not needed.

### Lemma 8.31

Wedhorn's Remark 8.29 explicitly uses Prop. 6.18(2) to get exactness of the sequence after applying `⟨X⟩` and then a five-lemma argument. The uploaded PDF excerpt shows this dependence. So your statement that Lemma 8.31 bottoms out at the Prop. 6.18 package is correct.

### Lemma 8.33

This should be an internal algebraic diagram chase once Example 6.38/6.39 quotient identifications are established. No additional domain or height hypothesis should enter.

### Lemma 8.34

Your four-step summary is faithful to Wedhorn. The key formalization issue is to ensure that when restricting Laurent covers to a rational subset, the generators are the images in the section ring `O_X(U)`, not necessarily elements of the original `A`. This is a bookkeeping issue around relative rational localizations, not a change in proof.

---

## Recommended proof priorities

1. **Finish the `Spv(A,I·A)` / Theorem 7.10 / Theorem 7.35 quasi-compactness route.** This stabilizes every later use of compactness and Cor. 7.32.
2. **Package Prop. 6.17/6.18 from the Tate open-mapping theorem.** You already know these are the analytic external core.
3. **Finish Example 6.38 strong-noetherian propagation.** This prevents false noetherianity shortcuts from reappearing.
4. **Prove Remark 7.55 chain.** After 6.38 and 8.31, this closes Prop. 8.30.
5. **Prove Lemma 8.33 diagram chase and Lemma 8.34 assembly.**
6. **Use Prop. 7.48 / relative Spa lifting for the Cor. 8.32 maximal bridge.**

---

## Manager message to worker

The current route is faithful.

For Q1: keep the decomposition. Use Cor. 8.32 for injectivity and algebraic separation. Use the equalizer plus open-mapping theorem for the topological embedding. Do not apply Prop. 6.18 naively to the full product; corestrict to the closed equalizer/image.

For Q2: prove quasi-compactness through Wedhorn 7.5 + 7.10 + 7.35. The ambient is `Spv(A, I·A)`, but the strict continuity condition is `v(a) < 1` for `a ∈ I ⊆ A₀`, not for all `a ∈ I·A`.

For Q3: treat 6.17/6.18 and 7.48 as genuine external analytic inputs. 7.54 can be formalized internally via Huber's product trick if desired.

For Q4: do not introduce noetherian rings of definition, domains, global height-1, or sigma-compactness into case (b). Section rings `O_X(V)` are strongly noetherian by Example 6.38, not by "noetherian Tate ⇒ strongly noetherian."
