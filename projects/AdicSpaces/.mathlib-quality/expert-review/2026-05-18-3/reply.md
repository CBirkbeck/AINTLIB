# Expert reviewer reply — 2026-05-18 (third brief, Session 24)

*Reviewer: ChatGPT (math model) responding to `brief.md` in this folder.*

## Q-S24.1 — Does Example 6.38 give a noetherian ring of definition?

Yes, **if you start with an explicit noetherian ring of definition**.

For a rational localization $A\langle f_1/s, \ldots, f_n/s \rangle$, the natural ring of definition is $A_0\langle f_1/s, \ldots, f_n/s \rangle = A_0[f_1/s, \ldots, f_n/s]^\wedge$. If $A_0$ is noetherian, then $A_0[f_i/s]$ is a finitely generated $A_0$-algebra, hence noetherian, and its adic completion is noetherian by the standard noetherian-completion theorem (Stacks 0316). This is also exactly the construction reviewed in Zavyalov's rational localization section.

So under Path α, `(P : PairOfDefinition A) [IsNoetherianRing P.A₀]` does propagate to rational localizations, provided the project constructs the canonical pair on `presheafValue D` as the completed `P.A₀[T/s]`.

This does NOT contradict the ℂ_p counterexample. The false statement was "strongly noetherian Tate ⇒ some/canonical ring of definition is noetherian". The true Path-α statement is "chosen noetherian A_0 ⇒ the induced rational-localization ring of definition is noetherian".

Recommended encoding:

```
presheafValue_pairOfDefinition_isNoetherian
  (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
  (D : RationalLocData A using P) :
  IsNoetherianRing (presheafValue_pairOfDefinition D).A₀
```

This is a routine consequence of finite type over `P.A₀` plus noetherianity of adic completion.

## Q-S24.2 — Does Wedhorn 8.31 need `A₀` noetherian?

For formalization purposes: **yes, the honest proof hypothesis is noetherianity of a ring of definition or an equivalent noetherian adic model, not merely that `A` is noetherian as an abstract ring.**

The phrase "noetherian Tate ring" in this part of the literature is dangerous. In Huber/Wedhorn-style usage it often means a topological/noetherian condition tied to a ring of definition, not simply `[IsNoetherianRing A]` as an abstract commutative ring.

The proof of Lemma 8.31 uses an adic completion model built from a pair of definition. The ingredients (exactness/flatness of completion, finite-module topology, completion of polynomial/Tate algebras) are naturally theorems over a noetherian adic ring of definition. Without noetherianity of `A_0`, those tools are not available.

So the project's Path-α theorem `TateAlgebra.faithfullyFlat_general (P : PairOfDefinition A) [IsNoetherianRing P.A₀]` is the honest formal target.

Do NOT try to prove the version with just `[IsNoetherianRing A]` as the main route. A field like ℂ_p is noetherian as an abstract ring, but its natural valuation ring is not noetherian. The theorem may still be true for such fields by BGR's Banach/Tate-algebra theory, but that is a different route, not Wedhorn's noetherian-ring-of-definition proof.

## Q-S24.3 — Non-domain Wedhorn 8.34

Wedhorn 8.34 is intended for non-domain strongly noetherian Tate rings. The proof does NOT require `A` to be a domain.

The apparent obstruction comes from thinking of ratio splits as requiring literal fractions in `A` or cancellation inside a domain. Wedhorn's construction avoids that:

- Laurent covers are defined by valuation inequalities, not by domain-theoretic cancellation.
- In Step (iii), the ratios are ratios of **units in the local affinoid ring** `O(V_j)`.
- If `u_i` and `u_j` are units in `O(V_j)`, then the Laurent split at `u_i u_j⁻¹` is meaningful regardless of whether `A` has zero divisors.
- When transported back to the original space, the corresponding rational subsets are denominator-cleared rational subdomains, not algebraic localizations requiring a domain.

The example `A = k⟨T,U⟩/(TU)` does not disprove Wedhorn's theorem. It only disproves false single-map statements such as individual restriction injectivity or naive ratio constructions that require global denominators to be nonzero everywhere. The cover-level / unit-generated / relative-ratio argument still works.

Therefore:
- `IsDomain A` should NOT be in the final theorem.
- Any proof step needing `IsDomain` should be treated as a proof artifact.
- F5 should remain the real target; F4 may be a temporary domain-restricted helper only.

For ratio splits, keep using `RatioNodeData` / relative unit-ratio transport rather than domain cancellation.

## Q-S24.4 — Does the final theorem need `[CompleteSpace A]`?

Yes, unless your project has already formalized completion invariance.

Wedhorn's adic-spectrum and structure-presheaf results in this range are normally stated for complete affinoid rings, or else one first replaces `A` by its completion. Zavyalov's proof, for example, explicitly begins by reducing to the complete case using the canonical isomorphism between the adic spectrum of `A` and that of its completion.

If your Lean typeclass `IsTateRing A` does NOT imply `CompleteSpace A`, then the honest formal theorem should either add `[CompleteSpace A]` or first prove a completion-invariance theorem.

For the current Path-α formalization, I recommend adding `[CompleteSpace A]`. It is mathematically faithful to the version of the theorem you are proving and avoids importing a large completion-invariance proof into the critical path.

Recommended final hypothesis profile for Path α:

```
[IsTateRing A]
[CompleteSpace A]
[T2Space A]
[NonarchimedeanRing A]
[IsStronglyNoetherian A]
(P : PairOfDefinition A)
[IsNoetherianRing P.A₀]
```

If later you prove completion invariance, you can remove `[CompleteSpace A]` from a wrapper theorem.

## Q-S24.META — Diagnostic for statement/proof hypothesis mismatch

Use all three proposed diagnostics, but make the central artifact a **proof-hypothesis ledger**.

For each lemma, record four columns:

```
1. Statement hypotheses
2. Source theorem hypotheses
3. Proof-route hypotheses
4. Downstream theorem hypotheses
```

Then require that every item in column 3 is either:
- already in column 1,
- derived by a proven lemma,
- or explicitly marked as an extra parameter.

This would have caught the current red flags:
- Example 6.38 preservation: proof-route hypothesis = noetherian A_0, so the theorem must either carry `[IsNoetherianRing P.A₀]` or use another route.
- Wedhorn 8.31: proof-route hypothesis = noetherian adic ring of definition, not merely abstract noetherianity of A.
- Wedhorn 8.34 relative standard cover: proof-route object = standard cover over O(C.base), not finite S ⊆ A spanning all of A.

A good pre-flight template is:

```
For each sorry:
  Statement:
  Literature statement:
  Literature proof uses:
  Lean proof route uses:
  Any proof-use not in statement?
  If yes: derive / add parameter / change route / mark invalid.
```

Also keep the taint graph. The sharper criterion is: **Audit not only syntactic dependencies, but also dependency by mathematical pattern.**

Examples of "taint patterns":
- strong noeth ⇒ noeth A_0
- single restriction is injective/surjective
- completed rational localization is algebraic IsLocalization
- standard cover over sub-rational base uses S ⊆ A spanning A
- domain cancellation in ratio splits

Any lemma whose proof route uses one of these patterns should be rechecked, even if it does not name the deleted lemma.

## Bottom-line recommendations

1. **Path α is sound** if you add `[CompleteSpace A]` and explicitly carry a noetherian pair of definition.
2. **Example 6.38 does preserve noetherianity of the induced ring of definition** when the input pair has noetherian `A_0`.
3. **Wedhorn 8.31 should be formalized with a noetherian pair of definition**, not merely abstract `[IsNoetherianRing A]`.
4. **Non-domain rings are allowed** in Wedhorn 8.28(b); remove `IsDomain` from final targets.
5. **Do not force all refinements to be over the original `A`**. For a rational base, standard covers and unit-ratio covers naturally live over `O(C.base)` or `O(L)` first, then are transported back.
6. **Add a proof-hypothesis ledger** to future decompose passes. It will catch statement-vs-proof-hypothesis mismatches before they become long dependency chains.
