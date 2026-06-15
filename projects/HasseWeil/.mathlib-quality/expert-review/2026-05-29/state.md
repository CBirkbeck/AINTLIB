# Expert-review session state — round 7

- Generated: 2026-05-29
- Audience: the standing arithmetic-geometry reviewer (rounds 1–6 context)
- Goal of brief: strategic guidance — is the dual-isogeny/degree-quadratic-form machinery (Silverman V.1.1 route) necessary for the Hasse bound, or is a leaner proof (e.g. Stepanov's elementary method) substantially cheaper to formalise? Emphasize reusable assets.
- Scope: the whole Hasse-bound strategy, framed around necessity of the deep machinery.
- Reply received: true (2026-05-29)
- Reply integrated: true (2026-05-29)

## Questions in the brief

| # | Question (verbatim from §9) |
|---|------------------------------|
| Q1 | Is a different proof of Hasse substantially cheaper to formalise — specifically Stepanov's elementary method (Bombieri/Schmidt: auxiliary polynomial + pole-order/Riemann–Roch on K(E), no isogenies, no quadratic form on End E) — given we already have K(E), Frobenius f↦f^q, division polynomials, and pole-order/valuation bookkeeping at O? Which reference / key estimate first? Pitfalls (genus-1 auxiliary-polynomial / derivative step; small-char derivative degeneracies)? Or is Stepanov a worse target than it looks? |
| Q2 | If we keep the current route: is the general dual unavoidable? Is there a path to "q r² − t rs + s² ≥ 0 ∀ r,s" needing only (a) the parallelogram law (deg a quadratic form) + (b) one non-degeneracy input — where (a) follows from a more primitive additivity than full duality? In particular: can the whole form be pinned down from just {1,π,V} and Vπ=[q], π+V=[t] (which we have), i.e. is the single dual identity (rπ−s)^ = rV−s cheaper than a general III.6.1? |
| Q3 | With 1−π proven separable, cleanest route to deg(1−π)=#ker (III.4.10a) — separable⇒étale fibre count via standard separable-field-extension theory (embeddings into K̄ fixing the subfield, or the trace form) — bypassing the bespoke ramification-over-places machinery? |
| Q4 | Worth re-modelling isogenies with a built-in basepoint/comorphism-compatibility constraint (kill the false-statement class at the type level), or carry explicit "genuine isogeny" hypotheses per lemma this late in the proof? |
| Q5 | Which §4 reusable assets survive a switch to Stepanov (Q1) or a leaner quadratic-form argument (Q2)? Pick the route stranding least finished work. |

## Ticket-board snapshot at brief time

The Hasse bound is assembled by a sorry-free skeleton (`hasse_bound_skeleton`, Silverman V.1.1) from exactly two open leaves:
- **Leaf 1 — qf_nonneg (Silverman III.6.3):** 0 ≤ q r² − t rs + s² for all r,s ∈ ℤ. Deep. Reduces (generic case) to the dual of r·π−s as a full isogeny: `genuineIsogSmulSub_pivot_witness`. Bottoms at Silverman III.6.1 (general dual) / VII.2 (formal-group pole bound for the addIsog construction). Char-divisible edges need [p]=V∘π.
- **Leaf 2 — V.1.3 / ker_deg (Silverman V.1.1 / III.4.10a):** deg(1−π) = #E(F_q). Reduces to the sharp residual `isogOneSub_negFrobenius_degree_eq_pointCount` (= deg = #ker for the separable 1−π). Pursued via the heavy Sinf/inertia function-field-places route (`l6_computationA`, `Sinf_sum_inertiaDeg_over_xIdeal_eq_pointCount`), mid-reformulation per Option I′; the false sub-route `nReduced_R_div_D_sq` (round-5 B2) is retired.

~48 `sorry`s remain, concentrated in the Leaf-1 (qf/dual) and Leaf-2 (V.1.3) machinery (OpenLemmaPrimitives, OpenLemmas, GapQfKernel, L6Witnesses, GapSpines). Build compiles cleanly; placeholder_guard.sh PASSES.

## Stuck points (from §8)

- 8.1 (Leaf 1, deep): positive-definiteness of the degree quadratic form ⇒ dual isogenies of general endomorphisms (III.6.1 / VII.2). Frobenius dual alone insufficient; mathlib has nothing here.
- 8.2 (Leaf 2, moderate): deg(1−π)=#E(F_q) = III.4.10(a) for the proven-separable 1−π; heavy places/ramification route, mid-reformulation; likely a shorter separable-étale route.

## Reference tags (from §2.2)

[Silverman] GTM 106 (III.4, III.5, III.6.3, V.1.1, VII.2); [Bombieri 1973] Sém. Bourbaki 430 (Stepanov); [Schmidt 1976] LNM 536; [Washington]; [mathlib] (division polynomials + Weierstrass only; no isogeny/dual/Hasse).

## Round-7 reusable assets (axiom-clean) — for cross-reference in Mode 2

Frobenius + deg π=q; Verschiebung = dual of Frobenius; separability⟺differential criterion (II.4.2c, NEW); 1−π separable with a_{1−π}=1; #ker(1−π)=#E(F_q); discriminant⇒bound wiring; place-at-O valuation identity orderTop(localExpand f)=ord_∞ f (NEW); deg[m]=m², [q]=Vπ, the III.6.3 identity for multiplication maps.
