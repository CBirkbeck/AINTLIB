# Review brief (round 9, follow-up) — Leaf 2: base change hit the **same** generic-fibre wall; which route to `#ker(1−π) = deg(1−π)`?

*Prepared 2026-05-29 for the same arithmetic-geometry reviewer as rounds 1–8. Self-contained; no repository access required. Still on **Leaf 2 only** (`deg(1−π) = #E(𝔽_q)`).*

---

## 1. What we did with your round-8 advice, and what happened

You advised (round 8): prove `deg(1−π) = #E(𝔽_q)` by base-changing to `K̄ = 𝔽̄_q` and applying the separable-isogeny **geometric** fibre count there (Silverman III.4.10a), since over `K̄` residue degrees vanish.

We implemented as much as the existing library allows. **Good news:** the "fibre = `E(𝔽_q)`" half is *already fully formalised* (axiom-clean): over `K̄` we have the geometric Frobenius `(x,y) ↦ (x^q,y^q)` on points, its fixed locus, and the identity
$$\#\ker\bigl(1 - \mathrm{Frob}\bigr)\big|_{K̄\text{-points}} \;=\; \#E(\mathbb{F}_q),$$
proved via the coordinate fixed-field lemma `a^q=a ⟺ a∈𝔽_q`, exactly as you outlined.

**The problem:** the *other* half — the III.4.10a core `#\ker = \deg` over `K̄` — **does not close**, and it fails for the **same** reason the K-level route failed. So base change *relocated* the obstruction but did not remove it.

## 2. The precise obstruction (it recurs over `K̄`)

The III.4.10a proof you cite goes through **II.2.6(b)**: a *generic* fibre of a nonconstant map of smooth curves has `deg_s` geometric points, then translation-invariance spreads this to every fibre. In our formalisation, the only theorem that produces "fibre cardinality = separable degree" is stated for a curve map equipped with a **coordinate-ring algebra homomorphism** `\mathcal{O}(E_2) \to \mathcal{O}(E_1)` (a "`CoordHom`"). And `1−π` **provably has no `CoordHom`** — its comorphism `(1−π)^*` exists on the *function fields* but does **not** restrict to the affine coordinate rings, because `(1−π)^*x` has poles at the *affine* kernel points (every `P ∈ E(𝔽_q)` has `(1−π)(P)=O`). (This is the same fact behind a divisibility statement we earlier confirmed false; counterexample `E: y²=x³−x / 𝔽_5`.) Base-changing to `K̄` does not help: `(1−π)_{K̄}` still has no coordinate-ring `CoordHom`.

Worse, there is a **circularity trap** we verified: the project's reduction "`#ker = deg` from a *fibre-size witness* `∃P₀, \#(\text{fibre over } \varphi P_0) = \deg_s`" is useless for `1−π`, because the only fibre we can compute directly is the one over `O`, which *is* the kernel — giving `#\ker = #\ker`, no information about `\deg`. A genuine **generic** (non-kernel) fibre is needed, and that is exactly what the `CoordHom` would provide. The trap recurs verbatim over `K̄`.

So: **both** of your recommended routes so far — round-7 "separable ⇒ unramified fibre count" and round-8 "base change + geometric fibre count" — bottom out at the *same* missing ingredient: a way to count a **generic fibre of `1−π`** (equivalently, to handle its degree) **without a coordinate-ring `CoordHom`**, which `1−π` does not have.

## 3. The two routes we can see, and what each costs

**Route R1 — a `CoordHom`-free generic-fibre theorem over `K̄`.** Build a genuine base-changed isogeny `(1−π)_{K̄}` (comorphism via the function-field tensor equivalence `K̄(E) ≅ \mathrm{Frac}(K̄ \otimes_K \mathcal{O}(E))`, point-map via geometric Frobenius), and a fibre-count theorem routed through `\mathrm{finSepDegree}` over the algebraically closed base (`[L:M]` embeddings into `\overline{M}`) rather than through coordinate-ring primes. This needs a place↔point bijection over `K̄` that currently lives only in the `CoordHom`-bound track. Estimated large.

**Route R2 — over-`K` Galois, no base change at all.** Since `\ker(1−π) = E(𝔽_q)` is **entirely `K`-rational**, the finite separable extension `K(E)\,/\,(1−π)^*K(E)` should be **Galois**, with Galois group the kernel acting by **translation**: for `k ∈ \ker(1−π)`, translation-by-`k` is a `K`-automorphism `τ_k` of `K(E)` fixing `(1−π)^*K(E)`, and `k ↦ τ_k` is an isomorphism `\ker(1−π) \xrightarrow{\sim} \mathrm{Gal}`. Then
$$\deg(1−π) = [K(E):(1−π)^*K(E)] = \#\mathrm{Gal} = \#\ker(1−π) = \#E(\mathbb{F}_q),$$
with **no generic fibre, no `CoordHom`, no base change, no residue degrees.** The project already has the *consumer* scaffold (a lemma "`#ker = deg` from a Galois witness `\mathrm{Aut} ≅ \ker` + normality"); the undischarged content is (a) constructing the translation automorphisms `τ_k : K(E) ≃_K K(E)` (≈200 LOC, comparable to our hardest existing construction, the addition-formula comorphism) and (b) the normality/`IsGalois` proof.

## 4. Questions

**Q1.** Is **R2 (over-`K` Galois)** the "right" formalisation of III.4.10a for `1−π` — i.e. is it standard that, *because the kernel is `K`-rational*, `K(E)/(1−π)^*K(E)` is Galois with group `\ker(1−π)` acting by translation, giving `\deg = \#\ker` directly? If so, this looks strictly cleaner than anything fibre-based for our setting. Are there traps (e.g. is normality automatic here, or does it need `\ker` to be `K`-rational *and* something else)?

**Q2.** Is there a route to `#\ker(1−π) = \deg(1−π)` that needs **neither** a generic-fibre/`CoordHom` **nor** the translation-automorphism construction — e.g. a direct identity `\deg(1−π) = \#\mathrm{Hom}_{(1−π)^*K(E)}(K(E), \overline{\cdot})` from separability + an embeddings-vs-translations count, using only that `(1−π)^*` exists at the *function-field* level (which it does)?

**Q3.** If you do recommend R1 instead, what is the lightest `CoordHom`-free way to get "geometric fibre cardinality = `\deg`" for a separable isogeny over `K̄` — is there a standard reduction to a finite-separable-field-extension embedding count that avoids scheme-theoretic fibres entirely?

**Meta.** Two of your routes have now hit the same `CoordHom`/generic-fibre wall. We suspect the *real* content of Leaf 2, in our function-field-first formalisation, is the **translation-automorphism / Galois** structure (R2), not fibre counting. Do you agree that's where to invest — or is there a fourth route we're missing?

## 5. Status / metadata
- Shipped axiom-clean: `#E(𝔽_q) ≤ deg(1−π)`; and (over `K̄`) `#\ker(1−\mathrm{Frob}) = #E(𝔽_q)`. Open: the reverse `\deg(1−π) ≤ #E(𝔽_q)` = the `#\ker=\deg` core.
- Leaf 1 (the restricted Frobenius-plane dual `(rπ−s)^=rV−s`) is unaffected by all of this and remains the alternative near-term target.
- Build green. Prepared 2026-05-29 (round 9, follow-up).
