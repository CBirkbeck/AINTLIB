# Review brief (round 12) — the Pic⁰ route is *degree-blind*: which pullback-level route for the inseparable degree?

*Prepared 2026-05-30 for the same arithmetic-geometry reviewer as rounds 1–11. Self-contained; no repository access required. A focused follow-up: your round-11 recommendation (Pic⁰ dual) turned out, on formalisation, to be degree-blind for our specific endomorphism, and we want your steer on the right pullback-level replacement.*

---

## 1. Recap and the round-11 decision

We are formalising the Hasse bound for `E/𝔽_q`. **Leaf 2** (`deg(1−π) = #E(𝔽_q)`) is closed. **Leaf 1** is the quadratic-form positivity `0 ≤ q r² − t r s + s²`, which reduces to the **signed degree identity** `deg(rπ − s) = N`, `N := q r² − t r s + s²` (since `deg ≥ 0`). Here `π` is the `q`-power Frobenius endomorphism, `t` its trace, and `deg φ := [K(E) : φ^* K(E)]` is the degree of the function-field comorphism.

In **round 11** you confirmed our finding that the signed identity needs the genuine dual isogeny (`(rV − s) = \widehat{rπ − s}` with `\widehat{β}β = [\deg β]`), and recommended building it via **Pic⁰**: `\mathrm{Pic}^0(E) ≅ E` plus functoriality, since Pic⁰ gives dual additivity naturally. We committed to that route.

## 2. What we built (Pic⁰ infrastructure, all formally verified, axiom-clean)

Substantial and reusable — but, as §3 explains, not able to close Leaf 1:

- **`E ≅ \mathrm{Pic}^0(E)`**: the group isomorphism `E(F) ≅ \mathrm{Cl}(F[E])` (ideal class group of the affine coordinate ring), unconditional over any field — i.e. **genus-1 Riemann–Roch**, which the library did not previously contain. (Proved by reducing every ideal class to a degree-≤1 representative via an exact dimension count, no finiteness of `F` assumed.)
- **Class-group functoriality**: the relative-norm and extension maps on class groups, with `\mathrm{norm} ∘ \mathrm{ext} = (\cdot)^{[\deg]}` at the class level.
- The **isogeny → class-group** bridge realising an isogeny's action on `\mathrm{Pic}^0`.

## 3. The finding — Pic⁰ is **degree-blind to inseparability**

When we formalised the III.3.4 functoriality (the compatibility of `E ≅ \mathrm{Pic}^0(E)` with an isogeny), the picture is:

- An isogeny `α` with comorphism `α^*` acts on a rational point's maximal ideal `\mathfrak m_P` by **contraction**: `\mathrm{Pic}^0`-class of `α(P)` = class of `(α^*)^{-1}(\mathfrak m_P)` (the **comap**/transpose), *not* the extension or the norm.
- Consequently the dual-composition that Pic⁰ produces, `\mathrm{norm} ∘ \mathrm{comap}`, evaluates on a prime to `\mathfrak p^{f}` where `f` is the **residue/inertia degree** — i.e. it sees only the **separable** part of the degree.

But in our formalisation `\deg(α) = [K(E) : α^* K(E)]` is the **full** degree, including the **inseparable** factor. And `rπ − s` is **generically inseparable**: its invariant-differential multiplier is `−s`, so for `p ∣ s` the map is inseparable, and the Frobenius summand contributes an inseparable part in general. Therefore the Pic⁰ point-level dual relation computes the *wrong* (separable) degree and **cannot pin `\deg(rπ − s) = N`**. Base-changing to `\bar{𝔽}_q` does not help: the full degree is a function-field/pullback-level invariant, invisible to the point-divisor (`\mathrm{Pic}^0`) machinery.

This re-confirms, concretely, a conclusion we had actually reached *before* round 11 — *"there is no point-level escape for Leaf 1 (unlike Leaf 2); the inseparable degree lives at the pullback level."* The round-11 Pic⁰ pivot was right that the **dual exists**, but its **point-level realisation is degree-blind**. We should have surfaced the inseparability obstruction more sharply in the round-11 brief; that's on us.

## 4. The question — which **pullback-level** route?

The signed `\deg(rπ − s) = N` is fundamentally a **function-field / inseparable-degree** statement. We see two classical pullback-level routes (both seen by our `\deg` because they live at the comorphism level), plus a possible decomposition:

**Route A — formal-group dual (Silverman IV.1 + VII.2).** Construct the genuine `rV − s` **comorphism** via the kernel-of-reduction pole bound at `O`: the formal group law `z(P + Q) = \hat F(z(P), z(Q))` (in the local parameter `z = −x/y`) controls `\mathrm{ord}_O` of the addition-formula pullback, which makes `rV − s` a genuine degree-bearing isogeny. Then the double-Vieta `(rV − s)(rπ − s) = [N]` at the **pullback** level + the degree-extraction lemma. The single hard residual is the coefficient-by-coefficient match of the explicit formal group law (built from `a_1,\dots,a_6`) against the local-expanded chord–tangent addition formula (a multi-pass power-series development).

**Route B — kernel-quotient (Silverman III.4).** Build the quotient curve `E / \ker(rπ − s)` and obtain the dual's **comorphism** from the universal property (`\widehat{β}` as the cofactor of `[\deg β]` through `β`). This yields the comorphism directly and is pullback-level.

- **Q1.** Given the inseparability obstruction (point-level methods are blind to it), which of **A** or **B** is the lighter route to the genuine **comorphism** dual of `rπ − s`, reusing what we have (`π`, `V` with `Vπ = πV = [q]` and `π + V = [t]` and a *proved* genuine `\mathrm{IsDual}(V, π)`; the point-map composition `(rV − s)(rπ − s) = [N]`; genuine-isogeny extensionality; the separable/inseparable degree theory)?
- **Q2.** For **B**: does the quotient construction `E / \ker(β)` cleanly handle the **inseparable** case `p ∣ s`, where `\ker(β)` is a non-étale (infinitesimal) group scheme? In the usual formalisation the quotient is built via the separable/Frobenius factorisation `β = β_{\mathrm{sep}} ∘ \mathrm{Frob}^k`; does that route deliver the comorphism *including* the inseparable factor `p^k`, or does it just relocate the same formal-group content?
- **Q3.** Is there a **degree-decomposition** shortcut? Write `rπ − s = \mathrm{Frob}^k ∘ σ` with `σ` separable, so `\deg_{\mathrm{insep}}(rπ − s) = p^k` and `\deg = p^k \cdot \deg_{\mathrm{sep}}`. The **separable** degree `\deg_{\mathrm{sep}} = \#\ker_{\mathrm{sep}}` *is* visible to point-level/Pic⁰ methods (which we now have via `E ≅ \mathrm{Pic}^0`). Could we compute `\deg_{\mathrm{insep}}` directly from the differential / the power of Frobenius dividing `rπ − s`, and multiply — getting the full `\deg` **without** the formal-group pole bound? Is `k` cleanly readable off `(r, s)` (e.g. `k = v_p(s)` in the relevant range)?
- **Q4.** Anything we're missing — a third pullback-level route, or a way to make the now-available `E ≅ \mathrm{Pic}^0` asset contribute to the **inseparable** part (so the Pic⁰ work isn't wasted)?

## 5. Status / metadata

- **Leaf 2**: closed, axiom-clean.
- **Leaf 1**: open; reduces to the signed, **pullback/inseparable-level** identity `\deg(rπ − s) = N`. The Pic⁰ infrastructure (`E ≅ \mathrm{Pic}^0`, class-group functoriality, the isogeny bridge) is formally verified but degree-blind for this. Reverting to a pullback-level route.
- **Shipped toward a pullback-level dual** (all axiom-clean): `π`, `V` with `Vπ = πV = [q]`, `π + V = [t]`, a *proved* genuine `\mathrm{IsDual}(V, π)`; point-map composition `(rV − s)(rπ − s) = [N]`; genuine-isogeny extensionality; the degree-extraction lemma; `0 < \deg` for every genuine isogeny; the separability ⟺ differential criterion.
- Build green throughout; placeholder guard passing. Prepared 2026-05-30 (round 12).
