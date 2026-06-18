# Review brief (round 10, follow-up) — Leaf 2 is CLOSED 🎉; Leaf 1 is the last leaf — which infrastructure?

*Prepared 2026-05-29 for the same arithmetic-geometry reviewer as rounds 1–9. Self-contained; no repository access required.*

---

## 1. Leaf 2 (V.1.3, `deg(1−π) = #E(𝔽_q)`) is CLOSED — thank you

Your rounds 7–9 guidance worked. `deg(1−π) = #E(𝔽_q)` is now **fully formalised, axiom-clean** (no `sorry`, no added axioms). The winning route was exactly the embeddings-classification you prescribed in round 9, with the round-8 correction:

- `deg(1−π) = #(K(E) →_{(1−π)^*K(E)} Ω)` is essentially **free** — `finSepDegree` is *defined* as the cardinality of embeddings into the algebraic closure, and `1−π` is separable.
- Every such embedding is classified as a **translation** `τ_T`, `T ∈ ker(1−π)`, via the σ-vs-σ₀ **torsor** difference (your warning was on point: the naive "`Q_σ − \mathrm{Frob}(Q_σ)` is Frobenius-fixed" is false because `(1−π)^*x` is transcendental; the *difference of two embeddings* is the right fixed object), descending by `a^q = a ⟺ a ∈ 𝔽_q`.
- `ker(1−π) = E(𝔽_q)` was already in hand. No `IsGalois`-first, no generic fibre, no `CoordHom`.

So `\hat{\text{hasse\_bound\_skeleton}}` is now a sorry-free body whose only remaining input is **Leaf 1**.

## 2. Leaf 1 (`0 ≤ q r^2 − t rs + s^2` for all `r,s`) — and a correction to round 7

We attempted Leaf 1 via your round-7 **restricted-dual** suggestion (`\widehat{r\pi-s} = rV - s` on the Frobenius plane, then `(rV-s)(r\pi-s) = [N]` ⟹ `\deg(r\pi-s)=N≥0`). **It does not obviate the formal-group "Wall A", for a structural reason we should flag:**

- In our formalisation `\deg` is read off the **function-field comorphism** (`[K(E) : (r\pi-s)^*K(E)]`), and `r\pi - s` is generically **inseparable** (its differential multiplier is `a_{r\pi-s} = -s`, which vanishes in `K` exactly in the char-divisible case, and even when `≠0` the *Frobenius part* makes the map non-étale). So `\deg(r\pi-s)` is **not** determined by the point map; the equality `\deg(r\pi-s) = N` genuinely requires a `\beta_{\mathrm{dual}} = rV-s` whose **comorphism** satisfies `(r\pi-s)^* \circ (rV-s)^* = [N]^*` — a *function-field-level* identity (we call it the "double-Vieta match"), which presupposes the genuine comorphism of `rV-s`.
- The only construction of that comorphism in the project is via the addition-formula pullback (`addIsog`), whose well-definedness needs the **V-side pole-order bound at `O`** = the kernel-of-reduction / Silverman VII.2 formal-group content (our "Wall A"). Even granting Wall A, the double-Vieta match (Wall B) and `\mathrm{IsDualOf}(rV-s)(r\pi-s)` remain, both at the comorphism level.
- **The Leaf-2 escape does NOT transfer.** Leaf 2 closed because `\#\ker(1-\pi) = E(\mathbb F_q)` is *computable*. For `r\pi-s`, `\#\ker` is an opaque torsion count; the embeddings technique yields `\deg(r\pi-s) = \#\ker(r\pi-s)` (when separable) but gives **no** independent handle on `= N`. There is no point-level shortcut for the **inseparable degree**.

What IS already formalised (axiom-clean): the **point-map**-level composition `(rV-s)(r\pi-s) = [N]` on `E`, the relations `V\pi = [q]`, `\pi + V = [t]`, and the reduction "from a genuine dual pair with `\beta_{\mathrm{dual}}\circ\beta=[N]` and `0<\deg\beta`, conclude `\deg\beta = N`" (Silverman III.6.1(a)+III.6.2(a), our "Wall C"). The irreducible gap is purely the **comorphism-level** dual.

## 3. The question

Leaf 1 is now isolated to a single classical fact realised at the **function-field/comorphism** level, and it needs genuine new infrastructure (none of it in mathlib, which has no isogenies/dual/formal-groups). We see two textbook routes and want your steer:

**Route A — formal-group dual (Silverman III.6 + VII.2).** Build the V-side pole-order bound (kernel-of-reduction is a subgroup ⟹ `\mathrm{ord}_O` of the V-side `addIsog` `x`-coordinate is negative), construct `rV-s` with its genuine comorphism, prove `\mathrm{IsDualOf}(rV-s)(r\pi-s)` and the double-Vieta match `(rV-s)(r\pi-s)=[N]` at the comorphism level, then Wall C finishes. This is "most faithful to Silverman" but is a multi-week formal-group development.

**Route B — Weil pairing / Tate module.** For `\ell \neq p`, on `T_\ell E \cong \mathbb Z_\ell^2` the endomorphism `r\pi - s` acts with `\det = \deg(r\pi-s)` and characteristic polynomial `X^2 - tX + q` (evaluated to give `qr^2 - trs + s^2`); the Weil pairing gives `\det = \deg`, and positivity of the QF is then the determinant being a norm. Avoids the dual/formal-group entirely but needs `\ell`-adic Tate-module + Weil-pairing infrastructure (also absent from mathlib).

- **Q1.** Which of Route A / Route B is the lighter formalisation target *given what's already shipped* (Frobenius, V with `V\pi=[q]`, `\pi+V=[t]`, the point-map composition `(rV-s)(r\pi-s)=[N]`, Wall C, the separability/differential criterion, the place-valuation machinery)? Route A reuses the most; Route B may be conceptually cleaner but starts from nothing.
- **Q2.** For Route A specifically: is the V-side pole bound (Wall A) genuinely the crux, or is there a way to get `\mathrm{IsDualOf}(rV-s)(r\pi-s)` + the comorphism-level `(rV-s)(r\pi-s)=[N]` that *starts* from the already-shipped point-map composition + Wall C and only needs a *degree/comorphism rigidity* input (rather than constructing `rV-s` from scratch via `addIsog`)? I.e., is there a "soft" upgrade from point-map dual to comorphism dual for this specific pair?
- **Q3.** Is there a third route to `0 ≤ qr^2 - trs + s^2` we're missing that does **not** require pinning `\deg(r\pi-s) = N` at all — e.g. exploiting that we now have `\#E(\mathbb F_q) = \deg(1-\pi)` (Leaf 2) to bound `t` more directly, or a parallelogram/Cauchy–Schwarz argument on `\deg` that needs only its values on `\{1, \pi, V\}` plus the *already-shipped* point-map bilinearity?
- **Meta.** Leaf 1 is genuinely the inseparable-degree/formal-group content; Leaf 2's point-level tricks are exhausted on it. Before we commit multi-week effort, is there any chance Q3 (a route avoiding `\deg(r\pi-s)=N` entirely) exists?

## 4. Status / metadata
- Leaf 2 / V.1.3: CLOSED axiom-clean. `hasse_bound_skeleton` is a sorry-free body; its sole remaining `sorryAx` is Leaf 1 (`qf_nonneg`).
- Shipped toward Leaf 1: point-map composition `(rV-s)(r\pi-s)=[N]`, `V\pi=[q]`, `\pi+V=[t]`, Wall C (`signed_degree_of_genuine_dual_pair`), separability⟺differential, the place-valuation identity.
- Build green throughout; placeholder guard passing. Prepared 2026-05-29 (round 10, follow-up).
