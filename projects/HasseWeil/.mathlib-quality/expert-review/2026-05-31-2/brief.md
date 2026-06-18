# Review brief (round 14) — the theorem-of-the-square step, formalised: the precise obstruction and the cleanest descent

*Prepared 2026-05-31 for the same arithmetic-geometry reviewer as rounds 1–13. Self-contained; no repository access required. A short, technical follow-up to your round-13 answer: we took your theorem-of-the-square route, formalised down to the exact additivity step, and hit a concrete obstruction that maps onto your own "base-change caution." We want your steer on the cleanest formalizable shape before committing.*

---

## 1. State

Following round 13, we are proving the one remaining residual — the dual additivity `(rπ − s)^ = rV − s` — via the **theorem of the square** (additivity of the Pic⁰ pullback action), characteristic-free, **not** the Weil pairing.

We reduced it cleanly (κ-transport, machine-checked, non-circular) to a single class-group identity. Writing `α^*` for the pullback on `Pic⁰(E) ≅ E` (in our formalisation this is *extension of ideals* in the affine coordinate ring `R = F[E]`; `κ: E ≅ \mathrm{Cl}(R)`):

> **`hmul`.** For isogenies `α_1, α_2` and `α = α_1 + α_2`, and every class `c ∈ \mathrm{Cl}(R)`:
> `α^*(c) = α_1^*(c) · α_2^*(c)` in `\mathrm{Cl}(R)`.

This gives `(α_1+α_2)^ = α̂_1 + α̂_2` by conjugating with `κ`. We also formalised the **pullback-as-divisor** half (your III.6.2(b)) at the ideal level:

> `α^*(𝔪_Q) = \prod_{P:\,α(P)=Q} 𝔪_P^{\,e_α(P)}`,  `e_α(P) = \deg_i α` (constant, by III.4.10),

so `α^*(κ Q) = \sum_{α(P)=Q} e_α(P)\,κ(P)` (using that `κ` is a group homomorphism).

## 2. The obstruction we hit

Attempting `hmul` **at the ideal-extension level over the base field `𝔽_q`** stalls for two reasons:

- **(O1) The perfectness obstruction resurfaces.** The fibre points `P` with `α(P)=Q` are generally **not `𝔽_q`-rational** (they live over `\bar{𝔽}_q`), while our `\mathrm{Cl}(R)` and `κ` are over `𝔽_q`. So `\sum_{α(P)=Q} e_α(P)\,κ(P)` is not literally a sum of `𝔽_q`-point classes — the same imperfect-field issue that killed the char-0 §III.6.2(c) `Div⁰` proof.
- **(O2) The group law is "non-structural" at the ideal level.** The needed input is `α(P) = α_1(P) + α_2(P)` (a statement about *points* and the group law), but the comorphism of the **sum isogeny** `α_1 + α_2` is built from the *addition-formula* pullback, and we see no direct ideal-theoretic relation between `(α_1+α_2)^*(𝔪_Q)` and `α_1^*(𝔪_Q), α_2^*(𝔪_Q)`. The additivity seems to be inherently a *divisor/point* statement, not an *ideal-extension* one.

This is exactly your round-13 **base-change caution** ("don't expect a constructed function over an imperfect field; prove over an algebraically closed field and descend").

## 3. Our intended fix (please sanity-check)

Work geometrically over `K = \bar{𝔽}_q`, where every fibre point is rational:

1. Prove the theorem of the square as a **divisor/point** statement over `K`:
   `[(α_1+α_2)^* D] = [α_1^* D] + [α_2^* D]` in `\mathrm{Pic}^0(E_K)` for `D ∈ \mathrm{Div}^0(E_K)`,
   via: the difference divisor has degree 0 and **sums to `O`** (because `(α_1+α_2)(P)=α_1(P)+α_2(P)` and `κ_K` is a group hom), hence is principal by **Abel (III.3.5)** — which in our setup *is* the statement that `κ_K: E(K) → \mathrm{Cl}(R_K)` (equivalently mathlib's `\mathrm{Point.toClass}`) is an injective group homomorphism.
2. Conclude `(α_1+α_2)^ = α̂_1 + α̂_2` as **point maps over `K`**.
3. **Descend** to `𝔽_q`.

Our endgame already operates over `E(\bar{𝔽}_q)` (we pin `[\deg(rπ−s)]=[N]` at the geometric-point level, using that `E(\bar{𝔽}_q)` is infinite while `E[k]` is finite), so an `\bar{𝔽}_q`-level additivity is exactly what the rest consumes — step 3 may even be unnecessary.

## 4. Questions

- **Q1 (shape).** Is the **divisor/point form over `\bar{𝔽}_q`** the right formalisation target (rather than the ideal-`classMap` form)? Concretely, is the cleanest statement `[(α_1+α_2)^* D] = [α_1^* D] + [α_2^* D]` in `\mathrm{Pic}^0` for `D∈\mathrm{Div}^0`, proved by "degree 0 + sums to `O` ⟹ principal (Abel)", with the *sums-to-`O`* step coming straight from the group law `(α_1+α_2)(P)=α_1(P)+α_2(P)`?

- **Q2 (the sums-to-`O` computation).** The crux is: the divisor `(α_1+α_2)^*((Q)−(O)) − α_1^*((Q)−(O)) − α_2^*((Q)−(O))` sums to `O`. Is this immediate from `κ_K` being a group hom applied to the fibre identity, or does it need the genuine **theorem of the square on `E×E`** (`m^*L ≅ p_1^*L ⊗ p_2^*L`) pulled back along `(α_1,α_2)`? We would much prefer to **avoid building a product-curve `E×E` divisor API**; is the pulled-back-to-`E` computation self-contained, and what is the minimal lemma about fibres of `α_1+α_2` vs `α_1,α_2` that it needs?

- **Q3 (descent).** Since our consumer only needs the additivity as an equality of **point maps over `\bar{𝔽}_q}`**, do we need any descent to `𝔽_q` at all? If we do (e.g. to keep `\deg` over `𝔽_q`), is "equality of `𝔽_q`-morphisms can be checked after the faithfully-flat extension `𝔽_q → \bar{𝔽}_q`" the right and sufficient principle, with no further subtlety?

- **Q4 (a shortcut we might be missing).** We have, unconditionally: `κ: E ≅ \mathrm{Pic}^0` a **group iso over any field**; the dual relation `α̂ ∘ α = [\deg α]`; `π̂=V`, `(rπ)^=rV`, `[n]^=[n]` (all non-circular); and the geometric injectivity `[m]=[n]` on `E(\bar{𝔽}_q) ⟹ m=n`. Given that `κ` is already a group homomorphism, is there a route to the **single** instance `(rπ + [-s])^ = (rπ)^ + [-s]^` that is lighter than the full theorem-of-the-square divisor computation — e.g. purely from `κ`'s additivity plus the Pic⁰-pullback functoriality we already have, without re-deriving the addition-formula divisor relation?

## 5. Status / metadata

- **Leaf 2**: closed. **Leaf 1 generic**: assembled, axiom-clean, modulo the single theorem-of-the-square identity `hmul` (+ pre-existing `CoordHom`/`hpoint` plumbing).
- **Shipped axiom-clean toward `hmul`**: the pullback-as-divisor `α^*(𝔪_Q)=∏ 𝔪_P^{e_α(P)}` (III.6.2(b)); the κ-transport reduction of the dual additivity to `hmul`; `π̂=V`, `(rπ)^=rV`, `[n]^=[n]`.
- **Obstruction**: ideal-level `hmul` over `𝔽_q` blocked by (O1) non-rational fibre points (imperfectness) and (O2) the group-law linkage being non-structural in ideal-extension. Intended fix: divisor/point theorem of the square over `\bar{𝔽}_q` + (possibly) descent.
- Build green; placeholder guard passing. Prepared 2026-05-31 (round 14).
