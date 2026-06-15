# Review brief (round 15) — the whole bound is one theorem away: how to build the two ingredients (divisor pullback + addition-formula linkage)?

*Prepared 2026-05-31 for the same arithmetic-geometry reviewer as rounds 1–14. Self-contained; no repository access required. A focused build-planning follow-up: we took your round-14 theorem-of-square route, formalised it down to two precise missing ingredients, and want your steer on the cleanest way to build them (and whether a slicker route exists).*

---

## 1. State — the entire generic bound is reduced to one predicate

Following round 14, the generic Hasse bound `deg(rπ − s) = N` is now reduced — machine-checked, axiom-clean, non-circular, with the end-to-end wiring verified — to the **single** dual-additivity predicate

> **`DualAdd`.** For all `Q`:  `(rπ − s)^(Q) = (rπ)^(Q) + (−s)(Q)`   (i.e. `\widehat{rπ−s} = rV − s`, Silverman III.6.2(c)).

We have, all axiom-clean and **non-circular** (never assuming `deg(rπ−s)=N`):
- `E ≅ Pic⁰(E)` (genus-1 Riemann–Roch); the Pic⁰ dual `α̂ = κ⁻¹∘α^*∘κ`; the dual relation `α̂α=[\deg α]`; the unconditional imperfect-field `relNorm=comap` ("`hnat`");
- the partial duals `π̂=V`, `\widehat{[n]}=[n]`, and **`\widehat{rπ}=rV`** (the last via your III.6.1(a) uniqueness with the *independently known* degree `\deg(rπ)=r²q` — so it is **not** circular);
- the discharged Miller machinery (the Miller hypothesis holds in all characteristics), and `κ`-divisor additivity `κ(P+Q) \sim κ(P)+κ(Q)` (the group law on Pic⁰ via divisors);
- the certified equivalence: `DualAdd ⟺ ∀Q,\ σ(Δ_Q)=O`, where `Δ_Q = (rπ−s)^*((Q)−(O)) − (rπ)^*((Q)−(O)) − (−s)^*((Q)−(O))` and `σ` is the group-law sum.

## 2. The two missing ingredients

`DualAdd` = the pulled-back theorem of the square `(α_1+α_2)^*L \simeq α_1^*L\otimes α_2^*L` on `Pic⁰`, specialised to `α_1=rπ, α_2=[−s]`. Two things are genuinely absent from our library:

- **(I) A divisor pullback `α^*` on the projective-divisor type.** We have the *pushforward* (and `κ(P)=(P)−(O)` with its additivity mod principal), and at the *ideal* level we have the pullback-as-divisor factorisation `α^*(𝔪_Q)=\prod_{α(P)=Q} 𝔪_P^{\,e_α(P)}` (`e_α(P)=\deg_i α`). But there is no `ProjectiveDivisor`-level operation `D \mapsto α^*D`.
- **(II) The addition-formula fibre linkage.** The genuine content of `σ(Δ_Q)=O`: relating the *fibres* of `rπ+[−s]` to those of `rπ` and `[−s]`. The chord-tangent/addition formula is what Silverman's char-0 p.84 proof uses (over `K(E_1)`); over `\bar{𝔽}_q` (perfect, all fibre points rational) it is char-free, but we have no Lean lemma assembling the three fibres into a single principal divisor `\mathrm{div}(f)`. (Our existing "addition-pullback" code is about differentials/transcendence, not this divisor identity.)

We have verified (machine + your Q2) that this **cannot** be shortcut by: the group law alone (fibres of a sum are not fibrewise); uniqueness (circular, needs `\deg=N`); the image-side theorem of the square; or the Weil pairing (heavier, agreed to avoid).

## 3. One observation we want you to evaluate (a possible slicker route)

`End(E) ⊇ ℤ[π] ≅ ℤ[t]/(t²−tt+q)`, an imaginary quadratic order, and the dual restricted to `ℤ[π]` is the **conjugation** `a+bπ \mapsto a+b\bar π = a+bV` (since `\bar π = V`). Conjugation is **additive for free** (ring structure). So `DualAdd` would follow immediately from:

> `α̂ = \mathrm{conj}(α)` for all `α ∈ ℤ[π]`,  equivalently  `α̂` is the unique `β` with `β = [\mathrm{tr}\,α] − α`.

We can prove the Cayley–Hamilton relation `(rπ−s)² − [rt−2s](rπ−s) + [N] = [0]` *unconditionally* (from `π+V=[t]`, `Vπ=[q]`). The trouble: identifying `α̂` with `[\mathrm{tr}\,α]−α` again seems to need `\deg α = N(α)` (the norm form), which is circular. **Q3 below asks whether this `ℤ[π]`-conjugation route has a non-circular completion** we are missing — it would avoid both ingredients entirely.

## 4. Questions

- **Q1 (divisor pullback).** What is the cleanest way to give `ProjectiveDivisor` a pullback `α^*` for an isogeny `α` — define it from the shipped *ideal* factorisation `α^*(𝔪_Q)=\prod 𝔪_P^{e_α(P)}` (i.e. `α^*((Q)) := \sum_{α(P)=Q} e_α(P)\,(P)` over `\bar K`), or as a primitive `ProjectiveDivisor`-level operation with a separate `degree`/`κ`-compatibility lemma? Which keeps the theorem-of-square proof shortest?

- **Q2 (the fibre linkage / `σ(Δ_Q)=O`).** What is the minimal, cleanest proof of `σ(Δ_Q)=O` (equivalently `Δ_Q` principal) over `\bar K`, avoiding an `E×E` API? Is the intended path: (a) construct the explicit Miller/chord-tangent function `f` with `\mathrm{div}(f)=Δ_Q` from the addition formula, or (b) compute `σ(Δ_Q)` directly via `σ(α^*((Q)−(O)))=α̂(Q)` plus a fibre-sum identity, or (c) something else? What is the *one* addition-formula divisor identity that does the work?

- **Q3 (the `ℤ[π]`-conjugation shortcut).** Is there a non-circular way to prove `α̂ = [\mathrm{tr}\,α] − α` on `ℤ[π]` (hence `DualAdd`) — e.g. from Cayley–Hamilton + the dual relation `α̂α=[\deg α]` + something that pins `\deg α` *without* assuming `\deg=N`? Or is this provably circular, so that the theorem-of-square divisor build is unavoidable?

- **Q4 (scope/order).** Assuming the divisor build: is ingredient (I) + (II) a *bounded* development on top of our Miller/`κ`-divisor machinery (estimate?), or does it effectively rebuild a chunk of intersection/divisor theory? And what is the cleanest build *order*?

## 5. Status / metadata

- **Leaf 2**: closed. **Leaf 1 generic**: reduced — axiom-clean, non-circular, wiring-verified — to `DualAdd` (dual additivity III.6.2(c)) + existing `CoordHom`/`hpoint` plumbing.
- **Two missing ingredients**: (I) divisor pullback `α^*` on `ProjectiveDivisor`; (II) the addition-formula fibre linkage (`σ(Δ_Q)=O`). Both char-free over `\bar K`; both absent from the library.
- **Shipped non-circular**: `E≅Pic⁰`, the Pic⁰ dual + `α̂α=[\deg]`, `hnat`, `π̂=V`, `\widehat{rπ}=rV`, `\widehat{[n]}=[n]`, the Miller machinery + `κ`-divisor additivity, the `DualAdd ⟺ σ(Δ_Q)=O` certification, Cayley–Hamilton for `rπ−s`.
- Build green; placeholder guard passing. Prepared 2026-05-31 (round 15).
