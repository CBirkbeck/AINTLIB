# Review brief (round 11) — Leaf 1 endgame: does "narrow Route A" actually avoid dual existence?

*Prepared 2026-05-29 for the same arithmetic-geometry reviewer as rounds 1–10. Self-contained; no repository access required. This is a short, focused follow-up: we believe we have found a structural fact that bears directly on your round-10 recommendation, and we want your check before committing multi-week effort.*

---

## 1. One-paragraph recap

We are formalising the Hasse bound `|#E(𝔽_q) − q − 1| ≤ 2√q` for an elliptic curve `E/𝔽_q`, following Silverman V.1.1. Write `q = |𝔽_q|`, let `π` be the `q`-power Frobenius endomorphism of `E`, and `t = q + 1 − #E(𝔽_q)` its trace. The bound is equivalent to the quadratic-form positivity

> `0 ≤ q r² − t r s + s²` for all integers `r, s`   (★)

(Silverman III.6.3 → V.1.1). **Leaf 2** — the identity `deg(1 − π) = #E(𝔽_q)`, which pins `t` — is **closed, axiom-clean**, via the embeddings-as-translations/torsor route you prescribed in round 9. **Leaf 1** is exactly (★), and is the only thing left. This brief is entirely about Leaf 1.

Throughout, endomorphisms of `E` act on the function field `K(E)` by pullback (comorphism), and for an isogeny `φ` we write `deg φ = [K(E) : φ^* K(E)]` (the degree of the comorphism field extension; always `≥ 0`, and we have now shown it is always `> 0` for a genuine isogeny, since `φ^*` is an injective field homomorphism into a finite extension). `[n]` denotes multiplication by `n ∈ ℤ`.

## 2. The reduction of Leaf 1, and what is shipped

Since `deg ≥ 0`, the positivity (★) is **immediate** from the signed degree identity

> `deg(rπ − s) = q r² − t r s + s² =: N`   (the **signed degree identity**).

So Leaf 1 = the signed degree identity, for all `r, s ∈ ℤ`. We treat the "generic" case (`r, s` both nonzero in `𝔽_q`) here; the char-divisible edge cases (`p ∣ r` or `p ∣ s`) are a separate, secondary matter via `[p] = V∘π`.

**Shipped, axiom-clean, toward the signed identity:**

1. **Verschiebung `V`** with `V∘π = π∘V = [q]` and `π + V = [t]` (as endomorphisms). Consequently `V` is the dual of `π`: the predicate `IsDualOf V π` — *defined* as `V∘π = [deg π] ∧ π∘V = [deg π]` — holds, **because `deg π = q` is independently known** (Frobenius has degree `q`). Likewise `deg V = q` and the trace of `V` equals `t`.

2. **The point-map composition** `(rV − s)∘(rπ − s) = [N]`, and the reverse order `(rπ − s)∘(rV − s) = [N]`, by the Vieta computation
   `(rV − s)(rπ − s) = r²(V∘π) − rs(V + π) + s² = r²[q] − rs[t] + s² = [N]`,
   established at the level of the additive (point) maps `E(K̄) → E(K̄)`.

3. **Genuine-isogeny extensionality** (the round-10 "Wall B killer"): the comorphism `φ^*` of a *genuine* isogeny is determined by its geometric point map. This upgrades the point-map identity in (2) to a **comorphism-level** identity `(rV − s)^* ∘ (rπ − s)^* = [N]^*`, **provided both `rπ − s` and `rV − s` are genuine isogenies** (i.e. carry honest comorphisms, not just point maps). `rπ − s` is genuine (built from `π` and `[·]`); the genuineness of `rV − s` is the issue in §3.

4. **Degree extraction ("Wall C").** *Given* a genuine isogeny `β_dual` with **both**
   - `IsDualOf β_dual β` (i.e. `β_dual∘β = [deg β]`), **and**
   - `β_dual∘β = [N]` (a comorphism-level composition equality),
   *and* `0 < deg β`, one concludes the **signed** `deg β = N` (combine the two compositions: `[deg β] = β_dual∘β = [N]`, then `[·]` is injective on `ℤ`). Here `β = rπ − s`, `β_dual = rV − s`.

5. `0 < deg(rπ − s)` — now unconditional.

## 3. The finding we want checked

To run the degree extraction (4) we must supply **two** facts about the pair `(β_dual, β) = (rV − s, rπ − s)`:

- **(i)** the composition `β_dual∘β = [N]` — delivered by (2)+(3) **once `rV − s` is genuine**; and
- **(ii)** `IsDualOf β_dual β`, i.e. `β_dual∘β = [deg β]`.

**Here is the point.** *Given* (i), condition (ii) reads `[N] = [deg β]`, i.e. it is **logically equivalent to `deg β = N` — the very conclusion.** So (ii) cannot be extracted from (i) together with the Vieta/relation algebra of `{1, π, V}`; supplying (ii) means knowing, independently, that `rV − s` acts as the **genuine dual** of `rπ − s`, i.e. `(rV − s)∘(rπ − s) = [deg(rπ − s)]`.

- For `β = π` this is free, because `deg π = q` is known a priori — that is exactly why `IsDualOf V π` is already shipped.
- For `β = rπ − s` it is **not** free: `deg(rπ − s)` is unknown — it is `N`, the goal.

The only non-circular source of (ii) is the **dual-isogeny existence theorem** (Silverman III.6.1): every isogeny `α` has a dual `α̂` with `α̂∘α = [deg α]`, and the dual is **additive** (`(φ + ψ)^ = φ̂ + ψ̂`) with `(s·id)^ = s·id`, so that `(rπ − s)^ = r·π̂ − s = r·V − s`. This is precisely the content "`deg` is a positive-definite quadratic form on `End(E)`" (Silverman III.6.2). In our formalisation this is an explicit open theorem (`∃! β, IsDualOf β α`, currently a `sorry`).

**Two consequences we want to stress-test with you:**

- **(A) The formal-group "Wall A" route does not by itself close Leaf 1.** Our long-running plan (your round-10 "narrow Route A") builds `rV − s` as a genuine isogeny via the addition-formula pullback, whose well-definedness reduces to a **kernel-of-reduction pole bound at `O`** (Silverman VII.2.2 / the IV.1.4 formal-group-law identity — what we have called "BRIDGE-003"). That construction supplies **(i)** (it makes `rV − s` genuine, so the Vieta composition lifts to comorphisms). **It does not supply (ii).** After BRIDGE-003 we would still face the dual-existence content for `rπ − s`.

- **(B) Dual existence subsumes the formal-group route.** Conversely, if we prove dual existence (III.6.1/6.2), then `α̂ := (rπ − s)^` is genuine **by construction**, equals `rV − s` (additivity + `π̂ = V`), and `IsDualOf α̂ (rπ − s)` holds **by construction** — giving (ii) for free, and giving the genuine `rV − s` (so (i) too) **without any formal-group pole bound**. So committing to dual existence retires BRIDGE-003 entirely.

- **(C) The sign is essential.** We need the *signed* `deg(rπ − s) = N`, not `deg = |N|`. The composition equality (i) alone yields only `deg(rπ − s)·deg(rV − s) = N²` (degree multiplicativity), hence at best `deg(rπ − s) = |N|` if one also knew `deg(rV − s) = deg(rπ − s)`. The sign — which is what makes (★) a *positivity* statement — comes only from the dual relation (ii) with the **same** `deg β` on both sides.

## 4. Questions

**Q1 (the validation we most want).** Is the finding in §3 correct — namely that the "narrow Route A" (genuine `rV − s` via the formal-group pole bound, then extensionality, then degree extraction), *traced to the bottom*, **still requires the genuine dual-isogeny existence** for `rπ − s` (our (ii)), and that the pole bound BRIDGE-003 supplies only (i)? Or is there a way to obtain `IsDualOf (rV − s) (rπ − s)` — equivalently the *signed* `deg(rπ − s) = N` — from the **two-sided** comorphism composition `(rV − s)(rπ − s) = (rπ − s)(rV − s) = [N]` plus degree multiplicativity, that we are missing? (We do not see one: two-sided `[N]` gives only `deg(rπ − s)·deg(rV − s) = N²`, no sign, no individual value.)

**Q2 (route choice, if Q1 confirms).** Given that dual existence (III.6.1/6.2) is then the real target and it **subsumes** the formal-group route, which constructor is the lighter formalisation given what is already shipped — `V` with `V∘π = π∘V = [q]`, `IsDualOf V π`, `π + V = [t]`, degree multiplicativity `deg(φ∘ψ) = deg φ · deg ψ`, the separable/inseparable degree theory + the separability⟺differential criterion, genuine-isogeny extensionality, and the point-map endomorphism algebra `ℤ[π]`:
  - **(a)** the **Pic⁰ route** — `Pic⁰(E) ≅ E` together with pushforward/pullback functoriality of degree-0 divisor classes, from which `α̂` and `α̂∘α = [deg α]` fall out; or
  - **(b)** the **kernel/factorisation route** — factor `α` through its separable quotient and the relative Frobenius (Silverman III.4), build the quotient curve `E/ker`, and obtain `α̂` from the universal property?

  In particular: is additivity of the dual `(φ + ψ)^ = φ̂ + ψ̂` (which is what we actually need, to get `(rπ − s)^ = rV − s`) cleaner to obtain in (a) or (b)? And is there a way to get **just** what Leaf 1 needs — additivity of the dual on the subring `ℤ[π] ⊆ End(E)`, plus `α̂∘α = [deg α]` — without the full `∃!`-dual for *every* isogeny?

**Q3 (a cheaper substitute for the quadratic-form content?).** Is there a route to (★) that needs **less** than full dual existence?
  - A **direct parallelogram law** `deg(φ + ψ) + deg(φ − ψ) = 2 deg φ + 2 deg ψ` on `End(E)` would give "`deg` is a quadratic form" and hence the signed identity directly — but is there a proof of it that does *not* itself route through the dual?
  - A **Frobenius-twist symmetry** giving `deg(rV − s) = deg(rπ − s)` — would this be reachable independently? (By §3(C) it yields only `deg = |N|`, so it would still leave the sign; is there an independent argument for the sign, short of the dual?)
  - The **Tate-module/Weil-pairing determinant** route (`det(rπ − s | T_ℓ E) = deg`, char. poly `X² − tX + q`): you judged this "starts from too little" in round 10 (no Tate module / Weil pairing in mathlib). Does the §3 finding change that calculus — i.e., is building the `ℓ`-adic determinant theory now comparable to, or lighter than, dual existence?

**Q4 (meta).** Does §3 change your round-10 recommendation? Concretely: should we **abandon the formal-group BRIDGE-003 scaffolding** (it gives (i) but not (ii), and dual existence gives both) and commit the deep effort to dual existence via your preferred route in Q2? Or do you still see "narrow Route A" as the lighter path, with a step for (ii) we have mis-estimated?

## 5. Status / metadata

- **Leaf 2** (`deg(1 − π) = #E(𝔽_q)`): closed, axiom-clean.
- **Leaf 1** (★): open; reduces to the signed degree identity `deg(rπ − s) = N`. Shipped toward it: `V` with `V∘π = π∘V = [q]`, `π + V = [t]`, `IsDualOf V π`, the point-map composition `(rV − s)(rπ − s) = [N]`, genuine-isogeny extensionality, the degree-extraction lemma ("Wall C"), `0 < deg`, degree multiplicativity.
- **Open deep gaps** as we now see them: **(D2)** the genuine dual-isogeny existence / "deg is a quadratic form" (our `h_isDual`), and **(D1 = BRIDGE-003)** the formal-group kernel-of-reduction pole bound — which §3(B) suggests is **subsumed by D2**.
- Build green throughout; placeholder guard passing. Prepared 2026-05-29 (round 11).
