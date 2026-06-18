# Review brief (round 13) — Route C is built; the last residual is the dual additivity (III.6.2(c)). What is the lightest char-p route?

*Prepared 2026-05-31 for the same arithmetic-geometry reviewer as rounds 1–12. Self-contained; no repository access required. A focused follow-up: the corrected Pic⁰ route ("Route C") is now formally assembled and the genuineness/inseparability obstacles are resolved; we are down to one classical residual and want your steer on the lightest way to discharge it.*

---

## 1. Recap and the state of Route C

We are formalising the Hasse bound for `E/𝔽_q` (`q` a power of `p`). **Leaf 2** (`deg(1−π)=#E(𝔽_q)`) is closed. **Leaf 1** is `0 ≤ q r² − t r s + s²` for all `r,s`, which reduces to the **signed degree identity** `deg(rπ − s) = N`, `N := q r² − t r s + s²`.

Following your round-11/12 guidance (corrected Pic⁰: divisor pullback / ideal **extension**, not comap), we have now **formally built and machine-verified** (axiom-clean, no `sorry` in the chain):

- **`E ≅ Pic⁰(E)`** (genus-1 Riemann–Roch), the class-group norm/extension functoriality, and the Pic⁰ dual `α̂ := κ⁻¹ ∘ (\text{extension}) ∘ κ` with `α̂ ∘ α = [\deg α]` and `α ∘ α̂ = [\deg α]`.
- **The degree-blindness is gone**: the extension map carries the inseparable degree via the ramification `e_φ = \deg_i φ` (III.4.10), exactly as you said.
- **The genuine comorphism is avoided**: we pin `[\deg(rπ−s)] = [N]` at the **point** level over the geometric points `E(\bar{𝔽}_q)` — which are infinite while `E[k]` is finite, so `[m]=[n] ⟹ m=n`. No genuine isogeny structure for `α̂`, no Wall C, no formal-group "BRIDGE-003".
- **The `\mathrm{relNorm}=\mathrm{comap}` ("`hnat`") obstruction is unconditional**: we proved the `[\text{PerfectField}]`-free per-prime relative norm over the imperfect function field that the library lacked.
- **Non-circular partial duals shipped**: `\hat{π}=V` (Verschiebung), `\widehat{[n]}=[n]`, and crucially `\widehat{rπ}=rV` — the last via your III.6.1(a) uniqueness with the **independently known** degree `\deg(rπ)=r²q` (so it is *not* circular).

So `deg(rπ−s) = N` is assembled modulo exactly one substantive residual.

## 2. The one residual, and why the easy routes are dead

The residual is the **dual additivity for the Frobenius plane**:

> `\widehat{rπ − s} = rV − s`,  equivalently  `(rπ − s) + \widehat{rπ − s} = [r t − 2s]`  (the III.8 trace relation),  equivalently  `(φ+ψ)^ = φ̂ + ψ̂` (III.6.2(c)) applied to `φ=rπ, ψ=−s`.

We have verified that the algebraic shortcuts are genuinely **circular**: deducing `\widehat{rπ−s}=rV−s` from the dual relation `\widehat{rπ−s}∘(rπ−s)=[\deg]` together with the Vieta identity `(rV−s)(rπ−s)=[N]` requires `N=\deg(rπ−s)` — which is the conclusion. (`[3]∘[2]=[6]` but `\deg[2]=4≠6`: a scalar-composition does not pin the degree.)

We then read your two proofs of III.6.2(c) directly:
- The **§III.6 (p. 84) proof is characteristic 0 only** — it works over `K(E_1)=K(x_1,y_1)` and the footnote flags that it uses perfectness of that field. For us `K(E_1)` is an **imperfect** function field over `𝔽_q`, so this proof does not apply.
- **Exercise 3.31** gives the char-p proof, and it routes through the **Weil pairing**: `\deg[2]=4` (division polynomials) ⟹ `#E[2^n]=4^n` ⟹ `E[2^n]≅(ℤ/2^n)²` ⟹ the pairing `e_{2^n}` (bilinear, nondegenerate) ⟹ `e_m(T_1,(φ+ψ)^T_2)=e_m(T_1,φ̂T_2+ψ̂T_2)` ⟹ nondegeneracy ⟹ `(φ+ψ)^=φ̂+ψ̂`.

The library has **division polynomials** but **no `E[m]≅(ℤ/m)²` structure and no Weil pairing**. So, on the face of it, our last residual reconnects to a *second* deep theory (the Weil-pairing/`E[m]` content — your "Route B"), having just escaped the formal-group one.

## 3. The questions

**Q1 (the main one).** Is the **Weil pairing (Exercise 3.31)** genuinely the lightest route to `\widehat{rπ−s}=rV−s` in characteristic `p`, or is there a lighter one given what we already have? Specifically, can the **§III.6.2(c) `Div⁰`/Abel argument be run geometrically** — over the *perfect closure* (or the algebraic closure) of `K(E_1)` — so that the function `f` with the prescribed degree-0 divisor exists, the additivity is proved over `\overline{K(E_1)}`, and then **descended** to `K`? Is the only real obstruction the existence of `f` over an imperfect field (curable by base-change to a perfect field), or is there a deeper char-p failure?

**Q2 (exploit the partial duals).** We have, non-circularly, `\widehat{[n]}=[n]`, `\hat{π}=V`, and `\widehat{rπ}=rV` (independently known degrees). We want only the **single** additivity instance `\widehat{(rπ)+(−s)} = \widehat{rπ}+\widehat{−s}`. Is there a route to this *one* instance (perhaps via the **linearity of the Pic⁰ pullback action**, `(α+β)^*|_{Pic⁰}=α^*|_{Pic⁰}+β^*|_{Pic⁰}`, the elliptic theorem-of-the-cube) that is lighter than building the Weil pairing? Does the theorem of the cube hold/transfer in our class-group (`κ: E ≅ \mathrm{Cl}(F[E])`, extension-of-ideals) formulation without the full Weil-pairing development?

**Q3 (how much Weil pairing is actually needed).** If Q1/Q2 fail, how much of Exercise 3.31 is truly required for *just* the additivity (not a general pairing theory)? Is the chain `\deg[2]=4 → #E[2^n]=4^n → E[2^n]≅(ℤ/2^n)² → e_{2^n}`-bilinearity tractable as a bounded development on top of mathlib's division polynomials, or does the Weil pairing's nondegeneracy/Galois-invariance drag in substantially more? Is there a smaller `m` (e.g. a single auxiliary `ℓ ≠ p`) that suffices, rather than the full `2^n`-tower?

**Q4 (a different endgame).** Exercise 3.32 derives the bound from `φ²−[a]φ+[d]=[0]` (Cayley–Hamilton, which we have for `π` from `π+V=[t]`, `Vπ=[q]`) plus `\deg([m]+[n]φ)≥0`. But computing `\deg([m]+[n]π)=m²+amn+qn²` still needs `\deg=` the norm form (i.e. the dual/additivity). Is there *any* route to `\deg(rπ−s)=N` (or directly to `|t|≤2√q`) that uses our **point-level** infrastructure (`π+V=[t]`, `Vπ=[q]`, Cayley–Hamilton, `κ: E≅Pic⁰`, `α̂α=[\deg]`, the geometric injectivity `E(\bar{𝔽}_q)` infinite) and avoids the dual additivity entirely?

## 4. Status / metadata

- **Leaf 2**: closed. **Leaf 1 generic case**: assembled, axiom-clean, modulo the single residual `\widehat{rπ−s}=rV−s` (III.6.2(c) dual additivity).
- **Resolved this round**: degree-blindness (Pic⁰ extension sees `\deg_i`), the genuine comorphism (point-level over `E(\bar{𝔽}_q)`), `hnat`/`relNorm=comap` (imperfect-field per-prime norm, unconditional), `\hat π=V`, `\widehat{rπ}=rV`, `\widehat{[n]}=[n]` (all non-circular).
- **The residual** `\widehat{rπ−s}=rV−s` = III.6.2(c); char-0 `Div⁰` proof inapplicable (imperfect `K(E_1)`); char-p = Exercise 3.31 = Weil pairing. Algebraic/uniqueness routes circular (verified).
- **Library**: division polynomials present; `E[m]≅(ℤ/m)²` and Weil pairing absent.
- Build green; placeholder guard passing. Prepared 2026-05-31 (round 13).
