# Review brief (round 20) — Hasse bound via the finite-level Weil pairing (Route 2A)

*Prepared 2026-06-03 for the same senior arithmetic-geometry reviewer as rounds 1–19. Self-contained: no repository access required. This continues the numbered conversation; §2.2 restates the rounds 16–19 guidance. Following your round-17/18/19 endorsement of Route 2A (finite-level Weil pairing + separable factorisation + integer separation), we have built and machine-checked the pairing/adjoint/scaling/determinant scaffolding. The remainder has reduced to a small, precise set of per-isogeny geometric facts that are **elementary in Silverman** but blocked by a **representation/framework** issue. We ask where to spend the remaining effort.*

## 0. Orientation

Goal: formalise `|#E(𝔽_q) − q − 1| ≤ 2√q` for `E/𝔽_q`, `q = p^r`. Per your guidance we use **Route 2A**: prove `det(ψ | E[ℓ]) ≡ deg ψ (mod ℓ)` for the Frobenius pencil `ψ ∈ {π, 1−π, rπ−s}` at every auxiliary prime `ℓ ≠ p`, then recover the integer identity `deg(rπ−s) = q r² − t rs + s²` by varying `ℓ`, whence `Q(r,s) := q r² − t rs + s² ≥ 0` (a degree is `≥0`) and Cauchy–Schwarz gives Hasse. We abandoned Route 1 (degree-quadratic-form via dual additivity `(φ+ψ)^=φ̂+ψ̂` in char `p`) on your advice. The pairing scaffolding is now done and axiom-clean; the residue is described in §5–§6. We have twice misjudged elementary facts as deep, so we want your read before committing the next large effort.

## 1. Goal

Hasse's theorem for `E/𝔽_q`: `|#E(𝔽_q) − q − 1| ≤ 2√q`. Equivalently, with `t := q + 1 − #E(𝔽_q)`, the form `Q(r,s) = q r² − t rs + s²` is nonnegative for all integers `r,s`.

## 2. Background, conventions, references

### 2.1 Notation
- `π : E → E` the `q`-power Frobenius; `V` its dual (Verschiebung), `Vπ = πV = [q]`, and `π + V = [t]`.
- `E[ℓ] ≅ (ℤ/ℓ)²` for `ℓ ≠ p`. `e_ℓ : E[ℓ]×E[ℓ] → μ_ℓ` the Weil pairing.
- For an isogeny `ψ`: `deg ψ`, separable/inseparable parts `deg_s`/`deg_i`, dual `ψ̂` (`ψ̂ψ = [deg ψ]`).
- **"Isogeny" in our formalisation** = a pair `(ψ^* : K(E)→K(E)` a function-field embedding, `ψ_* : E(K̄)→E(K̄)` a group homomorphism`)`, carried as **two independent fields**. "Genuine" = these are the comorphism and point-map of one actual morphism. This independence is the crux of §6.

### 2.2 References
- [Silverman] *The Arithmetic of Elliptic Curves*, 2nd ed., GTM 106. Used: **II.2.6/2.7** (finite-morphism fibre counts), **II.2.12** (separable–inseparable factorisation `φ = λ∘Frob^e`), **III.4.10** ((a) `#φ⁻¹(Q)=deg_s φ` ⟹ surjectivity; (b) `ker φ ≅ Aut(K̄(E₁)/φ^*K̄(E₂))`; (c) separable ⟹ unramified, `#ker φ = deg φ`), **III.5.1** (`τ_Q^*ω=ω`), **III.5.2** (`(φ+ψ)^*ω=φ^*ω+ψ^*ω`), **III.6.1–6.2** (dual isogeny + additivity), **III.8.1–8.6** (Weil pairing: bilinear/alternating/nondegenerate/Galois-equivariant; adjoint `e(φS,T)=e(S,φ̂T)`; scaling `e(φS,φT)=e(S,T)^{deg φ}`), **V.1.1** (Hasse).
- Prior replies (this conversation): **round 16** — the theorem-of-square divisor proof of `(φ+ψ)^=φ̂+ψ̂` is char-`p`-broken as written (base field stays imperfect), and the trace-relation route to `deg(rπ−s)` is circular (identifying `rV−s` as the dual needs `deg(rπ−s)` first). **round 17** — pivot to finite-level Route 2: `det(ψ|E[ℓ])≡deg ψ mod ℓ` for all `ℓ≠p`, recovered by varying `ℓ`; the hard work is the pairing construction + the adjoint. **round 18** — the separable-factorisation rescue: `β = λ∘Frob^e` (Frobenius factor scaled by Galois `z↦z^{p^e}`, separable factor `λ` by the separable adjoint), localising inseparability to a Frobenius power and avoiding the inseparable σ-bridge. **round 19** — Route 2A is the path; build pairing as a constant-ratio function; the separable adjoint should use the **Picard/divisor dual** `picDual = σ∘φ^*` (multiplicity-free for separable `φ`, **no coordinate-ring comorphism needed**); inseparable `π` via Galois; do NOT return to Route 1.

### 2.3 State of the art
Classical (Hasse, 1930s); only the formalisation is at issue. The alternative Stepanov/Bombieri elementary route was previously judged a different proof not worth switching to.

## 3. The agreed strategy (Route 2A, rounds 17–19)

1. `E[ℓ] ≅ (ℤ/ℓ)²`; build `e_ℓ`, prove bilinear/alternating/nondegenerate.
2. **Separable scaling.** For separable `λ`: `e_ℓ(λS,λT)=e_ℓ(S,T)^{deg λ}`, via the adjoint `e_ℓ(λS,T)=e_ℓ(S,λ̂T)` with `λ̂` the Picard/divisor dual.
3. **Frobenius factor.** `e_ℓ(πS,πT)=e_ℓ(S,T)^q` (Galois: `π` is `q`-power on `μ_ℓ`).
4. **Determinant–degree.** With `M=(π|E[ℓ])`: `det M ≡ q`, `det(1−M) ≡ #E` (⟹ `tr M ≡ t`), `det(rM−sI) ≡ Q(r,s) (mod ℓ)`.
5. **Separable factorisation (round 18)** for any inseparable pencil member; for `1−π`, `rπ−s` with `p∤s` this is vacuous (already separable) so step 2 applies directly.
6. **Integer separation.** Congruence for all `ℓ≠p` ⟹ integer identity ⟹ `Q ≥ 0` ⟹ Hasse.

## 4. What is built and machine-checked (no `sorry`, standard axioms only)

- `E[ℓ] ≅ (ℤ/ℓ)²` for `ℓ≠p`.
- The Weil pairing as the constant ratio `e_ℓ(S,T) = τ_S^* g_T / g_T` (your round-19 suggestion), and its **bilinearity, alternating property, `μ_ℓ`-membership, and nondegeneracy**.
- The **separable adjoint and scaling, CoordHom-free** (your round-19 prescription): for a separable isogeny `φ` with a point-endomorphism `δ` satisfying `δ∘φ = [#ker φ]`, we prove `e_ℓ(φS,φT)=e_ℓ(S,T)^{deg φ}`. We realise `δ` as the divisor-pushforward dual `δ = κ∘φ^*∘κ⁻¹` (`κ : Pic⁰ ≅ E`), and the dual relation `δ∘φ=[#ker φ]` is **automatic via the σ-bridge** (`σ(φ^*((Q)−(O)))=δQ`), multiplicity-free, no comorphism — exactly as you indicated.
- The determinant reduction: the additive symplectic form (`log e_ℓ`), `det(ρ_ℓ ψ) = scaling exponent`, and the assembled `Hasse ⟸ {three per-ℓ scalings}` and `Hasse ⟸ {det M≡q, det(1−M)≡q+1−t, det(rM−sI)≡deg(r,s)}` with the integer-separation endgame.
- `deg(1−π) = #E(𝔽_q)` (closed).
- **Separability** of `1−π` and of `rπ−s` (`p∤s`), via III.5.2 — `(rπ−s)^*ω = −s·ω ≠ 0` — with the general differential additivity `a_{α+β}=a_α+a_β` now formalised.
- `#ker φ = deg φ` for separable `φ` (general).

So the "hard work" you located in rounds 17–18 — the pairing construction, nondegeneracy, and the (separable) adjoint/scaling — is essentially complete and axiom-clean.

## 5. The precise remaining gap

To instantiate the *abstract* separable scaling at the concrete pencil members `1−π`, `rπ−s` (over `K̄`), each needs three per-isogeny witnesses, and the Frobenius factor needs one:
1. **Surjectivity** of the point-map over `K̄` (Silverman III.4.10(b)).
2. **Translation covariance** `τ_S^*φ^* = φ^*τ_{φS}^*` at the generic point (III.8.2), feeding the constant-ratio adjoint.
3. **Divisor transport** `div(φ^*h) = φ^*(div h)` (so `φ^*` descends to `Pic⁰` and `δ` is well-defined).
4. (Frobenius factor) **Galois-equivariance** `e_ℓ(πS,πT)=e_ℓ(S,T)^q` — not yet formalised.

Mathematically 1–3 are elementary Silverman III.4.10/III.8.2 (e.g. III.4.10(b) surjectivity is `#φ⁻¹(Q)=deg_s φ` plus the homomorphism translation `φ⁻¹(Q)≅φ⁻¹(Q')` — **not** Lang's theorem, which we initially mislabelled).

## 6. Where we are stuck — a representation obstruction, not a mathematical one

In our formalisation an isogeny carries comorphism `φ^*` and point-map `φ_*` as **two independent fields** with no built-in link. Consequently:
- The repository's finite-morphism / fibre-count machinery (which proves III.4.10(a)/(b)/(c): surjectivity, unramifiedness, `#ker=deg`) is developed for a *different, fully-geometric* isogeny type whose point-map is derived from the morphism. The genuine pencil isogenies live in the *abstract* (two-field) type.
- Hence the elementary Silverman facts (surjectivity, transport, covariance) cannot be **applied** to the pencil's point-maps without a bridge: that the abstract point-map field equals the geometric point-map of its comorphism. We have this bridge only for special cases — `[n]` (explicit division-polynomial coordinate formula) and the geometric Frobenius (explicit `q`-power coordinate map) — and only at the *generic point* for `1−π`, `rπ−s` (the "genuineness" witness), not globally.

So the separable scaling is built; the witnesses 1–3 are elementary; but the abstract two-field representation prevents invoking the existing geometric machinery for them. Two candidate fixes:
- **(A) Bridge the decoupling once.** Equip each genuine pencil isogeny with the geometric point-map of its comorphism (a point-functor structure) and prove the abstract point-map field agrees with it; then III.4.10/III.8.2 apply and discharge 1–3 by Silverman's elementary arguments. One construction, reused across the pencil.
- **(B) Re-realise the pencil isogenies in the geometric type** from the start (point-map derived from the morphism), so the witnesses are free, then re-connect to the determinant reduction.

## 7. Questions

**Q1 (structural).** Is fix (A) — bridge the abstract point-map to the geometric point-map of the comorphism, once, then invoke Silverman III.4.10/III.8.2 — the right move? Or is decoupling comorphism and point-map a design mistake to retire in favour of (B), a single geometric isogeny type carrying the morphism with the point-map derived?

**Q2 (avoid the witnesses).** For the *separable* scaling specifically (its only use: `1−π`, `rπ−s`), is there a realisation of the adjoint/dual that needs **neither** point-map surjectivity (1) **nor** divisor transport (3) — working entirely with divisor classes on `Pic⁰` and Abel–Jacobi, never invoking the genuine point-map — leaving only covariance (2)? You said in round 19 the separable adjoint is "Picard-divisor in nature"; can it be made point-map-free?

**Q3 (degree multiplication).** Our divisor-pushforward dual currently *consumes* point-map surjectivity (to know `φ^*` multiplies divisor degrees by `#ker`). Can `deg(φ^*D) = (#ker φ)·deg D` for separable `φ` be obtained from the comorphism alone (function-field degree `= deg φ`), independent of the point-map?

**Q4 (Frobenius factor).** Cleanest formalisation of `e_ℓ(πS,πT)=e_ℓ(S,T)^q`: the Galois-equivariance `e_ℓ(S^σ,T^σ)=e_ℓ(S,T)^σ` (`σ` the `q`-power, `π=σ` on points), or the round-18 factorisation computation `e(Frob^e P,Frob^e Q)=e(P,Q)^{p^e}`? Which has fewer prerequisites in a constant-ratio formalisation?

**Q5 (strategy).** Given §4 is done and the residue is the §6 decoupling: is Route 2A still the right path, or has the abstract-isogeny representation turned the "bounded, local" remainder into something where re-architecting (B) is warranted? Would you spend the next effort on (A) the point-functor bridge or (B) re-building the pencil isogenies geometrically?

## 8. Metadata
- Build: full project compiles; the assembled bound is axiom-clean modulo exactly the §5 witnesses (three per-isogeny geometric facts + Frobenius Galois-equivariance). Pairing, nondegeneracy, separable scaling, determinant reduction, separability, `#ker=deg`, `deg(1−π)=#E` are all `sorry`-free on standard axioms.
- Round 20; rounds 16–19 summarised in §2.2.
