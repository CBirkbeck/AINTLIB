# Review brief (round 16) — is the theorem-of-square proof of dual additivity actually characteristic-free over F̄, or is the char-p case genuinely Weil-pairing-only? (the K(E₁)-imperfectness obstruction)

*Prepared 2026-05-31 for the same arithmetic-geometry reviewer as rounds 1–15. Self-contained; no repository access required. A focused soundness follow-up: we started building the round-15 divisor route, and scoping it surfaced a precise mathematical question about whether the bivariate theorem-of-the-square proof of dual additivity is really characteristic-free over F̄ — together with two infrastructure realities that change the effort comparison with the Weil-pairing route.*

---

## 1. Where we are

Following your round-15 verdict we committed to the **narrow divisor route** for the one remaining residual, the **dual additivity** (Silverman III.6.2(c)) specialised to the Frobenius plane:

> **DualAdd.** `ŵ(rπ − s) = rV − s`, equivalently `∀Q, (rπ − s)^(Q) = (rπ)^(Q) + (−s)(Q)`.

We recorded your **Q3** verdict as settled: the ℤ[π]-conjugation shortcut is **circular** — we verified directly against Silverman that Corollary 6.3 (deg is a positive-definite quadratic form) is *proved using* III.6.2(c) twice, so additivity-of-dual is strictly upstream of the quadratic form and cannot be extracted from Cayley–Hamilton + the norm.

Everything above DualAdd is machine-checked, axiom-clean, non-circular: `E ≅ Pic⁰`, the dual `α̂ = κ⁻¹∘α*∘κ` with `α̂α = [deg α]`, the seeds `π̂ = V`, `(rπ)^ = rV`, `[n]^ = [n]`, the Abel/Miller divisor group law (characteristic-free), Cayley–Hamilton for `rπ − s`, and the full chain `DualAdd ⟹ htrace_dual ⟹ deg(rπ − s) = N`. The lone input is DualAdd.

## 2. The sharp question — does III.6.2(c)'s proof actually work over F̄ in char p?

Your round-14/15 steer was: prove the theorem of the square **over F̄ (perfect)**, where "the footnote's perfectness need is met, so the argument is characteristic-free." On re-reading Silverman's proof we think this **conflates two different fields**, and want your adjudication before we commit the build.

Silverman's III.6.2(c) proof (book p.83–84) is the bivariate "perspective switch":

1. Take Weierstrass coordinates `x₁,y₁ ∈ K(E₁)` and `x₂,y₂ ∈ K(E₂)`. **View E₂ as an elliptic curve over the field `K(E₁) = K(x₁,y₁)`.**¹
2. The points `φ(x₁,y₁), ψ(x₁,y₁), (φ+ψ)(x₁,y₁) ∈ E₂(K(E₁))` give a degree-0 divisor `D` on E₂ that sums to `O` (since `φ+ψ` is the sum), so by Abel (III.3.5) there is `f ∈ K(E₁)(E₂)` with `div f = D` **in the (x₂,y₂) variable**.
3. **Switch perspective:** view `f` as a function of `(x₁,y₁)` over `K(E₂)`. Then `ord_{P₁}(f) = e_φ(P₁)` for `P₁` in the fibre `φ⁻¹(x₂,y₂)`, and the divisor of `f` in the `(x₁,y₁)` variable is `(φ+ψ)*((Q)) − φ*((Q)) − ψ*((Q)) + Σnᵢ(Pᵢ)`; being `div f` it sums to `O`, giving III.6.2(c).

The footnote **¹** is attached **exactly to step 1** ("E₂ over `K(E₁) = K(x₁,y₁)`"): *"this is where we use the characteristic 0 assumption, since all of our results on elliptic curves have assumed that the base field is perfect."*

The base field in question is the **function field `K(E₁) = K(x₁,y₁)`**, not the constant field `K`. And `K(x₁,y₁)` is a transcendental extension of `K`, hence **imperfect in characteristic p even when `K = F̄` is algebraically closed** (`x₁^{1/p} ∉ F̄(x₁,y₁)`). So taking the constant field to be `F̄` does **not** discharge the footnote — the perfectness Silverman needs is of `K(E₁)`, which remains imperfect.

This is the same caution you gave in **round 13** ("don't rely on 'perfect closure fixes everything' — function fields stay transcendental/imperfect in char p"), which seems to sit in tension with the round-14/15 "char-free over F̄" framing. We want to know which is right, because it decides the whole route.

## 3. Two infrastructure realities (for the effort comparison)

Independent of §2, scoping the codebase shows the round-15 estimate (600–1300 LOC) assumed machinery we do not have:

- **(i) Two isogeny notions, unbridged.** The geometric divisor machinery (pushforward `φ_*`, the κ-divisor `(P)−(O)`, the section σ, Miller/Abel) is built on one isogeny datum; the live dual `α̂` (= `κ⁻¹∘α*∘κ`, ideal-extension form) is built on another. The residual chain never connects them, so the geometric pullback `α*` needs a bridge to the dual before it can speak about DualAdd.
- **(ii) No fibre theory.** There is no finite-fibre/`Σ_{αP=Q}` apparatus to even write `α*((Q)) = Σ_{αP=Q} e_α(P)(P)`, and the multiplicity identity `e_α(P) = deg_i α` is only available in a witness-parametric form, not as a usable lemma. Building char-free fibre-ramification theory over F̄ is itself a development.

Combined with §2, the divisor route looks materially heavier than 600–1300 LOC, and its viability in char p is in question.

## 4. Questions

- **Q1 (the soundness crux).** Does Silverman III.6.2(c)'s bivariate proof go through **characteristic-free over F̄**, given that its base field `K(E₁) = F̄(x₁,y₁)` is **imperfect** in char p? If yes: what replaces the perfectness of `K(E₁)` in the `ord_{P₁}(f) = e_φ(P₁)` step (does inseparability of `φ` break the ord computation, or is it absorbed into `e_φ`)? If no: is this exactly why Silverman restricts III.6.2(c) to char 0 and routes char p through **Exercise 3.31 (the Weil pairing)** — i.e., is the theorem-of-square/divisor proof of DualAdd **genuinely char-0-only**, so the char-p case (ours: `p ∣ s` is generic) cannot avoid the Weil pairing?

- **Q2 (route comparison, if Q1 = "char-0-only").** Given (i)+(ii), is the **Weil-pairing / Tate-module** route now the *more mechanical* formalization for char p? Your round-13 estimate was 500–1500 LOC for one auxiliary ℓ ≠ p with the full ℓⁿ tower + nondegeneracy + dual-compatibility `e(φP,Q)=e(P,φ̂Q)`. We have division-polynomial torsion cardinalities and `E[ℓⁿ]` structure available. Would you now recommend switching the char-p case to Weil/Tate?

- **Q3 (a Frobenius-specific shortcut).** Our `α₁ = rπ`, `α₂ = [−s]` are highly structured: `π` is the **purely inseparable q-power Frobenius** (so `π*` is the q-power map on functions, `V = π̂` explicit, `Vπ = πV = [q]`, `π + V = [t]`). Is there an explicit/computational proof of `ŵ(rπ − s) = rV − s` that exploits the **Frobenius structure** (e.g. computing the dual on `ℤ[π]` via `π*` = Frobenius directly, or via the action on `T_ℓ` / the formal group) and **avoids the general theorem of the square** entirely? Anything that turns "additivity at a structured pair" into a finite computation would dodge both §2 and §3.

- **Q4 (if we stay with the divisor route).** Assuming Q1 = "yes, char-free over F̄": what is the leanest way to handle the fibre/multiplicity infrastructure of §3(ii) — a genuine `Σ_{αP=Q} e_α(P)(P)` fibre sum (needing finite fibres + `e_α = deg_i`), or a formulation of the pulled-back theorem of the square that **avoids the explicit fibre sum** (working only with `div f` of the Miller/chord-tangent function and Abel)? And what is the minimal bridge between the two isogeny notions of §3(i)?

## 5. Status / metadata

- **Leaf 2** (`deg(1−π) = #E(F_q)`): closed, axiom-clean. **Leaf 1 generic**: reduced — axiom-clean, non-circular, wiring-verified — to **DualAdd** (III.6.2(c)).
- **Q3 of round 15 (ℤ[π]-conjugation) = circular**: settled, verified vs Cor 6.3.
- **Open soundness question**: whether the divisor/theorem-of-square proof of DualAdd is char-free over F̄ (the `K(E₁)`-imperfectness of §2) or genuinely char-0-only (⟹ Weil pairing for char p).
- Build paused on this question (we did not want to commit the fibre/bridge infrastructure of §3 before resolving §2). Prepared 2026-05-31 (round 16).

¹ Silverman, *The Arithmetic of Elliptic Curves*, III.6.2(c), book p.83, footnote 1.
