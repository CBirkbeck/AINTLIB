# Review brief (round 18) — does Route 2 (Weil pairing) actually bypass the σ-bridge? An adversarial decomposition says the *sign* (`deg = N`) for the inseparable sum `rπ − s` still needs the genuine adjoint

*Prepared 2026-05-31 for the same arithmetic-geometry reviewer as rounds 1–17. Self-contained; no repo
access required. A soundness check on the round-17 pivot: after pivoting to the finite-level Weil-pairing
route (your round-17 recommendation, Silverman V.2.3.1), we built the axiom-clean reduction and then ran
an adversarial decomposition of the remaining build (grounded in a full read of Silverman III.8). It
surfaced a gap in the pivot's premise that we want you to confirm or refute before committing the build.*

---

## 1. Where we are

Per round 17 we pivoted from the divisor / dual-additivity route (Route 1) to the **finite-level
Weil-pairing route** (Route 2): close Leaf 1 (`0 ≤ qr² − t·rs + s²`) via `det(ψ|E[ℓ]) ≡ deg ψ (mod ℓ)`
for all primes `ℓ ≠ p`, then lift the integer identity by infinitely many primes. We have shipped,
axiom-clean, the reduction: Leaf 1 follows from the per-`ℓ` residual "there is a `2×2` matrix `M` over
`𝔽_ℓ` with `det M = q`, `tr M = t`, `det(rM − sI) = deg(rπ − s)`", with `M` the matrix of Frobenius on
`E[ℓ] ≅ 𝔽_ℓ²`. The remaining build is the finite-level Weil pairing supplying that residual.

The round-17 premise (yours and ours) was: **`det(ψ_ℓ) = deg ψ` needs only the Weil-pairing adjoint
`e(φS,T) = e(S, φ̂T)` plus `φ̂φ = [deg φ]`, NOT dual additivity** — so Route 2 sidesteps the obstruction
that blocked Route 1.

## 2. The finding — the adjoint *is* the σ-bridge, and for the sum it is not free

We decomposed the residual adversarially. The clean, **σ-bridge-free** machinery gets us only part way:

- **Frobenius is clean.** `det(π|E[ℓ]) ≡ q = deg π` follows from **Galois-equivariance** of the pairing
  (`e_ℓ(πS, πT) = e_ℓ(S,T)^q`, since `π` is the `q`-power Frobenius acting as `ζ ↦ ζ^q` on `μ_ℓ`). No
  σ-bridge. Likewise the **adjoint for `π`**: `e_ℓ(πS,T) = e_ℓ(S, VT)` (with `V = [q]π^{-1}` on `E[ℓ]`).
- **The sum gets a *factor-by-factor* partner.** By bilinearity + the `π`-adjoint,
  `e_ℓ((rπ − s)S, T) = e_ℓ(S, (rV − s)T)`. So `rV − s` is *an* adjoint partner of `rπ − s` — provable
  with no σ-bridge. Hence `e_ℓ((rπ−s)v₁, (rπ−s)v₂) = e_ℓ(v₁, (rV−s)(rπ−s)v₂) = e_ℓ(v₁, [N]v₂)`, using
  the unconditional `(rV − s)(rπ − s) = [N]` (from `Vπ = [q]`, `V + π = [t]`). Therefore
  `det((rπ − s)|E[ℓ]) ≡ N (mod ℓ)`.

**But this is `det ≡ N`, not `deg = N`.** `det((rπ − s)|E[ℓ])` lives in `𝔽_ℓ`; `N mod ℓ` carries no
information about the **sign** of the integer `N = qr² − trs + s²`, and `N ≥ 0` is precisely the Hasse
content (`N ≥ 0 ⇔ t² ≤ 4q`). Degree-multiplicativity only yields `deg(rπ − s) = |N|` (the round-13 wall).

To obtain the **sign** we need **Prop 8.6 proper**, `det((rπ − s)|E[ℓ]) ≡ deg(rπ − s)`, whose proof
(`e((rπ−s)v₁,(rπ−s)v₂) = e(v₁, (rπ−s)̂(rπ−s)v₂) = e(v₁, [deg]v₂)`) uses the **genuine adjoint** with the
**genuine dual** `(rπ−s)̂`. The factor-by-factor partner is `rV − s`; by nondegeneracy the adjoint
partner is unique, so **`(rπ−s)̂ = rV − s` on `E[ℓ]` — which is exactly dual additivity.** Establishing
the genuine adjoint without it requires the **σ-bridge** `(rπ−s)̂ T = σ((rπ−s)^*((T) − (O)))` connecting
the genuine dual to the **divisor pullback** `(rπ−s)^*`. For **inseparable** `rπ − s` (the generic case
`p ∣ s`), `(rπ−s)^*` carries inseparable multiplicities — the **same content that blocked Route 1**.

The subtlety we missed: in Silverman this is free because the dual is *defined* as `φ̂ = σ ∘ φ^* ∘ κ`
(III.6.1), so the adjoint (Prop 8.2) is native. Our project's dual (`isogDual`) is characterised by
`φ̂φ = [deg φ]`, **not** by the Pic⁰ formula; `φ̂φ = [deg]` is *not* the adjoint. So we must *establish*
the σ-bridge to connect them, and for inseparable `rπ − s` that is exactly the inseparable-pullback
content Route 1 stalled on (`picDual = isogDual`, the comap-variance / inseparability wall).

## 3. The candidate rescue — separable factorisation

The one mitigation that looks like it genuinely localises the inseparability:

> **(A)** Factor `rπ − s = λ ∘ Frob^k` with `λ` **separable** and `Frob^k` the inseparable part
> (`deg Frob^k = p^k = deg_i(rπ−s)`, Silverman II.2.12). On `E[ℓ]` (`ℓ ≠ p`):
> `det((rπ−s)|E[ℓ]) = det(λ|E[ℓ]) · det(Frob^k|E[ℓ])`.
> - `det(Frob^k|E[ℓ]) ≡ q^k = deg_i` by **Galois** (clean, no σ-bridge).
> - `det(λ|E[ℓ]) ≡ deg λ = deg_s` by Prop 8.6 for the **separable** `λ`, where `λ^*` is
>   **multiplicity-free** — and the separable σ-bridge is the case where our existing Pic⁰/comap
>   machinery *does* work (separable degree = full degree, no inseparability gap).
> Then `det((rπ−s)|E[ℓ]) ≡ deg_s · deg_i = deg(rπ−s)`. The inseparability is confined to a pure
> Frobenius power that Galois handles.

## 4. Questions

- **Q1 (confirm/refute the finding).** Is our analysis correct — that the clean Galois +
  factor-by-factor route gives only `det((rπ−s)|E[ℓ]) ≡ N (mod ℓ)`, and that the **sign** `deg = N`
  genuinely requires Prop 8.6 (the genuine adjoint / σ-bridge for `rπ − s`), not obtainable from
  `isogDual`'s `φ̂φ = [deg]` + Galois alone? Or is there a way to pin the integer `det ≡ deg` (hence the
  sign) for the sum that we're missing?

- **Q2 (does (A) rescue it?).** Is the separable-factorisation refinement sound, and does it genuinely
  reduce the obstruction to the **separable** σ-bridge (where our Pic⁰/comap dual already computes the
  full = separable degree)? Two specific worries: (i) the factorisation `rπ−s = λ ∘ Frob^k` (II.2.12) —
  is `λ` separable with `deg λ = deg_s`, and is the supersingular `Frob_{deg_i}`-vs-`Frob_p` subtlety
  (which bit us before) an issue here? (ii) does Prop 8.6 for separable `λ` truly avoid the inseparable
  pullback, i.e. is the separable adjoint `e_ℓ(λS,T)=e_ℓ(S,λ̂T)` cheap given a separable Pic⁰ dual?

- **Q3 (route comparison, honestly).** Given the finding, is Route 2 genuinely *easier* than Route 1, or
  *comparable*? Both ultimately need the σ-bridge / inseparable-pullback content for `rπ − s` (Route 1
  as dual additivity, Route 2 as the genuine adjoint in Prop 8.6). Frobenius is clean in Route 2 (Galois)
  but the sum is not. If comparable, which do you now recommend — and does (A) tip it decisively to
  Route 2?

- **Q4 (a better route to `det ≡ deg` for the sum?).** Is there a cleaner path to Prop 8.6 for `rπ − s`
  that we're not seeing — e.g. adopting `picDual = σ ∘ classMap ∘ κ` as *the* dual throughout (making
  the adjoint native, Silverman-style) and only needing `picDual ∘ φ = [deg φ]`; or any standard
  finite-field argument for `det(ψ|E[ℓ]) ≡ deg ψ` that doesn't route through the genuine adjoint?

## 5. Status / metadata

- **Shipped (axiom-clean):** the Route-2 *reduction* (Leaf 1 ⇐ the per-`ℓ` Frobenius-matrix residual);
  `isogDual` (`φ̂φ = [deg]`); `Vπ = [q]`, `V + π = [t]`, `(rV−s)(rπ−s) = [N]`; `deg(1−π) = #E` (Leaf 2);
  the integer-separation endgame.
- **Finding:** the residual's third conjunct `det(rM−sI) = deg(rπ−s)` *is* Prop 8.6 for `rπ − s`, which
  needs the genuine adjoint / σ-bridge — the clean machinery only delivers `det ≡ N (mod ℓ)`, not the
  sign. Frobenius (`det(π|E[ℓ]) ≡ q`) is clean via Galois.
- **Candidate fix:** separable factorisation `rπ − s = λ ∘ Frob^k` (Galois kills `Frob^k`; separable
  `λ` uses the Pic⁰/comap dual where it works).
- All Silverman claims verified against the in-repo PDF this session (III.7–III.8 read in full, V.2.3.1,
  III.6.1–6.2). Build paused on this question. Round 18.
