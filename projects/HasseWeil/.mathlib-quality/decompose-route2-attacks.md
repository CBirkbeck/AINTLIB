# `/develop --decompose` adversarial pass — Route 2 (Weil pairing). 2026-05-31

Disposition: opposing the plan. Attacks grounded in the full read of Silverman III.8 (pp. 93–99).

## CRITICAL FINDING #1 — Route 2 does NOT cleanly bypass the σ-bridge; Prop 8.6 for the *sum* `rπ−s` needs the genuine adjoint (≈ Route-1 difficulty)

**Attack (composition of L4 = DET-DEG):** can the pieces hold and the residual still fail to give the
*sign* (`deg = N`, `N ≥ 0` — the Hasse content)?

**The attack succeeds.** Trace it carefully:

- The clean, σ-bridge-free machinery gives only `det((rπ−s)|E[ℓ]) ≡ N (mod ℓ)`:
  - Prop 8.2 (adjoint) for **Frobenius `π`** is free via **Galois-equivariance** (Prop 8.1d):
    `e_ℓ(πS,πT)=e_ℓ(S,T)^q` (π = q-power Frobenius acts as `ζ↦ζ^q` on `μ_ℓ`), hence
    `e_ℓ(πS,T)=e_ℓ(S,VT)` (using `V=[q]π⁻¹` on `E[ℓ]`). **No σ-bridge.** ✓
  - **Factor-by-factor**: `e_ℓ((rπ−s)S,T)=e_ℓ(πS,T)^r·e_ℓ(S,T)^{−s}=e_ℓ(S,(rV−s)T)` (bilinearity +
    the `π`-adjoint). So the adjoint *partner* of `rπ−s` is `rV−s` — **provable, no σ-bridge.**
  - Then `e_ℓ((rπ−s)v₁,(rπ−s)v₂)=e_ℓ(v₁,(rV−s)(rπ−s)v₂)=e_ℓ(v₁,[N]v₂)=e_ℓ(v₁,v₂)^N`
    (using the shipped `(rV−s)(rπ−s)=[N]`, from `Vπ=[q]`, `V+π=[t]`). So
    `det((rπ−s)|E[ℓ]) ≡ N (mod ℓ)`. **Clean, no σ-bridge, no dual additivity.**

- **But this is `det ≡ N`, not `deg = N`.** `det((rπ−s)|E[ℓ])` is an element of `ZMod ℓ`; `N` mod `ℓ`
  carries no information about the **sign** of `N` as an integer. And `N ≥ 0` *is* the Hasse content
  (`N ≥ 0 ⇔ t² ≤ 4q`). Multiplicativity only gives `deg(rπ−s) = |N|` (the round-13 wall, re-confirmed).

- To get `deg(rπ−s) = N` (with the sign), I need **Prop 8.6 proper**: `det((rπ−s)|E[ℓ]) ≡ deg(rπ−s)`,
  proved via `e_ℓ((rπ−s)v₁,(rπ−s)v₂)=e_ℓ(v₁,(rπ−s)̂(rπ−s)v₂)=e_ℓ(v₁,[deg(rπ−s)]v₂)`. This uses the
  **genuine adjoint** with the **genuine dual** `(rπ−s)̂` (`(rπ−s)̂(rπ−s)=[deg]`, `isogDual`).
  - The factor-by-factor partner is `rV−s`; the genuine partner is `(rπ−s)̂`. By nondegeneracy the
    adjoint partner is **unique**, so `(rπ−s)̂ = rV−s` on `E[ℓ]` — **but that is exactly dual
    additivity.** Establishing the genuine adjoint without it requires the **σ-bridge (III.6.1b):**
    `(rπ−s)̂T = σ((rπ−s)*((T)−(O)))`, connecting `isogDual` to the **divisor pullback** `(rπ−s)*`.
  - For **inseparable** `rπ−s` (the generic case `p ∣ s`), `(rπ−s)*` carries inseparable
    multiplicities — the **same content Route 1 needed** (`picDual = isogDual`, the comap-variance /
    inseparability wall).

**Verdict.** The round-17 premise "Route 2 bypasses the divisor-pullback bottleneck" is **qualified.**
Route 2 bypasses *dual additivity literally*, and handles **Frobenius** cleanly via Galois — but the
**sign** for the sum `rπ−s` needs **Prop 8.6 for `rπ−s`**, i.e. the **genuine adjoint / σ-bridge**, which
for inseparable `rπ−s` is the inseparable divisor-pullback content. This is **comparable to Route 1's
dual additivity**, not a clean escape. The plan's DET-DEG ticket (and the round-17 brief) understated
this: it cited "isogDual (`φ̂φ=[deg]`) shipped" as sufficient, but `φ̂φ=[deg]` is *not* the adjoint —
the adjoint (Prop 8.2) is the σ-bridge.

### Candidate resolutions (for the parent decision)
- **(A) Separable-factorisation refinement.** `rπ−s = λ ∘ Frob^k` (`λ` separable, `k=v_p` of the insep
  part). Handle `Frob^k` via Galois (`det ≡ q^k = deg_i`), and `λ` (separable!) via the **separable**
  adjoint — where `λ*` is **multiplicity-free**, avoiding the inseparable pullback. Then
  `det((rπ−s)|E[ℓ]) ≡ deg_s·deg_i = deg`. NEEDS the factorisation (Silverman II.2.12 — *caution:* the
  `mulByP_factors` B2 shows the supersingular subtlety, `Frob_{deg_i}` not `Frob_p`) + Prop 8.6 for the
  separable `λ`. **Most promising new idea; it genuinely localises the inseparability to a pure
  Frobenius power handled by Galois.**
- **(B) Adopt the Pic⁰ dual (`picDual = σ∘classMap∘κ`) as THE dual** (Silverman's way), making the
  adjoint native; reduces to `picDual∘φ = [deg φ]` (the project's existing comap-variance issue).
- **(C) Build the σ-bridge for `rπ−s` directly** (accept it as the hard core, comparable to Route 1).
- **(D) Re-consult the reviewer** with this specific finding before committing.

## FINDING #2 — TORSION (L0.1) depth understated
**Attack (discharge of `#E[ℓ]=ℓ²`):** is "separable ⇒ `#ker=deg`" actually shipped unconditionally for
`[ℓ]`? **No.** The project has `card_kernel_eq_degree_of_separable_witness` (witness-parametric: needs
finite kernel + finite-dim + a fibre witness `∃P₀, #(fibre over [ℓ]P₀)=sepDegree`). The unconditional
`[ℓ]` version needs the **fibre-size = sepDeg** content (III.4.10c) — nontrivial, the same kind of work
Leaf 2 needed for `1−π` (which used the special `ker(1−π)=⊤` route, *inapplicable* to `[ℓ]` since
`#ker[ℓ]=ℓ²<∞`). TORSION therefore has a real sub-dependency the ticket glossed. Plus **AG-SEP** (the
`[ℓ]`-separability entangled with the `OmegaPullbackCoeff` sorry) stacks under it.

## FINDING #3 — ASSEMBLE completeness (a STRENGTH, understated)
**Attack (does the residual close ALL `(r,s)`?):** `qf_nonneg` needs all `(r,s)`, including edges
`r≡0`/`s≡0` in `K` (the `degree_quadratic_exists_edge` sorry, `r≠0` in ℤ but `p∣r`). Route 2's
`det((rπ−s)|E[ℓ]) ≡ deg(rπ−s)` holds **uniformly in `r,s∈ℤ`** (the rep `ρ_ℓ` is a ring map; `rπ−s` is an
endomorphism for all `r,s`). So Route 2, IF it achieves Prop 8.6, **closes generic + edge cases in one
theorem** — potentially obsoleting both `genuineIsogSmulSub_degree_eq_signed` AND
`degree_quadratic_exists_edge`. **Strength**, but the ASSEMBLE wiring must realise `deg(rπ−s)` as a
genuine isogeny degree for all `(r,s)` (not only the `r,s≠0`-in-`K` `genuineIsogSmulSub`).

## Positive sub-findings (survived attack)
- Prop 8.6 for **Frobenius `π`** is clean via Galois-equivariance — `det(π|E[ℓ])≡q=deg π`, no σ-bridge.
- L1.3 (`[ℓ]*` pullback) is **multiplicity-free** since `[ℓ]` separable (`e=deg_i=1`) — the fibre is the
  explicit coset `T'+E[ℓ]`, no general/inseparable fibre theory. Survives.
- Pairing construction L1.1/L1.2 (`f`, `T'`), L2.2 (alternating telescope): grounded, survive.
- The shipped `Reduction` + `int_eq_of_congr_all_primes_ne` endgame: axiom-clean, survives.

## Overall
The decomposition is sound as a *proof*, but the adversarial pass shows the **hard core is NOT bypassed**:
Prop 8.6 for the inseparable sum `rπ−s` carries σ-bridge / inseparable-pullback content comparable to
Route 1. The most promising mitigation is **(A) the separable-factorisation refinement** (localising
inseparability to a Galois-handled Frobenius power). This is a parent-level decision — the plan should
not proceed to tickets until #1 is resolved.
