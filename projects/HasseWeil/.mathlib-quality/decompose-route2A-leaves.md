# `/develop --decompose` adversarial pass — Route 2A' LEAVES. 2026-05-31

Disposition: opposing. ≥3 attacks per leaf, grounded in III.8 + III.5.5 (read this session).

## Leaf 2 — `det(β|E[ℓ]) ≡ deg β` for SEPARABLE β  (THE HARD CORE)
**Attacks:**
- [1] *Is `isogDual`/Galois enough?* No — confirmed in the prior pass. Needs the genuine **adjoint**
  `e(βP,T)=e(P,β̂T)` (Prop 8.2), not just `β̂β=[deg]`.
- [2] *Does the project's picDual/comap actually deliver it?* Partially. picDual = `σ∘classMap∘κ`; the
  prior `degree-blind` issue was **inseparable-only** (`classNorm∘comap=(·)^inertia=sep degree`). For
  **separable** β, sep degree = full degree, so `picDual∘β=[deg β]` holds. BUT the adjoint is a
  *Weil-pairing* property: proving it (Prop 8.2) still needs the **σ-bridge construction** — the
  divisor pullback `β*((T))=Σ_{βP'=T}(P')` (mult-1, étale, since β separable) + the function `h` with
  `β*((T))−β*((O))=(β̂T)−(O)+div h` (exists by Abel). So Leaf 2 = **the separable adjoint Prop 8.2** =
  étale fibre pullback + Abel + function manipulation. **Real work, mult-free, bounded — the genuine
  core.** Survives, but is NOT "just use picDual."
- [3] *Edge instantiation:* used for β ∈ {`1−π`, `rπ−s` with p∤s} — both separable by III.5.5 (`m+nφ`
  sep ⟺ `p∤m`; here `m=1` and `m=−s`). NOT for `π` (`m=0`, inseparable) — see Leaf 3.
**Verdict:** survives as the hard core; the plan must state it is the separable adjoint (Prop 8.2),
mult-free, not a one-liner.

## Leaf 3 — `det(π|E[ℓ])≡q` and `tr(π|E[ℓ])≡t`  (REFINED — drop the factor-by-factor leaf)
**Attack [1] (does Leaf 2 give `det(π|E[ℓ])≡q`?):** **NO.** `π` is the Frobenius, `m+nφ` with `m=0` ⟹
**inseparable** (III.5.5). So Leaf 2 (separable) does **not** apply to `π`. `det(π|E[ℓ])≡q=deg π` must
come from **Galois-equivariance** `e(πv₁,πv₂)=e(v₁,v₂)^q` (π acts as `ζ↦ζ^q` on `μ_ℓ`).
⇒ **The pairing properties MUST include Galois-equivariance (Prop 8.1d)** — the prior plan omitted it
as "not needed"; it IS needed (for `det π`). Add it to Leaf 1.
**Attack [2] (char-poly shortcut for `det,tr`?):** `M²−tM+q=0` on `E[ℓ]` (from the shipped
`π²−[t]π+[q]=0`) gives `tr M=t, det M=q` ONLY if `M` is non-scalar. **The scalar case `M=λI` is a real
hole** (`det(rM−sI)=(rλ−s)²` need not equal `N`). So the char-poly route is NOT safe; use Galois +
Leaf 2 instead.
**Refined structure:** `det M≡q` via **Galois**; `tr M≡t` via **Leaf 2 applied to `1−π`** (separable!):
`det((1−π)|E[ℓ])≡deg(1−π)=#E`, then `tr M = 1+det M−det(1−M) = 1+q−#E = t`. Then
`det((rπ−s)|E[ℓ])=det(rM−sI)=qr²−trs+s²=N` via the **shipped `MatrixDet`** 2×2 identity.
⇒ **The factor-by-factor `det≡N` leaf is REDUNDANT and dropped.** (det π via Galois + tr via Leaf-2-on-(1−π)
+ MatrixDet is cleaner and avoids the scalar-case hole.)

## Leaf 4 — `deg(rπ−s)=N` for `p∤s`  (composition)
`det((rπ−s)|E[ℓ])≡N` (Leaf 3) AND `≡deg(rπ−s)` (Leaf 2, rπ−s separable) ⇒ `deg(rπ−s)≡N (mod ℓ)` ∀ℓ≠p ⇒
`=N` (shipped `int_eq_of_congr_all_primes_ne`). **Attack:** needs `rπ−s` a **genuine isogeny** with a
degree — `genuineIsogSmulSub` exists exactly when `p∤s` (its `s≠0`-in-K hypothesis), matching the
domain. ✓ Survives.

## Leaf 5 — discriminant lemma `Q≥0 on {p∤s} ⇒ t²≤4q ⇒ qf_nonneg ∀(r,s)`
**Attacks:**
- [1] *Witness explicit?* If `t²>4q`, the roots `x±=(t±√(t²−4q))/(2q)` of `Q(·,1)` are real distinct.
  Pick a prime `ℓ₀≠p`, `s=ℓ₀^k` (so `p∤s`), `k` large enough that `s·(x₊−x₋)>1`, `r=⌈x₋·s⌉`; then
  `x₋<r/s<x₊`, so `Q(r,s)=s²Q(r/s,1)<0` — contradiction. Elementary, formalisable. Survives.
- [2] *`t²≤4q ⇒ Q≥0`?* `Q=qr²−trs+s²`, `q=#K>0`, discriminant-in-`r` is `s²(t²−4q)≤0` ⇒ `Q≥0`. ✓
- [3] *Does this need "deg is a QF" (dual additivity)?* **No** — uses only the *explicit* value
  `deg(rπ−s)=N` (Leaf 4) and the *explicit* form `Q`. Avoids III.6.2c entirely. ✓
**Verdict:** survives; one elementary new lemma (p-coprime denominator witness).

## Leaf 1 — Weil pairing construction on `E[ℓ]`  (Prop 8.1, the bulk)
- **L1.3** `div g=[ℓ]*(T)−[ℓ]*(O)`: `[ℓ]*` mult-1 (separable `[ℓ]`), fibre `=T'+E[ℓ]` coset; sums to
  `O` (`ℓ²T'=O`). Needs the `[ℓ]`-divisor-pullback (étale). Survives.
- **L1.5** `e_ℓ(S,T)=g(X+S)/g(X)` constant: needs **function EVALUATION** + translate `g∘τ_S` +
  `g∘[ℓ]` + II.2.3 (non-surjective morphism to ℙ¹ is constant). **Genuinely new infrastructure**
  (project's function-field layer lacks pointwise evaluation). Medium risk; survives as a real ticket.
- **Galois-equivariance (Prop 8.1d)** now REQUIRED (Leaf 3 [1]).
- L1.1 (`div f=ℓ(T)−ℓ(O)`, Abel), L1.2 (`[ℓ]` surjective), L2.2 (alternating telescope): survive.

## Leaf 6/7 — `E[ℓ]≅𝔽_ℓ²` (TORSION) + AG-SEP (`[ℓ]` separable)
- **TORSION:** `#E[ℓ]=ℓ²` via the general "separable⇒#ker=deg" (witness-parametric; unconditional `[ℓ]`
  needs fibre-size=sepDeg, III.4.10c). Real depth. Survives with sub-dependency.
- **AG-SEP:** `[ℓ]` separable for `ℓ≠p`. **Attack:** the project closed Leaf 2 (`1−π` separable) — the
  SAME differential route (`[m]*ω=mω≠0` for `p∤m`) should give `[ℓ]` separable; check whether it is
  shipped unconditionally or inherits the `OmegaPullbackCoeff` T-IV-BRIDGE-001 sorry. Likely closable by
  the route already used for `1−π`. Flagged, lower risk than first thought.

## Net refinements from this pass
1. **DROP the factor-by-factor `det≡N` leaf.** Replace with: `det π≡q` (Galois) + `tr π≡t` (Leaf 2 on
   the separable `1−π`) + the shipped `MatrixDet`. Avoids the scalar-case hole.
2. **ADD Galois-equivariance (Prop 8.1d)** to the pairing properties — required for `det π≡q` (π is
   inseparable, so Leaf 2 can't supply it).
3. **The hard core is Leaf 2** (separable adjoint Prop 8.2, mult-free) used for `1−π` and `rπ−s`, **plus**
   the pairing construction Leaf 1 (esp. the EVAL infrastructure). Everything else is shipped, Galois,
   or elementary.
4. **AG-SEP** is likely closable via the `1−π`-separability route already in the project.
**Verdict:** Route 2A' survives the leaf-level attack with the above refinements. The build surface is
now sharp: pairing construction (incl. Galois-equivariance + evaluation) + the separable adjoint
(Prop 8.2, mult-free) — that is the whole remaining mathematical core.
