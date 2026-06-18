# Decomposition — Route 2 (Weil pairing) for Leaf 1 of the Hasse bound

*Phase 1e methodical decomposition. Grounded in a direct reading of Silverman, *The Arithmetic of
Elliptic Curves* (2nd ed.), III.7–III.8 and V.2.3.1 (in-repo PDF, offset +18: book p. N = PDF p. N+18).
Read this session: III.7 (Tate module, pp. 87–92), III.8 (Weil pairing, pp. 92–99), V.1.1 (p. 138),
V.2.3.1 (pp. 141–142).*

## Goal (the residual the project already isolated)

`HasseWeil/WeilPairing/Reduction.lean` ships, axiom-clean, `deg_eq_of_frobMatrix_data`: Leaf 1
(`deg(rπ − s) = qr² − t·rs + s²`, hence `qf_nonneg`) follows from the **residual**

> **R.** For every prime `ℓ ≠ p`, there is a `2×2` matrix `M` over `ZMod ℓ` with
> `det M = q`, `tr M = t`, and `det(r•M − s•1) = deg(rπ − s)` (all in `ZMod ℓ`).

This decomposition plans the build of `R`. `M` will be the matrix of Frobenius `π` acting on
`E[ℓ] ≅ (ZMod ℓ)²`; the three conjuncts come from `det(ψ|E[ℓ]) ≡ deg ψ (mod ℓ)` (Silverman III.8.6 at
finite level) applied to `ψ ∈ {π, 1−π, rπ−s}`.

## Source proof structure (Silverman III.8, read in full)

Silverman fixes `m ≥ 2` prime to `p`. We instantiate `m = ℓ` (prime, `≠ p`). The proof of III.8.6 has
this shape; our decomposition mirrors it exactly:

1. **E[ℓ] ≅ (ℤ/ℓ)²** (III.6.4b), so `det : E[ℓ]×E[ℓ] → ℤ/ℓ` exists (free rank-2 module).
2. **Construction of the Weil pairing** `e_ℓ : E[ℓ]×E[ℓ] → μ_ℓ` (p. 93–94).
3. **Prop 8.1**: `e_ℓ` is bilinear, alternating, nondegenerate (Galois-invariant, compatible — not
   needed at finite level for our purpose).
4. **Cor 8.1.1**: surjectivity — a basis `{v₁,v₂}` has `e_ℓ(v₁,v₂)` a *primitive* ℓ-th root of unity.
5. **Prop 8.2**: the adjoint `e_ℓ(φS, T) = e_ℓ(S, φ̂T)`.
6. **Prop 8.6 (finite level)**: `det(φ|E[ℓ]) ≡ deg φ (mod ℓ)` via the Weil-pairing computation
   `e(v₁,v₂)^{deg φ} = e([deg φ]v₁,v₂) = e(φ̂φv₁,v₂) = e(φv₁,φv₂) = e(v₁,v₂)^{det}`.

## Decomposition tree

### R — `frobMatrix_data` (top, internal)
Per prime `ℓ ≠ p`: the matrix `M = ρ_ℓ(π)` (Frobenius on `E[ℓ]≅(ZMod ℓ)²`) satisfies `det M = q`,
`tr M = t`, `det(r•M − s•1) = deg(rπ−s)` in `ZMod ℓ`. Composition of L4 (det≡deg) applied to
`ψ ∈ {π, 1−π, rπ−s}` + L5 (the ring-hom rep, so `ρ_ℓ(rπ−s)=r•ρ_ℓ(π)−s•1`) + `det(1−M)=1−tr M+det M`.
Source: V.2.3.1 (the 2×2 reduction), III.8.6.

---

### L0 — `torsion_ell_equiv` : `E[ℓ] ≃+ (ZMod ℓ × ZMod ℓ)` for `ℓ ≠ p` (internal)
**Source: III.6.4(b), restated III.8 p. 92.**
> Verbatim (p. 92): *"As an abstract group, the group of m-torsion points E[m] has the form (III.6.4b)
> E[m] ≅ ℤ/mℤ × ℤ/mℤ. Thus E[m] is a free ℤ/mℤ-module of rank two."*

Sub-leaves:
- **L0.1** `card_torsion_ell` : `Nat.card E[ℓ] = ℓ²` for `ℓ ≠ p`.
  - Discharged from project: `HasseWeil.torsionSubgroup_card_of_witness` (`Hasse/TorsionCard.lean`)
    + `mulByInt_degree` (`deg[ℓ]=ℓ²`) + the witness `#ker[ℓ]=deg[ℓ]`.
  - **PREREQUISITE / RISK (flagged):** the witness `#ker[ℓ]=deg[ℓ]` needs `[ℓ]` **separable** for
    `ℓ ≠ p` (Silverman III.5.4 / Cor 5.4: `[m]` separable ⇔ `p ∤ m`, via `[m]*ω = mω ≠ 0`). The
    project's `mulByInt_isSeparable_of_witness` is witness-parametric and the witness
    `omegaPullbackCoeff[m]=m` is entangled with the **open sorry** `OmegaPullbackCoeff` T-IV-BRIDGE-001
    (`HasseWeil/OmegaPullbackCoeff.lean:477`). → **sub-development AG-SEP** (below).
- **L0.2** `torsion_ell_isModule` : `E[ℓ]` is a `ZMod ℓ`-module (every `P∈E[ℓ]` has `ℓ•P = 0` by def).
  - Leaf, project/mathlib: `AddSubgroup` of `ker[ℓ]` is `ℓ`-torsion; `ZMod ℓ`-module from
    `AddCommGroup.zmodModule`-style (mathlib `AddCommGroup` of exponent `ℓ`).
- **L0.3** `torsion_ell_finrank_two` : a finite `ZMod ℓ`-vector space of card `ℓ²` has dimension 2,
  hence `≃ (ZMod ℓ)²`. Leaf, mathlib (`Module.finrank` from cardinality;
  `Module.finBasisOfFinrankEq` / `LinearEquiv` to `Fin 2 → ZMod ℓ`).

### L1 — `weilPairing_ell` : the Weil pairing `e_ℓ : E[ℓ] → E[ℓ] → μ_ℓ` (internal, **HARD CORE**)
**Source: III.8 construction, pp. 93–94.** This is the irreducible new content — absent from the
project and mathlib.
> Verbatim (p. 93): *"Let T ∈ E[m]. Then there is a function f ∈ K̄(E) satisfying div(f) = m(T) − m(O).
> Next take T′ ∈ E to be a point with [m]T′ = T. Then there is similarly a function g ∈ K̄(E) satisfying
> div(g) = [m]*(T) − [m]*(O) = Σ_{R∈E[m]} (T′ + R) − (R)."*
> *"It is easy to verify that the functions f∘[m] and g^m have the same divisor, so multiplying f by an
> appropriate constant from K̄*, we may assume that f∘[m] = g^m."*
> *"g(X+S)^m = f([m]X+[m]S) = f([m]X) = g(X)^m. … the morphism E → ℙ¹, S ↦ g(X+S)/g(X) is not surjective,
> so (II.2.3) says that it is constant. This allows us to define a pairing e_m : E[m]×E[m] → μ_m by
> setting e_m(S,T) = g(X+S)/g(X)."*

Sub-leaves:
- **L1.1** `exists_f_div` : `∀ T∈E[ℓ], ∃ f, div f = ℓ•(T) − ℓ•(O)`.
  - Discharged from project (Abel III.3.5 / Miller): the divisor `ℓ(T)−ℓ(O)` has degree 0 and sums to
    `[ℓ]T − [ℓ]O = O` (since `T∈E[ℓ]`), hence principal. Project: `EffectiveSumReduce` /
    `kappaDivisor`/`sub_principal_of_miller` machinery + `miller_hypothesis_holds_allChar`.
- **L1.2** `exists_preimage_mul` : `∀ T, ∃ T', [ℓ]•T' = T`. Leaf: `[ℓ]` surjective on `E(F̄)` (nonzero
  isogeny over algebraically closed field is surjective; project kernel/fiber API in
  `EC/IsogenyKernel.lean`, or `Isogeny` surjectivity).
- **L1.3** `exists_g_div` : `∃ g, div g = [ℓ]*(T) − [ℓ]*(O)`. Abel + the **divisor pullback `[ℓ]*`**.
  NOTE: `[ℓ]*(T) = Σ_{R∈E[ℓ]}(T'+R)`, a *concrete fibre sum over E[ℓ]* (the fibre is `T'+E[ℓ]`), NOT a
  general fibre-pullback API — this is the finite explicit form, dischargeable from the kernel coset
  structure (`fiberEquivKernel`) without the general fibre theory Route 1 needed. Sums to `O`
  (`#E[ℓ]=ℓ²`, `[ℓ²]T'=O`).
- **L1.4** `f_comp_mul_eq_g_pow` : after rescaling, `f∘[ℓ] = g^ℓ`. Divisor computation:
  `div(f∘[ℓ]) = [ℓ]*(div f) = ℓ([ℓ]*(T)−[ℓ]*(O)) = ℓ·div g = div(g^ℓ)`; equal divisors ⇒ scalar
  multiple ⇒ rescale. Project: `[ℓ]`-pullback of divisors commutes with `div`, function divisor theory.
- **L1.5** `weilPairing_ell` def + `pairing_is_root_of_unity` : `e_ℓ(S,T) := g(X+S)/g(X)` is a constant
  ℓ-th root of unity (independent of `X`). The constancy is `g(X+S)^ℓ = f([ℓ]X+[ℓ]S) = f([ℓ]X) =
  g(X)^ℓ` (since `[ℓ]S=O`) + nonconstant-image ⇒ constant (II.2.3). Needs **evaluation** `g(X+S)/g(X)`
  of a rational function at points — function-field evaluation API.

### L2 — `weilPairing` properties (Prop 8.1) (internal)
**Source: III.8 Prop 8.1, pp. 94–96.**
- **L2.1** `weilPairing_bilinear` (a). Verbatim (p. 94): *"It is bilinear: e_m(S₁+S₂,T)=e_m(S₁,T)e_m(S₂,T),
  e_m(S,T₁+T₂)=e_m(S,T₁)e_m(S,T₂)."* 1st factor: `g(X+S₁+S₂)/g(X)` telescopes. 2nd factor: uses
  `f₃ = c f₁ f₂ h^m` with `div h = (T₁+T₂)−(T₁)−(T₂)+(O)` (Abel/Miller).
- **L2.2** `weilPairing_alternating` (b): `e_ℓ(T,T)=1`. Verbatim (p. 95): the product
  `∏_{i=0}^{ℓ-1} f∘τ_{[i]T}` has divisor 0 hence constant; so does `∏ g∘τ_{[i]T'}`; comparing at `X`,
  `X+T'` gives `g(X)=g(X+T)`, i.e. `e_ℓ(T,T)=1`. Needs translation `τ` of functions + the telescoping.
- **L2.3** `weilPairing_nondegenerate` (c): `(∀S, e_ℓ(S,T)=1) ⇒ T=O`. Verbatim (p. 96): `g=h∘[ℓ]`
  (III.4.10b) ⇒ `f=h^ℓ` ⇒ `div h=(T)−(O)` ⇒ `T=O` (III.3.3 / `Lemma 3.3`: `(P)∼(Q) ⇔ P=Q`, shipped-ish).

### L3 — `weilPairing_adjoint` (Prop 8.2) (leaf-ish, internal)
**Source: III.8 Prop 8.2, p. 97.**
> Verbatim: *"Let φ:E₁→E₂ be an isogeny of elliptic curves. Then for all m-torsion points S∈E₁[m] and
> T∈E₂[m], e_m(S, φ̂(T)) = e_m(φ(S), T)."*
Proof uses `div f = m(T)−m(O)`, `f∘[m]=g^m`, and a function `h` with `φ*((T))−φ*((O))=(φ̂T)−(O)+div h`
(exists because **III.6.1ab says φ̂T is the sum of the points of φ*((T))−φ*((O))** — the σ-bridge, and
`φ̂` is shipped as `isogDual` with `φ̂φ=[deg φ]`). Endomorphism case `E₁=E₂=E`, `φ=π`.

### L4 — `det_eq_deg_mod_ell` (Prop 8.6, finite level) (internal)
**Source: III.8 Prop 8.6, p. 99 (read at finite level `E[ℓ]` instead of `T_ℓ`).**
> Verbatim: *"e(v₁,v₂)^{deg φ} = e([deg φ]v₁,v₂) = e(φ̂φv₁,v₂) = e(φv₁,φv₂) = e(av₁+cv₂,bv₁+dv₂) =
> e(v₁,v₂)^{ad−bc} = e(v₁,v₂)^{det φ_ℓ}. Since e is nondegenerate, we conclude that deg φ = det φ_ℓ."*
For us: with `{v₁,v₂}` a basis of `E[ℓ]` and `e_ℓ(v₁,v₂)` a primitive ℓ-th root (Cor 8.1.1 / L2.3
perfectness): `e_ℓ(v₁,v₂)^{deg φ} = e_ℓ(v₁,v₂)^{det(φ|E[ℓ])}` ⇒ `deg φ ≡ det(φ|E[ℓ]) (mod ℓ)`. Uses
L2 (bilinear/alternating), L3 (adjoint), `φ̂φ=[deg φ]` (`isogDual`, shipped). Pure once L2,L3 hold.

### L5 — `frobRep` : the ring-hom `ρ_ℓ : End(E) → M₂(ZMod ℓ)` (internal)
The action of `End(E)` on `E[ℓ] ≃ (ZMod ℓ)²` (L0) is `ZMod ℓ`-linear (each `ψ` is a group hom commuting
with `ℓ`), giving `ρ_ℓ(ψ) ∈ M₂(ZMod ℓ)`, a **ring homomorphism** (`ρ_ℓ(ψ∘χ)=ρ_ℓ(ψ)ρ_ℓ(χ)`,
`ρ_ℓ([n])=n•1`). Then `det(ρ_ℓ ψ) = det(φ|E[ℓ])` (det of the linear map = det of its matrix). Leaf,
mathlib (`LinearMap.toMatrix`, `LinearMap.det_toMatrix`) + project (End acts on E[ℓ]).
- `ρ_ℓ(rπ−s) = r•ρ_ℓ(π) − s•1` (ring-hom + `ρ_ℓ([n])=n•1`).

### AG-SEP — `[ℓ]` separable for `ℓ ≠ p` (API gap / prerequisite, needed by L0.1)
**Source: III.5.4 / Cor 5.4 (p. 79), restated III.6.4(b).**
> Verbatim (III.5.5 / Cor 5.4 region, p. 79): *"Let m∈ℤ. Assume that m≠0 in K. Then the
> multiplication-by-m map on E is a finite separable endomorphism."* (Proof: `[m]*ω = mω ≠ 0`, and
> `ψ*ω = 0 ⇔ ψ` inseparable, II.4.2c.)
Status: the project has `mulByInt_isSeparable_of_witness` (parametric) + `omegaPullbackCoeff_mulByInt`
(`= m`), but the latter is entangled with the open sorry T-IV-BRIDGE-001 in `OmegaPullbackCoeff.lean`.
**Sub-development:** either (a) discharge T-IV-BRIDGE-001, or (b) prove `[ℓ]` separable for `p∤ℓ`
independently via `[ℓ]*ω = ℓ•ω` (Cor 5.3, `[m]*ω=mω`, which the project has as
`omegaPullbackCoeff_mulByInt`) + `ψ*ω≠0 ⇒ separable` (II.4.2c reverse — check project has the reverse).
This must land before L0.1.

## Provability summary
- **Discharged from project / mathlib (scaffolding):** R (Reduction shipped), L0.2, L0.3, L1.1, L1.2,
  L4 (once L2,L3), L5; the dual `φ̂φ=[deg φ]` (`isogDual`), `deg[ℓ]=ℓ²`, the σ-bridge III.6.1ab.
- **HARD CORE (new content):** L1 (pairing construction, esp. L1.3–L1.5: divisor pullback `[ℓ]*` as the
  explicit `E[ℓ]`-coset fibre sum, `f∘[ℓ]=g^ℓ`, function evaluation `g(X+S)/g(X)`), L2 (bilinear /
  alternating / nondegenerate), L3 (adjoint). These mirror Silverman pp. 93–97 and lean on the
  shipped Miller/divisor-function layer (the pairing's engine) + function-field **evaluation** API
  (the one genuinely new infrastructure: evaluating a rational function at a point, and translates
  `g∘τ_S`).
- **PREREQUISITE / RISK:** AG-SEP (`[ℓ]`-separability, entangled with T-IV-BRIDGE-001 sorry).

## Prior-B2 consultation (b2_log.jsonl, 386 entries scanned for relevant matches)
- No leaf here matches a prior B2 by name (the Weil pairing is new to the project).
- **Placeholder caveat (inherited from `pointCount_eq` / `mulByP_factors` B2s):** `rπ−s` and `π` must be
  **genuine endomorphisms** with correct pullback (not point-map-only placeholders). The rep `ρ_ℓ` acts
  via the genuine point maps; `deg π = q`, `deg(rπ−s)` are genuine degrees. Keep the placeholder guard.
- The retracted `PIC0-route-leaf1` B2 (Pic⁰ "degree-blind") is **not relevant** to Route 2: we use the
  Weil-pairing determinant, not the Pic⁰ comap dual.

## Adversarial notes (composition attacks)
- **Finite-level soundness (attack: does mod-ℓ really give the integer?):** `det(ρ_ℓ ψ)` and `deg ψ` are
  integers; L4 gives `≡ mod ℓ` for every `ℓ≠p`; Reduction Step 7 (`int_eq_of_congr_all_primes_ne`,
  shipped, axiom-clean) lifts to equality. Survived: the lift is exactly the shipped lemma; one `ℓ` is
  insufficient (only `≡`), all `ℓ≠p` suffice. ✓
- **Primitive-root attack (does `e_ℓ(v₁,v₂)` generate μ_ℓ?):** needs the pairing perfect on the 2-dim
  `E[ℓ]` — Cor 8.1.1 (surjectivity) / nondegeneracy (L2.3) on a basis. If only nondegenerate (not
  perfect), `e_ℓ(v₁,v₂)` could be 1 for a bad basis; but nondegeneracy ⇒ for each `v₁≠O` some `v₂` with
  `e_ℓ(v₁,v₂)≠1`, and on a 2-dim space the pairing matrix is `[[1,ζ],[ζ⁻¹,1]]`-shape ⇒ `ζ` primitive.
  Must prove `e_ℓ(v₁,v₂)` primitive for a chosen basis (L4 sub-step). ✓ (flagged as a real sub-step)
- **AG-SEP attack (is `[ℓ]` really separable for all `ℓ≠p`?):** yes — III.5.4, `[ℓ]*ω=ℓω≠0` since
  `ℓ≠0` in `K` (`p∤ℓ`). The risk is only formalisation-entanglement (the sorry), not mathematical. ✓

## Feasibility
The route is sound and now fully grounded in Silverman III.8 (read in full). The reduction is shipped
axiom-clean. The remaining build is the Weil-pairing construction + its three properties + the adjoint
(III.8 pp. 93–97), at finite level `E[ℓ]` — a bounded, textbook development on top of the shipped
Miller/divisor layer, whose one genuinely new infrastructure piece is **function-field evaluation at
points** (`g(X+S)/g(X)`, translates `g∘τ_S`). The single prerequisite risk is AG-SEP (the
`[ℓ]`-separability, entangled with an open project sorry), which must be discharged first. No
multi-week new theory (no Tate module, no `ℤ_ℓ` linear algebra — the finite-level optimisation removes
those). This is the largest single piece of the project but is well-understood and decomposes cleanly.
