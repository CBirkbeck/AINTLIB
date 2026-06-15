# Ticket board — Route 2 (Weil pairing) for Leaf 1

Source of truth: `.mathlib-quality/decomposition-route2-weil-pairing.md` (Silverman III.8, read in full).
Shipped, axiom-clean: `HasseWeil/WeilPairing/{IntegerSeparation,MatrixDet,Reduction}.lean` (the residual
`deg_eq_of_frobMatrix_data`). These tickets BUILD the residual `R`.

## Summary
- 10 build tickets + 3 cleanup. Critical path: SEP → TORSION → EVAL → PAIRING-DEF → PROPS → NONDEG →
  ADJOINT → DET-DEG → REP/ASSEMBLE.
- Parallel: REP (L5) is independent of PAIRING-*.
- HARD tickets: TORSION (separable fibre count), PAIRING-DEF (L1), NONDEG (L2c), ADJOINT (L3).

## REVIEWER-ENDORSED PLAN (round 19, 2026-05-31 — see `.mathlib-quality/expert-review/2026-05-31-7/`)
Route 2A confirmed soundest (NOT Route 1, NOT full Tate modules). **Attack order §8.1 → §8.2 → §8.3:**
1. **TORSION first** — `#E[ℓ]=ℓ²` via a GENERAL separable-isogeny fibre-count theorem
   `card_kernel_eq_degree_of_separable_isogeny` (reuse the Leaf-2 embeddings-as-translations style);
   NOT the affine `R→R` CoordHom (reviewer-confirmed impossible), NOT the x-line (degree 2ℓ², quotient
   by ±1, messy). This is foundational (gives the 2-dim 𝔽_ℓ-rep) and reusable.
2. **PAIRING-DEF next** — define `e_ℓ(S,T)` as the CONSTANT QUOTIENT of `(τ_S^*g_T)/g_T` (div-zero ⟹
   constant), NOT by pointwise evaluation. Build only `div_translate` + the `g_T` special case; defer a
   broad evaluation API.
3. **ADJOINT then** — separable adjoint via `picDual` (NOT the unfinished `isogDual`); needs only:
   picDual a group hom E→E, preserves E[ℓ], its divisor-class identity matches the pairing divisor,
   `picDual∘φ=[deg φ]`. Scope = SEPARABLE φ (Frobenius factor handled by Galois).
4. DET-DEG + REP + ASSEMBLE = mostly formal algebra (incl. the shipped `int_eq_of_congr_all_primes_ne`
   integer-separation, reviewer caution 4). Keep `e_ℓ^ℓ=1` as a core PROPS output (caution 2).
   Naming: "nonnegative/semidefinite", not "positive definite" (caution 1).

---

### [T-R2-SEP] `[ℓ]` separable for `ℓ ≠ p`  (prerequisite, AG-SEP)
- Status: open · File: `HasseWeil/Hasse/Separability.lean` (or new) · Depends on: none · Type: lemma
- Statement (intended):
  ```lean
  theorem mulByInt_isSeparable_of_prime_ne {K} [Field K] [DecidableEq K] (p : ℕ) [CharP K p]
      (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) :
      (mulByInt W.toAffine (ℓ : ℤ)).IsSeparable := by sorry
  ```
- Sketch: `[ℓ]*ω = ℓ•ω` (Cor 5.3 = `omegaPullbackCoeff_mulByInt`, `=ℓ`); `ℓ ≠ 0` in `K` (since `p∤ℓ`);
  `ψ*ω ≠ 0 ⇒ ψ` separable (II.4.2c reverse). **Discharge or sidestep** the `OmegaPullbackCoeff`
  T-IV-BRIDGE-001 sorry that `omegaPullbackCoeff_mulByInt` currently routes through; if the reverse
  `omegaCoeff ≠ 0 ⇒ separable` is not shipped unconditionally, that is a sub-ticket.
- Source: Silverman III.5.4 / Cor 5.4 (p. 79): *"multiplication-by-m is a finite separable endomorphism"*
  when `m ≠ 0` in `K`.

### [T-R2-TORSION] `E[ℓ] ≃+ (ZMod ℓ)²` for `ℓ ≠ p`  (L0, **PRIORITY 1**, reviewer-endorsed)
- Status: open · File: `HasseWeil/WeilPairing/Torsion.lean` (new) · Depends on: T-R2-SEP, **T-R2-SEP-FIBRE** · Type: def+lemmas
- Statement (intended): `card_torsion_ell : Nat.card W[ℓ] = ℓ^2`; `torsion_ell_basis :
  Module.Basis (Fin 2) (ZMod ℓ) W[ℓ]` (or `W[ℓ] ≃ₗ[ZMod ℓ] (Fin 2 → ZMod ℓ)`).
- Sketch: `card` from `torsionSubgroup_card_of_separable_witness` (TorsionCard:54, general `[Field F]`,
  K̄-ready) + T-R2-SEP + the fibre witness from **T-R2-SEP-FIBRE**. Then `E[ℓ]` is killed by `ℓ`, `ℓ`
  prime ⟹ `𝔽_ℓ`-vector space, `card = ℓ²` ⟹ `finrank = 2` (`Module.card_eq_pow_finrank`).
- Source: III.6.4(a/b); reviewer round 19 Q1.

### [T-R2-SEP-FIBRE] `#ker φ = deg φ` for a SEPARABLE isogeny over K̄  (the torsion sub-construction, **PRIORITY 1**)
- Status: open · File: `HasseWeil/WeilPairing/Torsion.lean` (or `EC/IsogenyKernel.lean`) · Depends on: T-R2-SEP · Type: theorem (reusable)
- Statement (intended, reviewer-recommended):
  ```lean
  theorem card_kernel_eq_degree_of_separable_isogeny [IsAlgClosed F]
      (φ : Isogeny E₁ E₂) (hsep : φ.IsSeparable) : Nat.card φ.kernel = φ.degree
  ```
  (or the fibre form `card_fiber_eq_degree_of_separable_isogeny … (Q) : #{P // φ P = Q} = φ.degree`,
  then apply at `φ=[ℓ]`, `Q=O`, `deg[ℓ]=ℓ²`).
- Sketch (Silverman III.4.10c, FUNCTION-FIELD level): a separable isogeny over `K̄` is unramified
  (étale), so every fibre has exactly `deg` points. Build at the function-field / complete-curve level —
  reuse the **Leaf-2 embeddings-as-translations** strategy (the style that closed `ker_deg_skeleton`),
  NOT an affine `R→R` map. Discharges the `h_fiber_witness` hypothesis of
  `torsionSubgroup_card_of_separable_witness`.
- Source: Silverman III.4.10(c); reviewer round 19 Q1 option (a).
- **Progress (2026-05-31, /beastmode):** `card_kernel_eq_degree_of_separable_isogeny` reduces (axiom-clean, builds) to the torsor `sepDegree_eq_card_kernel_of_separable` via `card_kernel_eq_degree_of_sepDegree_eq_card_kernel` + `isogeny_finiteDimensional` (file `HasseWeil/EC/SeparableKernelTorsor.lean`). **STATEMENT BUG FOUND (subagent, counterexample-proven):** the bare torsor is FALSE — `Isogeny` decouples `pullback` (drives `sepDegree`/`IsSeparable`) from `toAddMonoidHom` (drives `kernel`), so `{pullback:=id, toAddMonoidHom:=0}` is "separable" (`sepDegree=1`) with `kernel=⊤` (`Nat.card=0` over K̄). FIX: add coherence hypothesis `hcov` = kernel-translation-invariance of the pullback range (`∀ T∈ker φ, ∀z, τ_T(φ.pullback z)=φ.pullback z`; the f.f. shadow of `φ∘τ_T=φ`; kills the counterexample). **The Leaf-2 1−π torsor does NOT fully generalize** — its hard half routes through geometric-Frobenius/`ker=⊤`, finite-field-specific. General hard half (`sepDegree≤#ker`) needs the embedding↔kernel surjectivity over K̄ = IsGalois normality (`isGalois_of_isSeparable_and_normal` + `card_aut_eq_degree_of_isGalois` shipped, parametric on a Normal witness) OR base-change point-map functoriality (an ~80-LOC TODO in CurveMapBaseChange). Easy half (`#ker≤sepDegree`) closeable now from hcov + `translateAlgEquivOfPoint_injective`. **Sub-ticket T-R2-SEP-FIBRE-GALOIS** (the Normal/surjectivity witness) + **T-R2-SEP-FIBRE-COV** (discharge hcov for [ℓ], via PointFix `kernelTranslateAsAut` machinery).
- **Progress (2026-05-31, /beastmode) — CLEAN REDUCTION SHIPPED (axiom-clean, 0 sorry, `HasseWeil/EC/SeparableKernelTorsor.lean`, builds 2556 jobs):**
  - `card_kernel_eq_degree_of_separable_isogeny` — `#ker φ = deg φ` from (`hsep`, `h_normal`, `h_card : #ker=#Aut`) via shipped `card_aut_eq_degree_of_isGalois` + `isGalois_of_isSeparable_and_normal`.
  - `card_kernel_eq_card_aut_of_inverse_witnesses` — `h_card` from (`forward`, `inverse`, mutual-inverse identities), inline `Nat.card_congr` (PointFix's consumer is `[Fintype]`-scoped, so rebuilt without finiteness).
  - `card_kernel_eq_degree_of_separable_of_witnesses` — the full thing parametric on (`h_normal`, `forward`, `inverse`, identities).
  - `kernelTranslateForwardAut` — the CONCRETE forward witness over K̄ (`translateAlgEquivOfPoint` + `AlgEquiv.ofRingEquiv`), parametric on `hcov` (`∀ k∈ker φ, ∀ z, τ_k(φ.pullback z)=φ.pullback z`).
  So `#E[ℓ]=ℓ²` is reduced axiom-clean to the [ℓ]-witnesses: **`hcov[ℓ]`** (covariance, the f.f. shadow of `[ℓ]∘(·+k)=[ℓ]`), the **`inverse` map `Aut→ker`** (`σ↦σ(P_gen)−P_gen`, with constancy over K̄ — the deep piece, needs base-change point-map functoriality, an ~80-LOC TODO in CurveMapBaseChange), the **bijection identities**, and **`h_normal[ℓ]`** (Normal). The whole PointFix scaffold is `[Fintype K]`-scoped so does NOT transfer to K̄ — these are genuine K̄ rebuilds. NEXT: the inverse map + identities (the substantive III.4.10c core).
- **DEAD ROUTES (reviewer-confirmed round 19; see [[mulbyint-coordhom-impossible]]):**
  (i) the affine `(mulByInt ℓ).CoordHom` (`R →ₐ[F] R`) is **mathematically impossible** —
  `[ℓ]^*x = Φ_ℓ(x)/ΨSq_ℓ(x) ∉ R` (poles at the affine ℓ-torsion); `[ℓ]` does NOT preserve the affine
  chart `E∖{O}`. So `exists_heightOneSpectrum_fiber_card_eq_sepDegree_unconditional` (which takes a
  CoordHom) can NEVER be instantiated for `[ℓ]`, and the repo's `(mulByInt n).CoordHom` hypotheses
  (RouteCGeometric:247, RouteCAddFormula:377) are un-dischargeable for `mulByInt`.
  (ii) the **x-line** route (`x∘[ℓ]: E→ℙ¹`, degree `2ℓ²`) is rejected — quotient-by-±1, ramification at
  2-torsion, behaviour at `O`; "formally much messier" (reviewer).

### [T-R2-EVAL] divisor transport under translation  (**PRIORITY 2**, reviewer-narrowed)
- Status: open · File: `HasseWeil/WeilPairing/Evaluation.lean` (new) · Depends on: none · Type: def+lemmas
- Statement (intended, reviewer round 19 Q2 — the CONSTANT-RATIO approach, NOT pointwise eval):
  ```lean
  theorem div_translate (S : E[ℓ]) (g : K(E)ˣ) :
      divisorOf (τ_S^* g) = translateDivisor S (divisorOf g)
  theorem div_translate_eq_self_for_gT (S T : E[ℓ]) :
      divisorOf (τ_S^* g_T) = divisorOf g_T   -- ⟹ (τ_S^* g_T)/g_T has trivial divisor
  ```
- Sketch: uses only (1) the translation automorphism `τ_S` on `K(E)` (`translateAlgEquivOfPoint`,
  shipped), (2) divisor transport under translation, (3) "divisor zero ⟹ constant" (Constancy.lean,
  shipped). Reuse the local-ring/valuation translation work (`isTranslateMaxIdealCompatible…`,
  `pointValuation` transport). The `g_T` special case follows because `S∈E[ℓ]` permutes the fibre
  `div g_T = [ℓ]^*(T)−[ℓ]^*(O)`.
- Source: III.8 p. 93–94; reviewer round 19 Q2.
- NOTE (reviewer): do **NOT** first build a broad pointwise-evaluation API for arbitrary rational
  functions. `div_translate` + the `g_T` special case is all PAIRING-DEF needs. Pointwise evaluation is
  a later convenience, not the foundation — this makes the ticket smaller than the old "Evaluation" plan.

### [T-R2-PAIRING-DEF] the Weil pairing `e_ℓ : E[ℓ] → E[ℓ] → μ_ℓ`  (L1, reviewer-revised def)
- Status: open · File: `HasseWeil/WeilPairing/Pairing.lean` (new) · Depends on: T-R2-TORSION, T-R2-EVAL
- Type: def + well-definedness lemmas
- Sub-leaves: `exists_f_div` (Abel/Miller, project); `exists_g_div` (`[ℓ]^*(T)−[ℓ]^*(O)` principal — the
  explicit E[ℓ]-coset fibre sum `Σ_{R∈E[ℓ]}(T'+R)`, via `fiberEquivKernel` + `pullbackDiv_sub_isPrincipal`,
  shipped); `f_comp_mul_eq_g_pow` (`f∘[ℓ]=g^ℓ` after rescale).
- **Definition (reviewer round 19 Q2 — CONSTANT QUOTIENT, not pointwise eval):** by T-R2-EVAL,
  `(τ_S^* g_T)/g_T` has trivial divisor, hence is a nonzero constant `c ∈ K̄ˣ`; set
  `e_ℓ(S,T) := c` (the value layer `pairing_const_of_transport` in Constancy.lean already extracts it).
  Then `pairing_root_of_unity` (`e_ℓ^ℓ=1`, via `pairing_const_pow_eq_one`, shipped — keep as a CORE
  output, reviewer caution 2). This avoids choosing a point `X` and evaluating `g_T(X+S)/g_T(X)`.
- Source: III.8 pp. 93–94; reviewer round 19 Q2. Engine: shipped Constancy value layer + T-R2-EVAL.

### [T-R2-PAIRING-PROPS] bilinear / alternating  (L2a/b)
- Status: open · File: `HasseWeil/WeilPairing/Pairing.lean` · Depends on: T-R2-PAIRING-DEF
- Statement: `weilPairing_bilinear` (both slots; `pairing_const_mul` in slot 1 is shipped),
  `weilPairing_alternating` (`e_ℓ(T,T)=1`).
- Sketch: Prop 8.1(a)(b), pp. 94–96. Bilinearity reuses the shipped `pairing_const_mul`/`pairing_const_refl`;
  alternating uses the telescoping product `∏ f∘τ_{[i]T}`.
- Source: III.8 Prop 8.1(a)(b).
- NOTE (reviewer round 19, caution 3): **nondegeneracy is split out into its own ticket `T-R2-NONDEG`** —
  it is the most delicate part and should NOT be folded in here.

### [T-R2-NONDEG] nondegeneracy of `e_ℓ`  (L2c, **its own ticket** — reviewer caution 3)
- Status: open · File: `HasseWeil/WeilPairing/Pairing.lean` · Depends on: T-R2-PAIRING-DEF, T-R2-TORSION
- Statement: `weilPairing_nondegenerate : (∀ S, e_ℓ(S,T)=1) → T = O`.
- Sketch: Prop 8.1(c), p. 96. The standard proof: if `e_ℓ(·,T)≡1` then `g_T = h∘[ℓ]` for some `h`
  (III.4.10b), forcing `div h` to make `(T)∼(O)`, whence `T=O` by `(P)∼(Q)⇔P=Q` (Lemma 3.3). Uses the
  shipped divisor foundations (`f_T`/`g_T` existence, Abel–Jacobi/Pic⁰≅E) but is delicate — give it room.
- Source: III.8 Prop 8.1(c); reviewer round 19 (caution 3: "deserves its own ticket").

### [T-R2-ADJOINT] separable adjoint `e_ℓ(φS,T) = e_ℓ(S, picDual φ T)`  (L3, **PRIORITY 3**, picDual route)
- Status: open · File: `HasseWeil/WeilPairing/Pairing.lean` · Depends on: T-R2-PAIRING-DEF, T-R2-NONDEG
- Statement (reviewer round 19 Q3 — `picDual`, SEPARABLE scope):
  ```lean
  theorem weilPairing_adjoint_separable_picDual
      (φ : Isogeny E₁ E₂) (hsep : φ.IsSeparable) (S : E₁[ℓ]) (T : E₂[ℓ]) :
      e_ℓ (φ S) T = e_ℓ S (picDual φ T)
  ```
- Sketch: Prop 8.2, p. 97. For SEPARABLE φ the divisor pullback is multiplicity-free
  `φ^*((T)−(O)) = Σ_{φP=T}(P) − Σ_{φP=O}(P)`, so the σ-bridge `φ̂T = σ(φ^*((T))−(O))` is automatic — and
  that is exactly `picDual`. Use `picDual` (shipped, sorry-free) in the role of `φ̂`; do **NOT** need the
  genuine `isogDual` (gated on a large sorry). The pairing adjoint is a statement about action on
  points/torsion + divisor classes (Silverman's proof is Picard-divisor in nature).
- Required `picDual` facts (reviewer): (1) `picDual φ` is a group hom `E→E`; (2) preserves `E[ℓ]`;
  (3) its divisor-class identity matches the divisor used in the pairing proof; (4) `picDual∘φ=[deg φ]`
  (shipped as `picDual_comp_toAddMonoidHom`). `picDual = isogDual` can be proved LATER if wanted — not a blocker.
- SCOPE: separable φ only (= the Route-2A rescue: separable factor λ via this; inseparable Frobenius
  factor via Galois/Frobenius action). Doing the adjoint directly for inseparable `rπ−s` would reintroduce
  the σ-bridge/inseparable-pullback wall.
- Source: III.8 Prop 8.2; reviewer round 19 Q3.

### [T-R2-DET-DEG] `det(φ|E[ℓ]) ≡ deg φ (mod ℓ)` for SEPARABLE φ  (L4)
- Status: open · File: `HasseWeil/WeilPairing/Determinant.lean` (new)
- Depends on: T-R2-PAIRING-PROPS, T-R2-NONDEG, T-R2-ADJOINT, T-R2-TORSION · Type: lemma
- Statement (intended): `(det (ρ_ℓ φ) : ZMod ℓ) = ((deg φ : ℤ) : ZMod ℓ)` for separable φ.
- Sketch: Prop 8.6, p. 99: pick basis `{v₁,v₂}`, `e_ℓ(v₁,v₂)` primitive (nondegeneracy, T-R2-NONDEG);
  `e_ℓ(v₁,v₂)^{deg φ}=e_ℓ([deg φ]v₁,v₂)=e_ℓ(picDual φ·φ v₁,v₂)=e_ℓ(φv₁,φv₂)=e_ℓ(v₁,v₂)^{det}`;
  primitive root ⇒ exponents equal mod ℓ. Uses `picDual∘φ=[deg φ]` (NOT `isogDual` — reviewer Q3) and
  the separable adjoint (T-R2-ADJOINT). For `π` (inseparable) use Galois-equivariance `e_ℓ(πS,πT)=e_ℓ(S,T)^q`
  instead (π acts as `ζ↦ζ^q` on μ_ℓ) ⟹ `det ρ_ℓ(π)≡q`; `tr` via `det(1−ρπ)=deg(1−π)=#E` (1−π separable).
- Source: III.8 Prop 8.6; reviewer round 19 Q3 (picDual) + Q1 setup.

### [T-R2-REP] the ring-hom rep `ρ_ℓ : End(E) → M₂(ZMod ℓ)`  (L5)
- Status: open · File: `HasseWeil/WeilPairing/Determinant.lean` · Depends on: T-R2-TORSION · Type: def+lemmas
- Statement: `ρ_ℓ` = matrix of `ψ` on `E[ℓ]≃(ZMod ℓ)²`; `map_one`, `map_mul`, `ρ_ℓ([n])=n•1`,
  `det (ρ_ℓ ψ) = det(ψ|E[ℓ])` (mathlib `LinearMap.det_toMatrix`).
- Source: III.8 p. 98–99 (the `φ_ℓ` matrix); finite-level version.

### [T-R2-ASSEMBLE] `frobMatrix_data` → Leaf 1  (R, milestone)
- Status: open · File: `HasseWeil/WeilPairing/Hasse.lean` (new)
- Depends on: T-R2-DET-DEG, T-R2-REP, CLEANUP-ALL · Type: theorem (milestone)
- Statement: supply `deg_eq_of_frobMatrix_data`'s hypothesis with `M = ρ_ℓ(π)`: `det M ≡ q` (DET-DEG at
  `π`, `deg π = q`), `tr M ≡ t` (DET-DEG at `1−π`: `det(1−ρπ)=deg(1−π)=#E`, `tr=1−#E+q=t`),
  `det(rM−sI)=det(ρ_ℓ(rπ−s))≡deg(rπ−s)` (REP ring-hom + DET-DEG at `rπ−s`). Then
  `WeilPairing.deg_eq_of_frobMatrix_data` ⇒ `deg(rπ−s)=qr²−trs+s²` ⇒ closes
  `genuineIsogSmulSub_degree_eq_signed` / `qf_nonneg_skeleton` ⇒ the Hasse bound.
- Source: V.2.3.1 (the assembly), III.8.6.
- CAVEAT: `rπ−s`, `π` are the GENUINE endomorphisms (placeholder guard); split `r=s=0`.

### [CLEANUP-R2-1] /cleanup on Pairing.lean (after PROPS+ADJOINT) · Depends on: T-R2-ADJOINT
### [CLEANUP-R2-2] /cleanup on Determinant.lean (after DET-DEG+REP) · Depends on: T-R2-DET-DEG, T-R2-REP
### [CLEANUP-ALL] /cleanup-all on WeilPairing/ before ASSEMBLE · Depends on: all build tickets

---
## SESSION PROGRESS (2026-05-31, /beastmode) — 8 axiom-clean files shipped

DONE (HasseWeil/WeilPairing/, all `#print axioms` = {propext, Classical.choice, Quot.sound}, 0 sorry):
- IntegerSeparation, MatrixDet, Reduction — the reduction of Leaf 1 to the per-ℓ Frobenius-matrix residual.
- Discriminant — qf_nonneg from {p∤s} (Leaf 5, Silverman V.1.1).
- PairingDet — abstract Prop 8.6 `det φ = deg` via the symplectic identity (det core).
- Fiber — fibre = kernel coset (keystone foundation).
- Pullback — mult-1 geometric pullback `f*((Q))=Σ(P)` + degree (=#ker) + σ-section.
- SigmaBridge — `σ(f*((Q))−f*((O)))=#ker·P₀` (III.6.1b).

REMAINING CORE (see the FOCUS sentinel for the ordered resume plan): (1) σ-bridge↔genuine dual /
geometric↔ideal dictionary; (2) AG-SEP [ℓ]-separable (BLOCKED: EDS Wronskian sorry); (3) TORSION
E[ℓ]≅𝔽_ℓ²; (4) Weil pairing Prop 8.1 a–d (needs function evaluation infra); (5) separable adjoint
Prop 8.2 → symplectic form; (6) final assembly. Genuinely multi-session; resume via /beastmode (or
/loop /beastmode).

## SESSION PROGRESS (2026-05-31, /beastmode round 2 — orchestrator)
- **`card_torsion_ell_of_discharges` SHIPPED + axiom-clean** (new file `HasseWeil/WeilPairing/TorsionCardEll.lean`, builds, `#print axioms` = {propext, Classical.choice, Quot.sound}). This is the verified ASSEMBLY: `#E[ℓ]=ℓ²` reduced mechanically to the three `[ℓ]` discharges — `hxy` (R1, via `hcov_mulByInt_of_xy`), `h_normal` (R2), `hdesc` (R3) — with `hsep` discharged by `mulByInt_isSeparable`. Wiring = capstone `card_kernel_eq_degree_of_separable_concrete` + `card_torsion_ell_of_ker_deg`.
- **FOUNDATION GAP FOUND:** `WeierstrassCurve.Affine.Point.map` additivity (`map_add`/`map_zsmul`/`map_neg`) is MISSING from mathlib AND the repo (and the formula-naturality lemmas `map_slope`/`map_addX`/`map_addY`/`map_negY` are absent too). It is the shared bottleneck for R1 (hxy via generic-point `Point.map (ℓ•P_gen)=ℓ•Point.map P_gen`) and R3 (hdesc equivariance). Sub-ticket: prove `Affine.Point.map` is a group hom for a ring/algebra hom (new file `HasseWeil/EC/PointMap.lean`), via case-analysis + formula naturality.
- Remaining to `#E[ℓ]=ℓ²`: (R1) `hxy_mulByInt`; (FOUND) `Point.map` additivity; (R2/R3) `h_normal_mulByInt`+`hdesc_mulByInt` (Silverman III.4.10c kernel-rationality, new file `TorsionKernelRational.lean`). Then `card_torsion_ell := card_torsion_ell_of_discharges …`. Then E[ℓ]≅(ZMod ℓ)², then §5 pairing.

## MILESTONE (2026-06-01, /beastmode): #E[ℓ]=ℓ² reduced to ONE sorry
- **`card_torsion_ell` (TorsionCardEll.lean) WIRED + builds**: `(Nat.card W.toAffine[ℓ]:ℤ)=ℓ^2` for `[IsAlgClosed F]`, `(ℓ:F)≠0`. `#print axioms` = {propext, Classical.choice, Quot.sound, **sorryAx**}. The lone sorryAx is the SINGLE residual `mulByInt_genCoords_minpoly_splits` (TorsionKernelRational.lean:294).
- DONE+axiom-clean this session: `hxy_mulByInt` (R1, TorsionGeometric), `hdesc_mulByInt` + `kernelOverKE_descends` (R3+engine, TorsionKernelRational), `h_normal_mulByInt` (R2, modulo the one sorry), `card_torsion_ell_of_discharges` (assembly, TorsionCardEll), `PointMap.lean` (Affine.Point.map is already an AddMonoidHom in mathlib — additivity free).
- **THE residual** `mulByInt_genCoords_minpoly_splits`: minpoly over [ℓ]*K(E) of x_gen,y_gen splits in K(E) (Silverman III.4.10c). Route: every root of minpoly(x_gen) over Ω lies in K(E), via kernel-rationality-over-Ω (σP_gen−P_gen killed by [ℓ] ⟹ F-rational ⟹ σP_gen=P_gen+lift k, coords in K(E)). Engine = generalize `kernelOverKE_descends` from W_KE to a general F-field-extension.

## ✅ T-R2-SEP-FIBRE + #E[ℓ]=ℓ² CLOSED — AXIOM-CLEAN (2026-06-01, /beastmode)
- `card_torsion_ell` (HasseWeil/WeilPairing/TorsionCardEll.lean): `(Nat.card W.toAffine[ℓ]:ℤ)=ℓ^2` for `[IsAlgClosed F]`, `(ℓ:F)≠0`. **`#print axioms` = [propext, Classical.choice, Quot.sound] — NO sorryAx.** VERIFIED.
- All discharges axiom-clean: `hxy_mulByInt`, `h_normal_mulByInt`, `hdesc_mulByInt`, `mulByInt_genCoords_minpoly_splits` (Silverman III.4.10c closed via Route A: kernel-rationality over Ω + embeddings-land-in-K, engine `kernelDescends_general` generalising `kernelOverKE_descends`). Mathlib keys: `Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly`, `Polynomial.Splits.of_splits_map_of_injective`, `Affine.Point.map` (AddMonoidHom).
- T-R2-SEP-FIBRE: **DONE**. T-R2-TORSION: card half DONE; basis/(ZMod ℓ)² half NEXT.

## T-R2-EVAL progress (2026-06-01): items 1-4 built, blocked on ∞-transport
- `HasseWeil/WeilPairing/DivisorTranslate.lean` builds; ships div-transport items 1-4. Pairing payoff `projectiveDivisorOf_translate_weilFunction_div_eq_zero` (feeds `pairing_const_of_transport`, VERIFIED) — but carries sorryAx via the SOLE residual `ordProj_translate_infinity` = `IsTranslateOrdAtInftyCompatible` (TranslationOrd.lean:5226), the order-at-∞ transport for translation by S≠0. Affine transport `translate_ord_eq_all_nonzero` (PROVEN) + sign `ord_P P(τ_S f)=ord_{P+S}f`. UNAVOIDABLE: [ℓ]^*(O) includes ∞. Sub-ticket T-R2-EVAL-INFTY.

## ✅ T-R2-EVAL DONE — AXIOM-CLEAN (2026-06-01, /beastmode)
- `HasseWeil.projectiveDivisorOf_translate_weilFunction_div_eq_zero` (DivisorTranslate.lean): `projectiveDivisorOf((τ_S g)/g)=0` for g a Weil function (div = pullbackDiv T − pullbackDiv 0), S∈ker[ℓ]. **`#print axioms`=[propext,Classical.choice,Quot.sound]**. Feeds `pairing_const_of_transport` (verified).
- Deep blocker DISCHARGED: `isTranslateOrdAtInftyCompatible_translateAlgEquivOfPoint` (new `HasseWeil/EC/TranslateOrdInfty.lean`) — the order-at-∞ transport `ord_P P(τ_k f)=ordAtInfty f` for P+k=O, previously an undischarged repo obligation. Axiom-clean. Via `ordAtInftyValuation`/`pointValuation_comap` + the basis-summands-distinct valuation argument. (+ 6-line helper in PoleDivisor2Tor.lean.)
- NEXT: T-R2-PAIRING-DEF.

## ✅ T-R2-PAIRING-DEF + bilinear-left + e_ℓ^ℓ=1 — AXIOM-CLEAN (2026-06-01, /beastmode)
- `HasseWeil/WeilPairing/Pairing.lean` SORRY-FREE. `weilPairing W ℓ hℓ S T hS hT : F` (constant ratio via `pairing_const_of_transport` + EVAL payoff), `weilPairing_ne_zero`, `weilPairing_refl_left` (e_ℓ(0,T)=1), `weilPairing_mul_left` (bilinear in S, via `pairing_const_mul` + `translateAlgEquivOfPoint_add_apply`), **`weilPairing_pow_eq_one`** (e_ℓ^ℓ=1) — all `#print axioms`=[propext,Classical.choice,Quot.sound].
- KEY: e_ℓ^ℓ=1 proved via bilinearity-left (e_ℓ(S,T)^ℓ=e_ℓ(ℓ•S,T)=e_ℓ(0,T)=1), AVOIDING the divisor-pullback functoriality (`g_T^ℓ∈[ℓ]^*K(E)`). The [ℓ]-surjectivity gap was sidestepped via a cardinality argument (`mulByEllTorsionHom_surjective`, using card_torsion_ell at ℓ and ℓ²).
- NEXT: divisor-pullback functoriality (foundational, unblocks bilinear-T/NONDEG/ADJOINT), then DET-DEG→ASSEMBLE.

## Divisor-pullback functoriality (2026-06-01): assembled, 1 residual
- `HasseWeil/WeilPairing/DivisorPullback.lean` builds. `projectiveDivisorOf_pullback_eq_pullbackDivisor` (div(φ^*h)=φ^*(div h)) ASSEMBLED axiom-clean modulo per-place core. ∞-half `inftyOrdTransport_mulByInt` + `ordAtInfty_mulByInt_y_eq_neg_three` PROVEN axiom-clean (field-general). Item-3 corollaries (`pullbackDivisor_weilDivisor`, `projectiveDivisorOf_pullback_weilFunction` = III.8.1 `f_T∘[ℓ]=g_T^ℓ` divisor) stated/proven modulo core.
- SOLE residual `ordTransport_affine_mulByInt` (DivisorPullback.lean:642): `ord_P P([ℓ].pullback h)=ord_{[ℓ]P}h` affine, mult 1 = geometric unramifiedness of [ℓ]. Decomp: (1) finite-place pinning lemma (smooth-pt ord_P analog of `eq_ordAtInftyValuation_of_x_y`), (2) local `ord_P P(mulByInt_x/y ℓ)` mult 1. Route = the PROVEN valuation-pinning (TranslateValuation/TranslateOrdInfty), NOT the Dedekind sum_ramification_inertia bridge (= V.1.3-CORE-hard).

## ✅ T-R2-REP DONE — AXIOM-CLEAN (2026-06-01, /beastmode)
- `HasseWeil/WeilPairing/Representation.lean` SORRY-FREE. `rhoEll ψ : Matrix (Fin 2)(Fin 2)(ZMod ℓ)` (matrix of ψ|E[ℓ] in torsion_ell_basis, via `torsionRestrict` = `toZModLinearMap` + `LinearMap.toMatrix`). `rhoEll_comp`(map_mul), `rhoEll_id`(map_one), `rhoEll_add`, **`rhoEll_mulByInt`** (ρ_ℓ([n])=(n:ZMod ℓ)•1), `rhoEll_det` (=LinearMap.det), `rhoEll_trace`. All #print axioms=[propext,Classical.choice,Quot.sound].

## Divisor-pullback functoriality for [ℓ]: char≠2 AXIOM-CLEAN (2026-06-02)
- `HasseWeil/WeilPairing/DivisorPullback.lean` + helpers (`MulByIntSamePlace`, `MulByIntUnramified`, `WronskianGeneral`, `IsogenyOrdTransport`): the [ℓ]-divisor-pullback functoriality `projectiveDivisorOf_pullback_weilFunction` (III.8.1, `f_T∘[ℓ]=g_T^ℓ` divisor) is AXIOM-CLEAN parametric on `ProjOrdTransport[ℓ]`.
- `ProjOrdTransport[ℓ]` (`projOrdTransport_mulByInt`): AXIOM-CLEAN for char≠2. char=2 has ONE leaf `ord_P_mulByInt_y_sub_const_eq_one` (2-torsion affine IMAGE, y-uniformizer) needing a Kähler-differential ord_P bridge (`[ℓ]^*ω=ℓω` → local order). 
- KEY ROUTES that worked: (1) EDS addition formula DODGED via route-B (`wronskian_Φ_ΨSq_general` from the differential `omegaCoeff_mulByInt`, downstream, general field). (2) ∞/torsion case via translation-invariance of mulByInt_x/y (no new simple-zero). (3) affine via uniformizer-pullback + glue `comap_pointValuation_eq_of_isEquiv_of_ord_eq_one`. (4) ∞/affine-non-2-tor: AXIOM-CLEAN all char.
- For the PAIRING (ℓ odd): div(g_T)=[ℓ]^*(T)−[ℓ]^*(O), support = fibres over E[ℓ] pts (non-2-tor affine + O for ℓ odd) — NEVER affine 2-torsion. So support-restricted functoriality is char-uniform AXIOM-CLEAN, dodging the char=2 leaf. NEXT: support-restrict, then bilinear-T/NONDEG/ADJOINT→DET-DEG→ASSEMBLE.

## ★ ROUTE 2A ASSEMBLED — Hasse bound reached via Weil pairing (2026-06-02) ★
- **`hasse_bound_via_weil_pairing` (HasseAssembly.lean) AXIOM-CLEAN** [propext,Classical.choice,Quot.sound], parametric on the per-ℓ Frobenius-matrix data `hres` (standard project idiom). `qf_nonneg_skeleton_of_weil_det_data` axiom-clean.
- **DET-DEG `det_rhoEll_eq_degree` (DetDeg.lean)**: det(ρ_ℓ φ)=(deg φ:ZMod ℓ) from `weilPairing_scaling`, via the additive symplectic form `omegaForm` (discrete-log of e_ℓ through `rootsOfUnity_addEquiv_zmod`, alternating+nondeg+scaling) + shipped `PairingDet.det_eq_of_alternating_scaling` + `rhoEll_det`. Plus ρ_ℓ ring-map identities (`rhoEll_sub/_zsmul/one_sub_rhoEll/smul_rhoEll_sub`) + `frob_det_residual_of_weil_scaling` (matches `Reduction`/`Assembly` hres shape exactly).
- **WHOLE §5 BUILT.** All WeilPairing files sorry-free EXCEPT the isolated deep residuals:
  1. `mulByInt_point_surjective` (PairingNondeg) — [ℓ] surjective on E(K̄), Silverman III.4.10b.
  2. `ord_P_mulByInt_y_sub_const_eq_one` char=2 (MulByIntUnramified) — 2-torsion y-uniformizer, needs Kähler-diff ord_P bridge (dodgeable via support-restriction for ℓ odd).
  3. per-ℓ Frobenius matrix data over K̄ (`hres`) — base-change-to-K̄ + inseparable-π Frobenius-equivariance (ζ↦ζ^q).
  4. ADJOINT `hcomm`/`hfact` hyps — picDual divisor-class identity for genuine [ℓ] (parametric, true for separable isogenies).
- AXIOM-CLEAN end-to-end pieces: card_torsion_ell, E[ℓ]≅(ZMod ℓ)², EVAL+∞-transport, pairing DEF/ne_zero/refl/mul_left/mul_right/pow_eq_one/self(alternating)/antisymm, REP, functoriality(char≠2), NONDEG(mod #1), ADJOINT(adjoint clean; scaling mod functoriality), DET-DEG(mod #1,#2), Hasse assembly.

## ★★ §5 FULLY SORRY-FREE — entire Weil-pairing chain axiom-clean (2026-06-02) ★★
- TOTAL real sorries across all §5 + [ℓ] helper files = **0**. char=2 2-torsion leaf CLOSED (`ord_P_mulByInt_y_sub_const_eq_one` via the invariant-differential bound `ord_P_mulByInt_y_sub_const_le_one` in `DifferentialOrd.lean` + direct numerator-unit split).
- `projOrdTransport_mulByInt` (full [ℓ]-divisor-pullback functoriality, ALL char), `weilPairing_mul_right`, `det_rhoEll_eq_degree`, `weilPairing_nondegenerate` — ALL axiom-clean [propext,Classical.choice,Quot.sound].
- SILVERMAN-VERIFIED faithful (read III.8 Prop 8.1a-e/Cor 8.1.1/Prop 8.2, Prop 8.6, V.1.1 directly): def e_m=g(X+S)/g(X), bilinear/alternating(telescoping)/nondeg/adjoint/det=deg/tr=1+det−det(1−), Hasse via deg=pos-def-qf + Cauchy-Schwarz. No straying.
- REMAINING for UNCONDITIONAL Hasse = exactly 2 PARAMETRIC geometric hypotheses (not sorries): (a) ADJOINT `hcomm`/`hfact` = picDual divisor identity for genuine [ℓ] (Silverman III.6.1b/8.2); (b) per-ℓ Frobenius matrix data `hres` over F̄_q (base-change + inseparable π via Galois-equivariance ζ↦ζ^q, Prop 8.1d).

## ★★★ ADJOINT COHERENCE RESOLVED (2026-06-02) ★★★
- `hcomm` → `hcomm_of_isGenuineWith` (HcommLemma.lean, axiom-clean): reduces to per-isogeny `hgcomm` (φ-additivity shadow at P_gen; automatic for [ℓ]).
- `hfact` → `PicDualDivisorClass` (HfactLemma.lean, axiom-clean) → **DISCHARGED** (PicDualDivisorClassLemma.lean): `picDualDivisorClass_mulByInt` AXIOM-CLEAN ([ℓ] instance, fully), `weilPairing_adjoint_of_naturality` AXIOM-CLEAN (separable adjoint via standard witnesses). Route: Abel σ=0⟹principal (char-free `projIsPrincipal_of_degZero_of_sigma_eq_zero`) + σ-bridge `sigma_pullbackDiv_sub` (#ker·P₀) + shipped dual relation `picDual_comp_toAddMonoidHom_of_surjective` — BYPASSING the ClassGroup↔ProjectiveDivisor bridge.
- REMAINING for unconditional Hasse = the F̄_q base-change `hres` (IsogenyBaseChange.lean has `mkBaseChange`+Frobenius-twist): instantiate DET-DEG at 1−π,rπ−s (separable, via the now-reduced scaling + per-isogeny Naturality/hgcomm/surjectivity) and inseparable π (Galois-equiv e_ℓ(πS,πT)=e_ℓ(S,T)^q). The genuine final geometric frontier.

## ★★★ MILESTONE (2026-06-02): BOTH WALLS BROKEN; Route 2A converged to standing residuals ★★★
Unconditional `hasse_bound_unconditional_of_baseChange_scalings` (FrobMatrixData.lean) reduced AXIOM-CLEAN to `FrobBaseChangeScalings` (3 leaves). NEW axiom-clean files: SeparableScaling (CoordHom-free scaling `weilScales_of_dualComp`), FrobeniusGalois (`frobeniusScaling_of_witnesses`), OneSubScaling (`oneSubFrobeniusScaling_of_data`), IsogenyBaseChangeConcrete (`baseChangePullback`+`finrankBaseChange` — degree-preservation DISCHARGED), OneSubWitnesses (`frobeniusHomBaseChange=geomFrobeniusPoint`, finiteKer, #ker=pointCount PROVED; hkerdeg→V.1.3, hsurj→dual REDUCED).
- CoordHom wall: BROKEN (abstract dual δ, δ∘φ=[#ker], CoordHom-free).
- Function-field base-change: COMPLETE (CurveMapBaseChange, axiom-clean) — was wrongly believed deferred.
REMAINING (= project's standing witness-parametric residuals, base-changed, CoordHom-FREE): IsDualOf(1−V̄), ProjOrdTransport, hcomm' covariance — for π/1−π/rπ−s over K̄; leaf-1 FrobeniusScalingWitnesses (hfact); leaf-3 PencilScalingData; + KNOWN V.1.3 (deg(1−π)=#E); + wiring. See memory route2a-converged-to-standing-residuals.

## Sharper convergence (2026-06-02 cont'd): leaf-2 dual → base-changed standing witnesses
NEW axiom-clean: OneSubDual.lean (`oneSubFrobeniusDual_isDual`, `mkOneSubScalingDataConcrete_of_charPoly`), FrobeniusCharPoly.lean (`frobeniusCharPolyBaseChange_of_verschiebung`, `mkOneSubScalingDataConcrete_of_verschiebung`).
Leaf-2 dual (δ/hdc/hself + hsurj) reduced to ONE Prop `FrobeniusVerschiebungBaseChange` = ∃V̄,(π̄+V̄=[t])∧(V̄∘π̄=[q]) over K̄ = K̄-base-change of standing K-witnesses (sum_trace_frobenius_witness + verschiebung_comp_frobenius_eq_mulByInt_q).
CORE open infra = isogeny POINT-MAP base-change over K̄ (Verschiebung): pullback base-changes (complete), pullback→point-map bridge over K̄ has none. Also: ProjOrdTransport/hcomm' base-changed; V.1.3 (known); leaf-1 hfact, leaf-3 PencilScalingData, wiring. See memory route2a-converged-to-standing-residuals.

## CLEANUP (2026-06-02): dead files removed, canonical divisor-route wired
- DELETED OneSubDual.lean + FrobeniusCharPoly.lean (char-poly/trace route — superseded by OneSubDualDivisor, CIRCULAR per reviewer round 16, nothing imported them).
- WIRED into HasseWeil.lean (default build): OneSubDualDivisor, PencilDualDivisor, SeparableWitnesses. `lake build HasseWeil` GREEN 8321 jobs. Both leaf discharges (oneSubFrobeniusScaling_of_divisorDual, pencilScaling_of_divisorDual) axiom-clean in the integrated build.
- mulByInt_isSeparable: benign dup (mine in ns ...TorsionGeometric, yours in ...WeilPairing) — different fully-qualified names, no clash; left as-is.
- CANONICAL Route-2A separable path = divisor-pushforward dual (OneSubDualDivisor/PencilDualDivisor + SeparableScaling weilScales_of_dualComp). NOT char-poly/trace (deleted), NOT picDual-CoordHom (impossible).
- REMAINING to finish: per-isogeny witnesses {ProjOrdTransport, hsurj (no general lemma — needs "nonconstant isog surjective over K̄"), hgcomm/hcomm', #ker=deg(rπ−s)} for base-changed 1−π & rπ−s + leaf-1 (π) Galois-equivariance / FrobeniusScalingWitnesses.
