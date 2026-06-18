# HANDOVER — Hasse bound, Route 2A (Weil pairing), torsion frontier
*Written 2026-05-31. For a new worker picking up the proof. Self-contained.*

---

## 0. TL;DR — where the frontier is right now

The whole Hasse bound is reduced, **axiom-clean**, to the finite-level Weil-pairing route (Route 2A,
expert-reviewer-endorsed). The **current frontier is `#E[ℓ] = ℓ²`** (the geometric ℓ-torsion has ℓ²
points over `K̄`, for `ℓ ≠ p`). This session built the entire Silverman III.4.10c **embedding↔kernel
torsor** axiom-clean and reduced `#E[ℓ]=ℓ²` to **exactly three concrete `[ℓ]` facts**, all in files
that compile:

1. **`hxy`** — coordinate-function translation-invariance: for `k ∈ E[ℓ]`,
   `τ_k(mulByInt_x ℓ) = mulByInt_x ℓ` and the `mulByInt_y` analogue. (This *is* `hcov` for `[ℓ]`.)
2. **`h_normal`** — the extension `K(E)/[ℓ]*K(E)` is `Normal`.
3. **`hdesc`** — descent: `σ(P_gen) − P_gen` is an `F`-rational kernel point, for `σ ∈ Aut`.

`h_normal` and `hdesc` BOTH follow from one fact: **kernel-rationality of `[ℓ]` over `K̄`** (the
ℓ-torsion points are `K̄`-rational), which is reachable **CoordHom-free** via the division polynomial
(the ℓ-torsion x-coords are roots of `ψ_ℓ ∈ K̄[x]`, and `K̄` algebraically closed ⟹ no new roots in
extensions). `hxy` is the addition-formula identity `x([ℓ](P+k)) = x([ℓ]P)`.

**These three facts are the only gap between the current code and `#E[ℓ]=ℓ²`.** Everything downstream
(`#E[ℓ]=ℓ² ⟹ E[ℓ]≅(ZMod ℓ)² ⟹` the pairing `⟹` Hasse) has a concrete plan (§5).

---

## 1. The overall goal and the big-picture chain

**Goal:** the Hasse bound `|#E(F_q) − q − 1| ≤ 2√q` (Silverman V.1.1), as a constructive,
characteristic-uniform Lean 4 / mathlib formalisation.

**The reduction chain (the top of it is shipped & axiom-clean):**
```
hasse_bound  (HasseWeilSkeleton.lean)
  ⟸ qf_nonneg_skeleton : ∀ r s, 0 ≤ q·r² − t·r·s + s²    (GapSpines.lean:2142, THE one open leaf)
  ⟸ [Route 2A] qf_nonneg_of_pairing_scaling : qf_nonneg ⟸ hscale   (WeilPairing/Assembly.lean, SORRY-FREE)
       hscale = per prime ℓ≠p, a Frobenius matrix M over ZMod ℓ with the symplectic
                scaling φᵀ·J·φ = (deg φ)•J  for φ ∈ {M, 1−M, rM−sI}      (= Silverman III.8.6)
```
The **second leaf, `ker_deg_skeleton` (deg(1−π)=#E), is CLOSED** (axiom-clean). So the whole bound
rests on `hscale`, i.e. on building the **Weil pairing** `e_ℓ` and its `det = deg` property.

`hscale` needs, per ℓ: the torsion module `E[ℓ]≅(ZMod ℓ)²`, the pairing `e_ℓ`, and the per-isogeny
scaling. **The torsion module is the current target** (and the prerequisite for everything else).

---

## 2. The strategy (Route 2A) — and the expert reviewer's endorsement

Route 2A proves `det(ρ_ℓ φ) ≡ deg φ (mod ℓ)` via the Weil pairing scaling
`e_ℓ(φv₁,φv₂)=e_ℓ(v₁,v₂)^{deg φ}` (Silverman III.8.6), which uses only single-isogeny facts — it is
**additivity-free**, bypassing the characteristic-p stall of the classical "degree is a quadratic
form" route (Route 1). Reviewer **round 19** (see `REVIEW_BRIEF.md` + `expert-review/2026-05-31-7/`)
confirmed Route 2A is the soundest path (NOT Route 1, NOT a full Tate-module route) and gave the
attack order:

1. **`#E[ℓ]=ℓ²` FIRST** — via a *general separable-isogeny fibre-count theorem*
   (`card_kernel_eq_degree_of_separable_isogeny`), the embeddings-as-translations style, **NOT** an
   affine CoordHom (impossible — see §6), **NOT** the x-line map. ← **WE ARE HERE.**
2. **Pairing definition** via the **constant ratio** `(τ_S^*g_T)/g_T` (NOT pointwise evaluation).
3. **Separable adjoint** via `picDual` (NOT the unfinished `isogDual`).
4. **DET-DEG + REP + ASSEMBLE** — mostly formal algebra.

Full ticket board with the reviewer's revisions: `.mathlib-quality/tickets-route2-weil-pairing.md`.

---

## 3. What is DONE (this is solid — built & verified this session and before)

### 3a. Shipped before this session (axiom-clean)
- The whole top reduction (`qf_nonneg_of_pairing_scaling`, Prop 8.6 abstract `PairingDet.lean`,
  `Discriminant`, `Fiber`, `Pullback` = the mult-1 geometric divisor pullback, `SigmaBridge`).
- The pairing-VALUE layer (`Constancy.lean`: `pairing_const_of_transport/_pow_eq_one/_mul/_refl`).
- `ker_deg_skeleton` (Leaf 2, deg(1−π)=#E) — CLOSED.
- The divisor foundation (`WeilFunction.lean`: `weilDivisor`, `weilFunction_exists`,
  `pullbackDiv_sub_isPrincipal`).

### 3b. Built THIS session — the III.4.10c torsor (the big new piece)

**`HasseWeil/EC/SeparableKernelTorsor.lean`** (0 sorry, every decl `#print axioms` =
`[propext, Classical.choice, Quot.sound]`). The general embedding↔kernel torsor for a separable
**endomorphism** `φ` of `E` over `K̄`:
- `card_kernel_eq_degree_of_separable_isogeny (φ) (hsep) (h_normal) (h_card)` : `#ker φ = deg φ`
  — via the shipped Galois machinery `Isogeny.card_aut_eq_degree_of_isGalois` +
  `isGalois_of_isSeparable_and_normal` (in `EC/IsogenyKernel.lean`).
- `card_kernel_eq_card_aut_of_inverse_witnesses` : `h_card` (`#ker = #Aut`) from forward/inverse
  maps + mutual-inverse identities (inline `Nat.card_congr`).
- `kernelTranslateForwardAut (φ) (hcov)` : the CONCRETE forward map `k ↦ τ_k`, over `K̄`
  (`translateAlgEquivOfPoint` + `AlgEquiv.ofRingEquiv`), parametric on the covariance `hcov`.
- **`card_kernel_eq_degree_of_separable_concrete (φ) (hsep) (hcov) (h_normal) (hdesc)`** : the
  CAPSTONE — `#ker φ = deg φ` reduced to those four hypotheses. The substantive bijection content
  — the **inverse map `σ ↦ σ(P_gen)−P_gen`, BOTH mutual-inverse identities** (via
  `algEquiv_ext_x_y_gen`), the **σ-equivariance/kernel-membership brick `genericPointAct_mem_ker_g`**,
  and the **action lemma `translateAlgEquivOfPoint_map_genericPoint`** (`τ_k(P_gen)=P_gen+k`) — is
  all BUILT. This generalises the `1−π`-only torsor in `GapSpines.lean` (`emb_le_card_kernel` etc.),
  dropping its geometric-Frobenius / `ker=⊤` crutch.

**`HasseWeil/WeilPairing/TorsionGeometric.lean`** (0 sorry, builds):
- `mulByInt_isSeparable (ℓ) (hℓ : (ℓ:F)≠0)` — `[ℓ]` separable over `K̄` (re-derived field-general
  via the Kähler/formal-group route, NOT the `[Finite K]`-scoped `TorsionSeparable.lean` version).
  Discharges `hsep`.
- `hcov_of_xy` + `hcov_mulByInt_of_xy (ℓ) (hℓ) (hxy)` — reduces `hcov[ℓ]` to **`hxy`** (the two
  generator equalities `τ_k(mulByInt_x ℓ)=mulByInt_x ℓ`, `τ_k(mulByInt_y ℓ)=mulByInt_y ℓ`), via
  `algHom_ext_x_y_gen` + `mulByInt_pullback_x/_y`.
- `card_torsion_ell_of_ker_deg (ℓ) (hℓ) (h_ker_deg : #ker[ℓ]=deg[ℓ])` : `#E[ℓ]=ℓ²`, via
  `torsionSubgroup_card_of_witness`. (So once `#ker[ℓ]=deg[ℓ]` is in hand, `#E[ℓ]=ℓ²` is immediate.)

Build check: `lake build HasseWeil.WeilPairing.TorsionGeometric HasseWeil.EC.SeparableKernelTorsor`
→ "Build completed successfully (2963 jobs)". (Pre-existing `sorry`s in OTHER files — e.g.
`OmegaPullbackCoeff`, `DualIsogeny`, `Hasse/OpenLemmas` — are NOT on this path.)

---

## 4. What is LEFT (the only gap to `#E[ℓ]=ℓ²`)

Three concrete `[ℓ]` facts, then pure wiring. Instantiate
`card_kernel_eq_degree_of_separable_concrete` at `φ = mulByInt W.toAffine ℓ`:

| # | Residual | Statement | Difficulty / route |
|---|----------|-----------|--------------------|
| R1 | **`hxy`** | `∀ k∈E[ℓ], τ_k(mulByInt_x ℓ)=mulByInt_x ℓ ∧ (…y…)` | MODERATE. The addition-formula identity `x([ℓ](P+k))=x([ℓ]P)`. `mulByInt_x = Φ_ff/ΨSq_ff` (`MulByIntPullback.lean:59`); `τ_k` acts on `x_gen` by `translateX_xy`; reduce to a division-polynomial / addition-formula functional identity. See `GenericPointZsmul.lean` (`evalEval_φ_at_mulByInt_*`) and the `translateAlgEquivOfPoint_apply_x_gen` action lemmas. |
| R2 | **`h_normal`** | `Normal K(E)/[ℓ]*K(E)` | from kernel-rationality (R-KR below). |
| R3 | **`hdesc`** | `∀σ∈Aut, ∃k∈ker[ℓ], lift k = genericPointAct σ − P_gen` | from kernel-rationality (R-KR). The membership half is the shipped `genericPointAct_mem_ker_g`; only the descent to `F`-rationality remains. |
| **R-KR** | **kernel-rationality** | every `P` with `[ℓ]P=O` (over any ext. of `K̄`) has coords in `K̄` | DEEP but CoordHom-FREE: ℓ-torsion x-coords are roots of `ψ_ℓ ∈ K̄[x]` (`ΨSq`, see `MulByIntPullback.lean:140 ΨSq_poly_ne_zero`, `OrdAtInftyBridge.lean ΨSq_ff`), `K̄` alg-closed ⟹ no new roots in extensions ⟹ x-coords in `K̄`; `y` from the curve eqn over `K̄`. **This is THE remaining geometric sub-development.** |

**Then the wiring (all shipped lemmas):**
```
card_kernel_eq_degree_of_separable_concrete (mulByInt ℓ) (mulByInt_isSeparable …)
    (hcov_mulByInt_of_xy … hxy) (h_normal) (hdesc)          -- gives #ker[ℓ] = deg[ℓ]
  ▸ deg[ℓ] = ℓ²            (Basic.lean:1122 mulByInt_degree — check exact natAbs/sq form)
  ▸ card_torsion_ell_of_ker_deg                              -- gives #E[ℓ] = ℓ²
  ▸ E[ℓ] is ℓ-torsion + card ℓ² ⟹ ZMod ℓ-module, finrank 2  (Module.card_eq_pow_finrank)
                                                              -- gives E[ℓ] ≅ (ZMod ℓ)²
```

---

## 5. The plan AFTER `#E[ℓ]=ℓ²` (reviewer-endorsed, §2 attack order 2–4)

Once `E[ℓ]≅(ZMod ℓ)²` is in hand, follow `tickets-route2-weil-pairing.md`:

1. **T-R2-EVAL** — build ONLY `div_translate` (`divisorOf(τ_S^*g)=translateDivisor S (divisorOf g)`)
   + the `g_T` special case. **Do NOT** build a broad pointwise-evaluation API (reviewer).
2. **T-R2-PAIRING-DEF** — define `e_ℓ(S,T)` as the **constant quotient** of `(τ_S^*g_T)/g_T`
   (div-zero ⟹ constant; the `Constancy.lean` value layer extracts it). Keep `e_ℓ^ℓ=1` a core output.
3. **T-R2-PAIRING-PROPS** (bilinear/alternating) + **T-R2-NONDEG** (nondegeneracy — its OWN ticket).
4. **T-R2-ADJOINT** — `weilPairing_adjoint_separable_picDual`: use `picDual` (sorry-free,
   `picDual∘φ=[deg φ]` shipped), NOT `isogDual`. SEPARABLE scope only (Frobenius factor via Galois).
5. **T-R2-DET-DEG / REP / ASSEMBLE** — Prop 8.6 assembly + the matrix/integer endgame
   (`int_eq_of_congr_all_primes_ne` already implements the integer-separation). π handled via
   Galois-equivariance `e_ℓ(πS,πT)=e_ℓ(S,T)^q`.

---

## 6. DEAD ENDS & WARNINGS (do not waste time here)

- **`(mulByInt ℓ).CoordHom` is MATHEMATICALLY IMPOSSIBLE** (an `R →ₐ R` map). `[ℓ]^*x =
  Φ_ℓ/ΨSq_ℓ ∉ R` (poles at the affine ℓ-torsion); `[ℓ]` does not preserve the affine chart. Frobenius
  is the lone exception (`x↦x^q` polynomial). **Reviewer-confirmed.** Consequence: the
  `exists_heightOneSpectrum_fiber_card_eq_sepDegree_unconditional` route + all `CurveMapBaseChange`
  base-change machinery (gated on a CoordHom) are USELESS for `[ℓ]`. **`hdesc`/kernel-rationality MUST
  go CoordHom-free** (the division-polynomial route, R-KR). See memory `mulbyint-coordhom-impossible`.
- **`HasseWeil/Hasse/PointFix.lean` is `[Fintype K]`-scoped** (finite field) — its `kernelTranslate*`
  / `aut_kernel_equiv_of_inverse_witnesses` scaffold is USELESS over `K̄`. We rebuilt the needed pieces
  in `SeparableKernelTorsor.lean` without finiteness. Don't try to reuse PointFix over `K̄`.
- **The `1−π` torsor in `GapSpines.lean` does NOT generalise** — its hard half routes through
  geometric Frobenius + `ker=⊤` (finite-field specific). The general version is the rebuilt
  `SeparableKernelTorsor.lean`.
- **Placeholder anti-pattern is FORBIDDEN**: never an `Isogeny` whose `pullback` ≠ its
  `toAddMonoidHom` morphism. The `Isogeny` structure decouples these two fields — this is WHY the bare
  `sepDegree φ = #ker φ` is FALSE and the capstone needs the coherence inputs (`hcov`, `hdesc`).
- **Verify against the in-repo Silverman PDF** before recording any impossibility/dead-end. PDF offset
  = book page + 18. (User directive; a past "Pic⁰ degree-blind" dead-end was a misdiagnosis.)
- **Don't catastrophize.** The Route-2A leaves are bounded textbook Silverman III.8 (adversarially
  `/develop --decompose`'d). "Genuinely multi-session bounded build" = grind it, not stop. But each
  leaf DOES contain a real geometric sub-construction (not trivial assembly) — calibrate between
  "trivial" and "research-scale". See memory `dont-catastrophize-decomposed-leaves`.

---

## 7. Build / verify

```bash
# the two new files (the torsion frontier):
lake build HasseWeil.WeilPairing.TorsionGeometric HasseWeil.EC.SeparableKernelTorsor
# axiom check (must be [propext, Classical.choice, Quot.sound]):
echo 'import HasseWeil.EC.SeparableKernelTorsor
#print axioms HasseWeil.card_kernel_eq_degree_of_separable_concrete' > /tmp/ax.lean
lake env lean /tmp/ax.lean
```
Incremental builds of these files are ~5–11s (deps cached). `#print axioms` is the gate — no
`sorryAx`, no custom axioms.

---

## 8. Pointers

- **Tickets:** `.mathlib-quality/tickets-route2-weil-pairing.md` (the full Route-2A board, with the
  round-19 reviewer revisions + the T-R2-SEP-FIBRE progress log).
- **Reviewer correspondence:** `REVIEW_BRIEF.md` (round 19) +
  `.mathlib-quality/expert-review/2026-05-31-7/{brief,reply,integration,state}.md`.
- **Memory (auto-loaded each session, `~/.claude2/.../memory/`):** `sep-kernel-torsor-built`
  (this milestone), `leaf1-route2a-endorsed-plan`, `mulbyint-coordhom-impossible`,
  `dont-catastrophize-decomposed-leaves`, `route2a-scaling-additivity-free`, `v13-leaf2-closed`.
- **Key files:** `HasseWeil/EC/SeparableKernelTorsor.lean`, `HasseWeil/WeilPairing/TorsionGeometric.lean`,
  `HasseWeil/EC/IsogenyKernel.lean` (the kernel/sepDegree/Galois machinery),
  `HasseWeil/WeilPairing/{Assembly,PairingDet,Constancy,WeilFunction}.lean`,
  `HasseWeil/GapSpines.lean` (the `1−π` torsor template + `qf_nonneg_skeleton`).

### Suggested first move for the new worker
Pick up **R1 (`hxy`)** — it is the most self-contained (an addition-formula / division-polynomial
functional identity, no descent), and closing it fully discharges `hcov` for `[ℓ]`. Then **R-KR**
(division-polynomial kernel-rationality), which discharges both `h_normal` and `hdesc`. Then the §4
wiring gives `#E[ℓ]=ℓ²`, and §5 is the remaining Weil-pairing build.
