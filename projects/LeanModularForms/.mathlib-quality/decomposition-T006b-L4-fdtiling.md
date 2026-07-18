# Decomposition (source-verified, ADVERSARIAL) — T006-b-L4: the bad-prime FD-tiling

*`/develop --decompose`, 2026-06-21. Sources read directly: Diamond–Shurman (`/tmp/ds.txt`).
Investigation agent a955a8e6 (read-only, Lean-grounded) + my independent verification of the
generic FD engines + adversarial spot-check of every load-bearing reuse claim.*

## Executive verdict — **BOUNDED, not research-scale (the "wall" is overturned)**

> **The bad-prime fundamental-domain tiling `hFD` (`⋃_{b<p} [1,b;0,p]•Γ₁-FD` is a fundamental
> domain for `Gamma_p_α(diag(1,p)) = Γ₁(N)∩Γ⁰(p)`, `p∣N`) is a BOUNDED ~350–500 LOC development
> against the codebase's EXISTING generic engines — NOT a multi-week from-scratch construction.**

The source-faithfulness hypothesis is **CONFIRMED**: DS Lemma 5.5.1 is generic (`ds.txt:14380`:
"Let Γ ⊂ SL₂(Z) be a congruence subgroup, and let α ∈ GL₂⁺(Q)" — no coprimality), but the codebase
built the coprime FD-tiling via a coprime-SPECIFIC route (M_∞ + Bézout, the bulk of
`DeltaBSystem.lean`'s 1524 lines). The bad-prime case is **strictly simpler** than the coprime
case it mirrors — it **deletes** the M_∞ tile, the Bézout/`gcdA` surjectivity, and the
`Option (Fin p)` branch — because the obstruction DS flags for `p∤N` is **vacuous when `p∣N`**.
The prior `AdjointTheoryBadPrime.lean:194` / `tickets.md` "research-scale WALL" framing conflated
"no ready-made bad-prime lemma" with "genuinely hard", and predated recognizing the generic engines.

## The α reconciliation
`U_p = [Γ₁(N) diag(1,p) Γ₁(N)]`, reps `β_b = T_p_upper(b) = [1,b;0,p]`, `b=0..p−1` — DS §5.2
(`ds.txt:13631`): "βⱼ for 0≤j<p, **excluding β∞ when p|N**" ⟹ **exactly p cosets** (vs p+1 coprime).
`hFD` is at `α=diag(1,p)`; **Lean-verified** `diag(1,p)·[a,b;Nc,d]·diag(1,p)⁻¹ = [a,b/p;pNc,d]` ⟹
integral ⟺ `p∣b` ⟺ `Γ⁰(p)`, so `Gamma_p_α(diag(1,p)) = Γ₁(N)∩Γ⁰(p)` = DS `Γ₁⁰(N,p)`
(`ds.txt:13222`). The lower-left `pNc ≡ 0 (mod N)` is **automatic** — no coprimality.

## Decomposition tree (mirrors DS Lemma 5.5.1 generic proof)

| Leaf | Content | Status | Verified |
|---|---|---|---|
| **L1** | generic FD engines (`iUnion_smul_of_transversal` PeterssonLevelN:289; `smul_of_eq_conjAct` :322; `Gamma_p_α_FD_finite_index_decomp` FDTransport:132; `Gamma_p_α_fundDomain_PSL` :198) | **DISCHARGED** | ✓ I read :289 (generic arbitrary-transversal); spot-checked `Gamma_p_α_FD_finite_index_decomp (α : GL ℚ)` — **α-generic, no Coprime** |
| **L2** | `Gamma_p_α(diag(1,p)) = Γ₁(N)∩Γ⁰(p)` | **PROVE ~60 L** (easier than coprime; no coprimality — lower-left auto) | mirror `Gamma_p_α_T_p_lower_eq_inf` FDTransport:1389 |
| **L3** ★ | `[Γ₁(N) : Γ₁(N)∩Γ⁰(p)] = p` for `p∣N` | **PROVE ~120 L** (the hardest; coprime Bézout route inapplicable, replaced by direct proof) | distinctness reuses `T_p_lower_tile_some_some_notMem_Gamma_up` (DeltaBSystem:841 — spot-checked **`(p)(hp:Prime p){b₁ b₂:Fin p}`, NO Coprime** ✓); covering = "`a` is a unit mod p" (DS `ds.txt:13247`: bad `p∣a` case **vacuous**) |
| **L4** | `Fin p` transversal bijective (no `Option`/M_∞ branch) | **PROVE ~80 L** | mirror `T_p_lower_tile_transversal_bijective` DeltaBSystem:953, simplified |
| **L5** | det-p→det-1 conjugation `diag•(⋃β_b•FD)=⋃[1,b;0,1]•FD` | **PROVE ~50 L** | mirror `T_p_lower_smul_Hecke_FD_eq_iUnion_tile` DeltaBSystem:331; 2-step conj template = `isFundamentalDomain_Hecke_tiles_Gamma_p_α` DeltaBSystem:1094 |
| **L6** | AE-disjointness of p tiles | **DISCHARGED** | `aedisjoint_glMap_T_p_upper_pair` SummandAdjoint:402 — spot-checked **`(hp:0<p)`, NO Coprime** ✓ (already used @ AdjointTheoryBadPrime:134) |
| **L7** | 5.5.2(a) per-summand change-of-vars | **DISCHARGED** | `peterssonInner_slash_adjoint` AdjointTheory:399 (generic α) |
| **L8** | fiber-count `hcp` reconciliation | **DISCHARGED** (pattern) | `slToPslQuot_fiberCard` automatic N≥3; `center_le_Gamma_up` coprimality-free |

**Assembly**: L1–L8 → `isFundamentalDomain_BadHecke_tiles` via the 2-step conj template (det-1 engine
on `⋃[1,b;0,1]•FD`, then `smul_of_eq_conjAct` back) → discharges `hFD` in `petN_doubleCoset_adjoint`
→ closes `petN_badUp_eq_petN_badUpAdjoint` (T006-b-L4) → closes T006-b → unblocks T003.

## Source quotes (DS, line-located)
- **5.5.1 generic** (`ds.txt:14380`): "Let Γ ⊂ SL₂(Z) be a congruence subgroup, and let α ∈ GL₂⁺(Q)."
- **βⱼ, p cosets for p|N** (`ds.txt:13631`): "βⱼ for 0≤j<p, excluding β∞ when p|N."
- **Γ₁⁰(N,p)** (`ds.txt:13222`): "Γ₃ = Γ₁⁰(N,p) = Γ₁(N) ∩ Γ⁰(p) … additional condition b ≡ 0 (mod p)."
- **vacuous bad obstruction** (`ds.txt:13247`): "if p|a then b−ja can't be 0 (mod p) for any j … Instances of γ₂ with p|a occur if and only if p∤N … Thus γ₂,0,…,γ₂,p−1 are a complete set of coset representatives when p|N."
- **Lemma 5.1.2** (`ds.txt:12833`): coset ↔ double-coset-orbit correspondence (the βⱼ engine).

## Adversarial attacks (all SURVIVED)
1. *"engines need det-1 reps; βⱼ have det p"* → defused by the 2-step conj (L5): conjugate to det-1 tiles `[1,b;0,1]`, apply det-1 engine, conjugate back. Template `isFundamentalDomain_Hecke_tiles_Gamma_p_α` DeltaBSystem:1094 does exactly this for coprime. SURVIVES.
2. *"non-coprime breaks the index"* → REAL but FAVORABLE: p+1→p (drop M_∞), and DS's own proof (`ds.txt:13247`) shows the bad case is the *clean* one. SURVIVES.
3. *"−I/PSL fiber breaks"* → `center SL₂ℤ = ±I ⊆ Γ⁰(p)` (scalars have 0 upper-right); `center_le_Gamma_up` already coprimality-free. SURVIVES.
4. *"petN is FD-defined so the tiling is unavoidable"* → TRUE (it's why `hFD` exists) but it reduces to L1–L8, all bounded. SURVIVES.
5. *"a group-theoretic petN-coset assembly might bypass the FD entirely"* → possible alternative (DS 5.5.2(b) is group-theoretic, `ds.txt:14482`); would only make the verdict *more* favorable.

## Feasibility
Every leaf is DISCHARGED-by-existing (L1,L6,L7,L8 — all spot-checked coprimality-free/α-generic) or a
BOUNDED prove-leaf (L2–L5, ~310 L total) mirroring a coprime sibling **with the M_∞/Bézout apparatus
deleted**. The hardest, L3 (index=p), has both halves Lean-verified (distinctness reuses an existing
coprimality-free lemma; covering is the trivial "unit mod p"). **Total ~350–500 LOC vs the 1524-line
coprime `DeltaBSystem` it mirrors.** This is an *instantiate-and-specialize* exercise enabled by the
generic engines — a bounded `/beastmode` ticket board, NOT a multi-week research project.

## Next step
Run `/develop` (full) to create the L2–L5 ticket board (each ~50–120 LOC, with the coprime sibling
named as the template-to-simplify), then `/beastmode`. Closing it finishes T006-b → `Newform.isFullEigenform`
fully axiom-clean → unblocks T003. (T002 / Eichler–Shimura remains the *other* deep block for T004/T005.)
