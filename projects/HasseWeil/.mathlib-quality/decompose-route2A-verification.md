# `/develop --decompose` — VERIFICATION pass on Route 2A' (vs the in-repo PDF, word-for-word). 2026-05-31

Re-read this session to verify (NOT memory): III.5 Cor 5.3–5.6 (PDF 96–98 = book 78–80), III.8 Prop
8.1d/8.2 (PDF 114–115 = book 96–97), Prop 8.6 (PDF 117 = book 99), Cor 8.1.1 (PDF 114 = book 96).

## Load-bearing claims — each VERIFIED verbatim

| Claim (Route 2A') | Silverman, verbatim | Verdict |
|---|---|---|
| **rπ−s separable ⟺ p∤s** (LINCHPIN) | **Cor 5.5** (p.79): *"m+nφ is separable iff p∤m. In particular 1−φ is separable."* For rπ−s=(−s)+rφ: m=−s ⟹ p∤s. | ✓ exact |
| `[ℓ]` separable for ℓ≠p | **Cor 5.4** (p.79): *"m≠0 in K ⟹ [m] is a finite separable endomorphism."* | ✓ exact |
| adjoint needs the σ-bridge | **Prop 8.2** (p.97): *"h satisfying φ*((T))−φ*((O))=(φ̂T)−(O)+div(h). Such an h exists because (III.6.1ab) tells us φ̂T is precisely the sum of the points of the divisor on the LHS."* | ✓ exact (my finding confirmed) |
| det=deg via the adjoint | **Prop 8.6** (p.99): `e(φv₁,φv₂)` step cited *"III.8.3 and III.6.2f"* (the adjoint + φ̂̂=φ); `tr(A)=1+det(A)−det(1−A)`. | ✓ exact |
| Galois: e(πS,πT)=e(S,T)^q | **Prop 8.1d** (p.96): `e_m(S^σ,T^σ)=e_m(S,T)^σ`. With π=σ on points (V.1.1: φ(P)=P^σ for E/F_q) and σ(ζ)=ζ^q on μ_ℓ. | ✓ exact |
| e(v₁,v₂) primitive for a basis | **Cor 8.1.1** (p.96) + nondegeneracy on the 2-dim E[ℓ]: e(v₁,v₂)≠1 ⟹ order ℓ. | ✓ |

## Deeper attack the verification unlocked — the σ-bridge is FREE via picDual

**Attack:** is Leaf 2 (the separable adjoint) really tractable, given the project's `isogDual` ≠ the
Pic⁰ dual?

**Finding (favourable):** the project's **`picDual = κ⁻¹∘classMap∘κ = σ∘φ*∘κ`** is *by construction* the
Pic⁰ dual, so the σ-bridge `φ̂T = σ(φ*((T)−(O)))` that Prop 8.2 needs is **automatic** (it is picDual's
definition). Hence Prop 8.2's "h exists" step is **free** (the h-divisor has degree 0 and σ=0 by
definition, so principal by Abel). And `picDual∘φ=[deg φ]` is **shipped** (`picDual_comp_toAddMonoidHom`),
the relation Prop 8.6 needs. The retracted `degree-blind` B2 was the **comap** (point action); `classMap`
(ideal extension) carries `e_φ=deg_i`, the FULL degree — so `picDual` is *not* degree-blind. So with
`β̂ = picDual`, Leaf 2's σ-bridge and `β̂β=[deg]` are both in hand.

**But the separable restriction is STILL essential** (attack survives): Prop 8.2 uses the **divisor
pullback `φ*((T)) = Σ_{φP=T} e_φ(P)(P)`** as a genuine divisor (to form `h` and `f∘φ`). For
**inseparable** φ this is the **inseparable** pullback (`e_φ=deg_i>1`) — the Route-1 obstruction. For
**separable** β (`p∤s`), it is **multiplicity-free** (`e=1`), the étale fibre sum `Σ_{βP=T}(P)`,
recoverable from `σ∘classMap` (or the kernel coset). So Leaf 2 = Prop 8.2 for separable β = the **mult-1
étale pullback + the (free) σ-bridge + the function manipulation + Abel** — bounded, the genuine core.
The inseparable case is correctly **avoided** by the discriminant argument (Route 2A').

**Prop 8.6 restructured** (verified safe): use the adjoint for **φ itself** (separable β), not φ̂:
`e(βv₁,βv₂) = e(v₁, β̂βv₂) = e(v₁,[deg β]v₂) = e(v₁,v₂)^{deg β}`. This avoids the (possibly inseparable)
β̂ as a *map* — β̂ enters only as the point `β̂T = picDual(T)`. ✓ Mult-free.

## Residual real dependencies (BUILD work, not flaws)
1. **Leaf 1** — Weil pairing construction (Prop 8.1 a–d) on E[ℓ]; the one new infra is **function
   evaluation** `g(X+S)/g(X)` (+ translates, `∘[ℓ]`, II.2.3 constancy).
2. **Leaf 2** — Prop 8.2 for separable β: the **mult-1 étale pullback** + picDual (σ-bridge free) +
   `picDual∘β=[deg β]` (shipped) + Abel + the pairing manipulation.
3. **TORSION** — `#E[ℓ]=ℓ²` via `[ℓ]` separable (Cor 5.4) + `#ker=deg` for separable (III.4.10c;
   witness-parametric in project — needs the étale `#fibre=deg_s`).
4. **AG-SEP** — `[ℓ]` separable via the differential (Cor 5.4); the SAME route the project used for
   `1−π` (Leaf 2). Verify it is sorry-free (vs `OmegaPullbackCoeff` T-IV-BRIDGE-001).
5. **Discriminant lemma** — `Q≥0 on {p∤s} ⟹ t²≤4q ⟹ qf_nonneg` (elementary; p-coprime-denominator witness).

## CODE verification (vs the actual repo, NOT memory) — corrects two "shipped" claims I had wrong

The user's "don't rely on memory" caught real inaccuracies in my project-state assumptions:

- **`picDual` IS sorry-free** (`PicDual.lean`/`IsogenyClassGroup.lean`: 0 sorries) and **is**
  `κ⁻¹∘classMap∘κ = σ∘φ*∘κ` (`picDual = classTransport (classMap …)`, line 113–116). ✓ So the
  σ-bridge as a *definition* is genuine.
- **BUT `α∘α̂=[deg α]` is NOT unconditionally shipped.** `toAddMonoidHom_comp_picDual` (line 565)
  **carries `hnat : α.Naturality` as a hypothesis** (the III.3.4 κ-naturality). It is *reduced*
  (line 339) to the **point-map ↔ comap agreement** — dischargeable for a *geometric* isogeny via
  the shipped `toClass_toPointMap`, but a **real obligation**, not free.
- **`α̂∘α=[deg α]` (the order Prop 8.6 actually needs: `e(βv₁,βv₂)=e(v₁,β̂βv₂)`)** needs `hnat` **AND**
  **`hother`** — the *reverse-order* class identity `classMap∘classNorm=(·)^n` (`= map∘relNorm=(·)^n`),
  which the file flags as a **genuine separate Silverman III.6.2(a) ingredient / mathlib gap** (line
  605–613). The file also notes Silverman derives `α̂∘α` from `α∘α̂` by **right-cancelling the
  nonconstant α** (line 615–624) — so `hother` is likely dischargeable via cancellation, but it is a
  real step.
- **`isogDual` (the genuine dual) is NOT sorry-free:** `DualIsogeny.lean:142` `exists_dual := sorry`
  ("gated on ~2000 lines"); `isogDual` (185) is built on it. ⇒ **Use `picDual`, NOT `isogDual`**, to
  avoid that sorry. `picDual` is sorry-free modulo `hnat`/`hother`.

**Net correction to Leaf 2's cost:** my memory-claim "the σ-bridge + `β̂β=[deg]` are free via picDual"
was **rosy**. Reality: `picDual` and the σ-bridge-by-definition are genuine, but `β̂β=[deg β]` (the
relation Prop 8.6 needs) is **parametric on `hnat` (dischargeable via `toClass_toPointMap`) + `hother`
(the reverse-order class identity, dischargeable via α-cancellation)**. Both are real obligations to
land, on top of the pairing adjoint construction. Leaf 2 is therefore **more dependency-laden than
memory suggested** — but still bounded and not blocked (no inseparable σ-bridge; mult-free).

**New Leaf-2 dependency list (code-verified):** Weil-pairing adjoint Prop 8.2 (separable, mult-1
pullback) + `picDual` (shipped) + `hnat` (κ-naturality, via `toClass_toPointMap`) + `hother`
(reverse-order class identity, via α-cancellation) + `picPushforward_comp_picDual` (shipped,
unconditional). `isogDual` avoided.

## PASS 6 — targeted code verification of the Leaf-2 obligations (`hnat`, `hother`)

Good news + a sharper core. Verified against the repo (not memory):

- **`hother` is NOT a mathlib gap — it is already REPLACED by surjectivity + cancellation, sorry-free.**
  `PicDual.lean:676` `picDual_comp_toAddMonoidHom_of_surjective` derives `α̂∘α=[deg]` from
  `α∘α̂=[deg]` (`hnat`) by **right-cancelling the nonconstant `α̂`** (Silverman III.6.2(a)), using
  `hsurj : Surjective (picDual)` — **automatic over K̄** (III.4.10a). The cancellation lemmas
  (`comp_eq_mulByInt_of_comp_eq_of_surjective`, `eq_of_comp_eq_of_surjective`, lines 638/660) are
  **sorry-free, ~10-line proofs**. So my prior "reverse-order class identity = mathlib gap" worry was
  itself imprecise — the project already routes around it.
- **`hnat` is dischargeable sorry-free.** `ToClassFunctorial.lean` has **0 sorries**; its
  `toClass_toPointMap` (line 156) supplies the point-map ↔ comap agreement that `hnat`/`Naturality`
  reduces to, for any isogeny whose point map is the geometric `toPointMap` (ours are).
- `classNorm_comp_classMap` (= `relNorm∘map=(·)^finrank`, forward order) shipped via
  `ClassGroup.relNorm_comp_map` (`ClassGroupNorm.lean:923`), axiom-clean.

⇒ **Leaf-2 dual relations `β̂β=[deg β]` discharge cleanly over K̄** (via `hnat` + automatic surjectivity
+ the sorry-free cancellation), modulo the `finrank=degree` tower bridge (plumbing). **`isogDual`
avoided.** The previous-pass pessimism is corrected: this is NOT a blocker.

## PASS 6 — but the genuine remaining CORE is now pinned: the mult-1 geometric divisor pullback

**Attack on Leaf 2's Prop 8.2 construction:** it needs the **divisor** `β*((T)) = Σ_{βP=T}(P)` (to form
`h` with `div h = β*((T))−β*((O))−(β̂T)+(O)`) — not just its `σ`. The project ships `classMap` (ideal
level) and `picpushforward`, but **no geometric divisor pullback** `β*` (RouteCAddFormula's own note).
For **separable** β this pullback is **multiplicity-free** (étale fibre, `e=1`), so it is the *easy*
regime — but it is **genuinely new infrastructure, not shipped.**

**The same mult-1 pullback is needed by Leaf 1** (`div g = [ℓ]*((T))−[ℓ]*((O)) = Σ_{R∈E[ℓ]}(T'+R)−…`).
So the **central new piece is the multiplicity-free geometric divisor pullback** `β*((T))=Σ_{βP=T}(P)`
(separable/étale), used by both the pairing construction (Leaf 1) and the separable adjoint (Leaf 2).
It is the *same object Route 1 lacked* — but now confined to the **mult-free** case (no inseparable
exponents). Bounded, but a real build (étale fibre sum from the kernel coset + `σ∘classMap` agreement).

## Verdict
Route 2A' is **verified verbatim against the PDF** and survives the verification pass. Every
load-bearing claim is exact. The σ-bridge — the thing that made the naive Route 2 look comparable to
Route 1 — is **free** in the separable case via the shipped `picDual` (definition). The genuine remaining
work is the Weil-pairing construction (Leaf 1, incl. evaluation infra) and the separable adjoint (Leaf 2,
mult-1) — both bounded, textbook III.8. **No flaws found; the items above are tickets, not defects.**
The plan is solid.
