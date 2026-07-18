# Decomposition (source-verified) — T006-b: `U_p` preserves `cuspFormsNewExtended`

*`/develop` (resume, plan T006-b), 2026-06-20. Source read directly: Diamond–Shurman §5.5–5.6
(`/tmp/ds.txt`). This REPLANS T006-b along **DS's actual proof of Prop 5.6.2 (the Fricke route)**,
replacing the background agent's invented `Γ⁰(p)`-fundamental-domain-tiling route (a dead-end that
hit "infrastructure absent from mathlib"). The agent's sorry-free `petN → aggregate-integral`
reduction in `AdjointTheoryBadPrime.lean` is correct but becomes UNUSED on the Fricke route.*

## Headline

> **DS Prop 5.6.2 proves `S_k^new` is `T_n`-stable (all `n`) NOT by tiling, but via the Fricke
> involution `w_N = [0,−1;N,0]`**: `new = (old)^⊥`, so `T_n(new) ⊆ new ⟺ T_n*(old) ⊆ old`; for bad
> `n` the adjoint is `T_n* = w_N T_n w_N⁻¹` (Ex 5.5.1), so it suffices that **`w_N` and every `T_n`
> preserve `old`**. The codebase already has `frickeOperator` (= `w_N` on `M_k(Γ₁N)`) and the generic
> per-summand change-of-variables `peterssonInner_slash_adjoint` (= DS Prop 5.5.2(a)). The one deep
> leaf is **DS Prop 5.5.2(b)** — the *generic* double-coset Petersson adjoint — which the codebase
> currently has only in its coprime specialization (`heckeT_n_adjoint`).

## Source proof (DS, read with locators)

### Prop 5.6.2 — the top-level result (`ds.txt:14688`, proof `:14689–14781`)
> "Proposition 5.6.2. The subspaces `S_k(Γ₁(N))^old` and `S_k(Γ₁(N))^new` are stable under the Hecke
> operators `T_n` and `⟨n⟩` for all `n ∈ Z⁺`."

Proof structure (verbatim landmarks):
- `:14738` "The two diagrams combine to show that `S_k(Γ₁(N))^old` is stable under all `T_n` and `⟨n⟩`"
  (Ex 5.6.3(a)(b)(c), the degeneracy-map `i_p` commuting diagrams). → **L3**.
- `:14739` "To establish the result for `S_k(Γ₁(N))^new` it is enough to show that `S_k(Γ₁(N))^old`
  is stable under the adjoints of `T_n` and `⟨n⟩` for all `n`" (Ex 5.6.3(d)). → **L5**.
- `:14740` "Since `T_n* = ⟨n⟩⁻¹ T_n` and `⟨n⟩* = ⟨n⟩⁻¹` when `(n,N)=1` … the result is clear in these
  cases. But discussing `T_n*` when `(n,N) > 1` requires Exercise 5.5.1: **`T_n* = w T_n w⁻¹`** where
  `w = [−N,0;1,0]_k`." → **L4**.
- `:14747` "Thus it suffices to show that the oldforms are preserved under the injective linear map
  `w`." (Ex 5.6.3(e), the `w`-vs-`i_p` commuting diagram). → **L2**.

### Ex 5.5.1 — the Fricke-conjugation adjoint (`ds.txt:14599–14637`)
> "(a) Let `γ = [0,−1;N,0]`. Establish the normalization formula `γ⁻¹[a,b;Nc,d]γ = [d,−c;−Nb,a]`.
> Use this to show that `γ⁻¹Γ₁(N)γ = Γ₁(N)`, and so the operator `w_N = [γ]_k` is the double coset
> operator `[Γ₁(N)γΓ₁(N)]_k` on `S_k(Γ₁(N))`. Show that `w_N ⟨n⟩ w_N⁻¹ = ⟨n⟩*` for all `n` with
> `(n,N)=1` and thus for all `n`.
> (b) Let `Γ₁(N)[1,0;0,p]Γ₁(N) = ⊔ Γ₁(N)β_j`, i.e. `T_p = Σ[β_j]_k`. From part (a), `γΓ₁(N) =
> Γ₁(N)γ` … Use this and the formula `[p,0;0,1] = γ⁻¹[1,0;0,p]γ` to find coset representatives for
> `Γ₁(N)[p,0;0,1]Γ₁(N)`. Use Proposition 5.5.2 and the coset representatives to show that
> `T_p* = w_N T_p w_N⁻¹`, and so `T_n* = w_N T_n w_N⁻¹` for all `n`.
> (c) Show that `w_N* = (−1)^k w_N` and that `iᵏ w_N T_n` is self-adjoint."

### Prop 5.5.2 — the generic double-coset Petersson adjoint (`ds.txt:14446–14512`)
> "Proposition 5.5.2. Let `Γ ⊂ SL₂(Z)` be a congruence subgroup, and let `α ∈ GL₂⁺(Q)`. Set
> `α' = det(α)α⁻¹`. Then (a) If `α⁻¹Γα ⊂ SL₂(Z)` then for all `f ∈ S_k(Γ)` and `g ∈ S_k(α⁻¹Γα)`,
> `⟨f[α]_k, g⟩_{α⁻¹Γα} = ⟨f, g[α']_k⟩_Γ`. (b) For all `f, g ∈ S_k(Γ)`, `⟨f[ΓαΓ]_k, g⟩ =
> ⟨f, g[Γα'Γ]_k⟩`. In particular … `[ΓαΓ]*_k = [Γα'Γ]_k`."

Prop 5.5.2(a) proof (`:14458–14480`) is exactly a single GL₂⁺ change-of-variables — the cocycle
identity `j(αα',τ) = j(α,α'τ)j(α',τ)` + `Im(α'τ) = det(α')Im(τ)|j(α',τ)|⁻²`. **This is the codebase's
`peterssonInner_slash_adjoint`.** Prop 5.5.2(b) proof (`:14482–14512`) assembles (a) over the βj
coset reps via Lemma 5.5.1(c) (`Γαγ_j ∩ γ̃_j αΓ ≠ ∅`).

## Decomposition tree

```
T006-b  heckeT_n_cusp_preserves_cuspFormsNewExtended_bad  (p ∣ N)
  │   [DS Prop 5.6.2]: T_p(new) ⊆ new  ⟺  ∀ g ∈ oldExt, petN(U_p f, g) = 0 = petN(f, U_p* g),
  │   and U_p* g = w (U_p (w⁻¹ g)) ∈ oldExt by L2+L3, so petN(f, U_p* g)=0 since f ⊥ oldExt.
  │
  ├─ L1  frickeOperatorCusp : Module.End ℂ (CuspForm (Γ₁N) k)   [cusp version of frickeOperator]
  │       → leaf (API; frickeOperator EXISTS at Fricke.lean:262, + cusp-preservation)
  │
  ├─ L2  frickeOperatorCusp preserves cuspFormsOldExtended      [DS Ex 5.6.3(e)]
  │       → sub-tree: the w/i_p commuting diagram `w_N ∘ i_d = (scalar) i_{?} ∘ w_{N/d}`
  │
  ├─ L3  heckeT_n_cusp preserves cuspFormsOldExtended, ALL n     [DS Ex 5.6.3(c)]
  │       → sub-tree: bad-prime + Extended version of heckeT_n_preserves_cuspFormsOld
  │         (codebase has the coprime, non-extended version at LevelRaiseComm.lean:614)
  │
  ├─ L4  U_p* = w_N U_p w_N⁻¹  (petN-adjoint, bad p)            [DS Ex 5.5.1(b) + Prop 5.5.2(b)]  ★ DEEP LEAF ★
  │       ⟸ L4.1  Prop 5.5.2(b): generic [ΓαΓ]* = [Γα'Γ]      (API GAP — sub-development)
  │       │        ⟸ L4.2  Prop 5.5.2(a) per-summand = peterssonInner_slash_adjoint  (EXISTS ✓ AdjointTheory.lean:399)
  │       │        ⟸ L4.3  Lemma 5.5.1(a,b,c): double-coset βj reps  (group theory + petN coset assembly)
  │       └─ L4.4  the algebraic conjugation [Γ diag(p,1) Γ] = w_N [Γ diag(1,p) Γ] w_N⁻¹
  │                 (Fricke.lean has pieces: frickeGL_mul_adj_lunipRep_mul_frickeGL_inv :95, the Ψ=U_p bridge)
  │
  └─ L5  abstract: T preserves oldExt^⊥ = newExt ⟺ T* preserves oldExt   [DS Ex 5.6.3(d)]
          → leaf (mathlib: orthogonal-complement of an operator-stable subspace under the adjoint;
            uses petN_innerProductCore @ AdjointTheoryPetersson.lean:427 + LinearMap.adjoint on finite-dim)
```

## Per-leaf source + discharge (Step 3/4)

- **L1** `frickeOperatorCusp` — API. Discharge: `frickeOperator` (Fricke.lean:262, ℂ-linear endo of
  `M_k(Γ₁N)`) + `frickeOperator` preserves cuspidality (cusp forms → cusp forms; the `frickeGL`
  normalizes Γ₁N so the cusp condition transports — same pattern as `heckeT_n_cusp` from `heckeT_n`).
  Verified exists: `frickeOperator`, `frickeOperator_coe`, `frickeOperator_frickeOperator` (W²=scalar).
- **L2** `frickeOperatorCusp` preserves `cuspFormsOldExtended`. Source: DS Ex 5.6.3(e), `ds.txt:14747`
  + the diagram `:14748–14781` ("the oldforms are preserved under the injective linear map `w`",
  via `w ∘ i_p = [0,p^{k-2}w; w,0]`-style intertwining of degeneracy maps between levels `N` and
  `N/p`). `span_induction` over the `cuspFormsOldExtended` generators (level-raise + level-inclusion);
  on a generator `i_d(h)`, `w_N(i_d h) = (scalar)·i_{d'}(w_{N/d} h)` is again old.
- **L3** `heckeT_n_cusp` preserves `cuspFormsOldExtended`, all `n`. Source: DS Ex 5.6.3(c),
  `ds.txt:14738`. Codebase: `heckeT_n_preserves_cuspFormsOld` (LevelRaiseComm.lean:614) is the
  coprime, non-extended version; extend to bad primes (the `[T,0;0,T]` + `[T_p, −p^{k−1}⟨p⟩; …]`
  diagrams `:14690–14737`) and to `cuspFormsOldExtended`.
- **L4** ★ `U_p* = w_N U_p w_N⁻¹`. Source: DS Ex 5.5.1(b), `ds.txt:14599`. THE deep analytic leaf.
  - **L4.2** Prop 5.5.2(a) = `peterssonInner_slash_adjoint` — **VERIFIED EXISTS** (AdjointTheory.lean:399,
    generic `α`, `0 < det α`, no coprimality). This is the entire analytic content of one summand.
  - **L4.1/L4.3** Prop 5.5.2(b) assembly over βj reps (Lemma 5.5.1) — API GAP, classical (~1.5 source
    pages `:14380–14512`), reusable (generic double-coset adjoint, not U_p-specific).
  - **L4.4** algebraic conjugation — Fricke.lean:95 `frickeGL_mul_adj_lunipRep_mul_frickeGL_inv`
    (machine-verified matrix identity) is exactly this for the bad rep; + the in-progress Ψ work (task #13).
- **L5** new = old^⊥ stable ⟺ adjoint stable. Source: DS Ex 5.6.3(d), `ds.txt:14739`. Discharge:
  `petN_innerProductCore` (AdjointTheoryPetersson.lean:427) gives the finite-dim `InnerProductSpace`;
  `LinearMap.adjoint` + `Submodule.orthogonal` API (an operator preserves `Wᗮ` iff its adjoint
  preserves `W`, on a finite-dim inner product space).

## Feasibility

The decomposition bottoms out cleanly: **L1, L5 are near-leaves** (existing `frickeOperator` /
mathlib `LinearMap.adjoint` + orthogonal-complement API); **L2, L3 are classical level-raising
commuting-diagram arguments** (the codebase has the coprime/non-extended templates); **L4.2 EXISTS**
(`peterssonInner_slash_adjoint`); **L4.4** is largely in `Fricke.lean`. The genuine remaining
development is **L4.1/L4.3 = DS Prop 5.5.2(b)**, the generic double-coset Petersson adjoint — a
~1.5-page classical proof, reusable (it also re-derives the coprime `heckeT_n_adjoint`), grounded in
the existing per-summand `peterssonInner_slash_adjoint`. This is materially more tractable and more
reusable than the agent's `Γ⁰(p)`-FD-tiling route, and it is **the route DS actually uses**. Net: a
focused multi-ticket sub-development whose deep core (Prop 5.5.2(b)) is bounded and well-templated,
not the open-ended tiling/measure morass.

## Attacks attempted (adversarial)

- *Is the Fricke route actually DS's proof, or invented?* Quote `ds.txt:14741` names Ex 5.5.1
  `T_n* = w T_n w⁻¹` explicitly and `:14747` "suffices to show oldforms preserved under `w`".
  **SURVIVES** — transcribed, not invented.
- *Does L4 secretly need the same tiling the agent hit?* Prop 5.5.2(b)'s proof (`:14482–14512`) uses
  Lemma 5.5.1(c)'s βj double-coset reps + Prop 5.5.2(a) per summand — NOT fundamental-domain tiling.
  The per-summand step is `peterssonInner_slash_adjoint` (EXISTS). **SURVIVES** (different, lighter
  machinery; the βj assembly is group-theoretic, not measure-theoretic FD tiling).
- *Is `frickeOperator` really `w_N` and on the right space?* Fricke.lean:262 docstring + `frickeGL`
  det N + normalizes Γ₁N (`frickeConjSL_mem_Gamma1`). **SURVIVES.**
- *Could L4.1 (generic Prop 5.5.2(b)) be false / need coprimality?* DS states it for ANY `α ∈ GL₂⁺(Q)`,
  no coprimality (`:14446`). The coprime hypothesis only enters the *consumer* (when one further
  simplifies `T_n* = ⟨n⟩⁻¹T_n`); the adjoint identity itself is general. **SURVIVES.**
- *Does L5 (orthogonal-complement) need finite-dimensionality?* Yes — `S_k(Γ₁N)` is finite-dim
  (`cuspForm_finiteDimensional`, Basic.lean:231) and `petN` is a definite inner product
  (`petN_definite`). Both present. **SURVIVES.**
