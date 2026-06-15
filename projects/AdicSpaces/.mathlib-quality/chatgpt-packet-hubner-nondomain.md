# ChatGPT Pro escalation packet: non-domain Laurent-pair separation

**Question.** Can we prove Laurent simple-cover separation at the `presheafValue` level for noetherian Tate rings (not necessarily domains), without invoking Cor 8.32 / Stacks 00MA / faithful flatness of `A → A⟨f⟩ × A⟨1/f⟩`?

Date: 2026-04-20. Project: Lean 4 formalization of Wedhorn's *Adic Spaces*.

## Context (1-paragraph)

Project: `/Users/mcu22seu/Documents/GitHub/Adic spaces`. Goal: close `ValuationSpectrum.tateAcyclicity` Part 1 (separation for rational covers, Wedhorn Thm 8.28(b)) without depending on Cor 8.32's faithful-flatness residual (Stacks 00MA). The **Hübner route** (Hübner arXiv 2405.06435 Lemma 3.8) reduces to simple-Laurent-cover separation. The simple-Laurent separation at algebraic level `LaurentCover.epsilonHom_gen_injective` uses Krull's intersection theorem in the **domain case only**. We need it for general noetherian Tate rings.

## Exact statement we want to prove

```lean
-- Location: Adic spaces/HubnerSeparation.lean:187 (currently `sorry`)
theorem laurentCover_separation_presheaf_viaRow3_noetherian
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ : RationalLocData A) [IsNoetherianRing (presheafValue D₀)]
    (f : A)
    (hf_nonunit : ¬IsUnit (D₀.canonicalMap f))
    (hplus : rationalOpen (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (hminus : rationalOpen (laurentMinusDatum D₀ f).T (laurentMinusDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (τ_plus : presheafValue (laurentPlusDatum D₀ f) ≃+*
      LaurentCover.B₁_gen (D₀.canonicalMap f))
    (τ_minus : presheafValue (laurentMinusDatum D₀ f) ≃+*
      LaurentCover.B₂_gen (D₀.canonicalMap f))
    (htau_plus : ∀ x : presheafValue D₀,
      τ_plus (restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x) =
        (LaurentCover.epsilonHom_gen (D₀.canonicalMap f) x).1)
    (htau_minus : ∀ x : presheafValue D₀,
      τ_minus (restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x) =
        (LaurentCover.epsilonHom_gen (D₀.canonicalMap f) x).2)
    (x : presheafValue D₀)
    (hplus0 : restrictionMap D₀ (laurentPlusDatum D₀ f) hplus x = 0)
    (hminus0 : restrictionMap D₀ (laurentMinusDatum D₀ f) hminus x = 0) :
    x = 0
```

Equivalent to proving, at `B := presheafValue D₀`:

```lean
-- Free-standing algebraic core, could be stated in LaurentCoverExact.lean:
theorem epsilonHom_gen_injective_noetherian_tate
    {B : Type*} [CommRing B] [TopologicalSpace B] [NonarchimedeanRing B]
    [T2Space B] [IsNoetherianRing B] [IsTateRing B]
    (g : B) (hg : ¬IsUnit g) :
    Function.Injective (LaurentCover.epsilonHom_gen g)
```

where `LaurentCover.epsilonHom_gen g : B →+* (B⟨X⟩/(g - X)) × (B⟨X⟩/(1 - g·X))` is the canonical diagonal.

## Mathematical proof sketch

Given `ε(a) = 0` for `a ∈ B` (where B is noetherian Tate Hausdorff, `g ∈ B` non-unit), show `a = 0`.

1. **Coefficient analysis from first projection**: `algebraMap a ∈ (g - X) · B⟨X⟩`, so writing the witness `c`, coefficient recurrence gives `a = g · coeff 0 c`, `coeff n c = g · coeff (n+1) c`, hence `a ∈ (g)^(n+1)` for all `n`. **Algebraic, no domain/topology needed.**
2. **General Krull's intersection theorem** (Mathlib `Ideal.mem_iInf_smul_pow_eq_bot_iff`): for noetherian `B`, `a ∈ ⋂_n (g)^n • ⊤ ↔ ∃ r ∈ (g), r • a = a`, i.e., `∃ c ∈ B, (1 - g·c) · a = 0`, hence `a = g·c · a`. **No domain needed.**
3. **Iteration**: `a = (g·c)^N · a = c^N · g^N · a` for all `N`.
4. **Coefficient convergence from second projection**: `algebraMap a ∈ (1 - g·X) · B⟨X⟩`, so writing the witness `c''`, coefficient analysis gives `coeff n c'' = g^n · a`. Since `c'' ∈ B⟨X⟩` (restricted power series), `MvPowerSeries.IsRestricted c''` says the coefficients tend to `0` in B's topology. Thus `g^n · a → 0` in B's topology.
5. **Topological conclusion**: The Tate topology on B has a 0-neighborhood basis consisting of **ideals** (specifically, powers of a pair-of-definition ideal `I`). From (4), `g^N · a ∈ I^k` for every `k` and `N` large enough. From (3), `a = c^N · g^N · a ∈ c^N · I^k ⊆ I^k` (since I^k is an ideal). Hence `a ∈ I^k` for every `k`. By `T2Space` + the basis `{I^k}`, `⋂_k I^k = {0}`, so `a = 0`.

## What makes this hard in Lean?

### Step 1 and 2: straightforward

- Step 1: The existing proof of `algebraMap_mem_span_fSubX_eq_zero` (LaurentCoverExact.lean:261) derives `a ∈ (f)^n` for all `n` **without using domain** — only the Krull step in domain is used. So we can reuse the coefficient-recurrence part and stop before Krull.
- Step 2 (general Krull): Mathlib's `Ideal.mem_iInf_smul_pow_eq_bot_iff` is available — requires `[IsNoetherianRing R]` + `[Module.Finite R M]`. For `M = R`, `Module.Finite R R` is automatic.

### Step 4: `IsRestricted ⟹ f^n · a → 0` in B's topology

`MvPowerSeries.IsRestricted c'' := Tendsto (fun s => coeff s c'') cofinite (nhds 0)` (RestrictedPowerSeries.lean:65). We need: `Tendsto (fun n => g^n · a) atTop (nhds 0)` follows from `∀ n, coeff (toIndex n) c'' = g^n · a`.

- In the univariate case, `coeff n c'' = g^n · a` is an equality of functions `ℕ → B`.
- `IsRestricted c''` gives `coeff s c'' → 0` along cofinite, which in the univariate case is the same as `coeff n c'' → 0` as `n → ∞` (since `Fin 1 →₀ ℕ ≃ ℕ`).
- Translation: need a lemma `coeff_atTop_of_IsRestricted` of the form: "if `c'' ∈ TateAlgebra B` then `∀ U ∈ nhds (0 : B), ∃ N, ∀ n ≥ N, coeff n c'' ∈ U`."

This should be a straightforward consequence of `IsRestricted` but might not have an off-the-shelf Mathlib/project lemma. **First explicit blocker.**

### Step 5: topological `a ∈ I^k` for every `k`

B = `presheafValue D₀` is a Tate ring. Its topology comes from the completion of `Localization.Away D₀.s` with the `locTopology` (from `LocalizationTopology.lean`). The topology has a nhd basis of 0 `{locNhd D₀.P D₀.T D₀.s k}_k`.

For the Hübner argument, we need:

- (a) A **sequence of ideals** `I_k ⊆ B` forming a 0-neighborhood basis.
- (b) `⋂_k I_k = {0}` (Hausdorffness).
- (c) For our convergent `g^N · a → 0`: `∀ k, ∃ N_k, ∀ N ≥ N_k, g^N · a ∈ I_k`.

For B = `presheafValue D₀`:
- `presheafValue_isAdic` in `PresheafTateStructure.lean:804` gives `IsAdic (presheafValue_idealOfDef D₀)` **on the ring-of-definition subring** `presheafValue_ringOfDef D₀`, not directly on `presheafValue D₀`.
- `presheafValue_ringOfDef D₀` is an OPEN subring of `presheafValue D₀`, with the subspace topology.
- The 0-neighborhood basis in `presheafValue D₀` can likely be derived from the adic basis in `presheafValue_ringOfDef D₀` via the openness, but this needs a bridging lemma.

**Second explicit blocker.** Need a lemma like:

```lean
theorem presheafValue_nhds_basis_as_ideals (D₀ : RationalLocData A) :
    ∃ (I : ℕ → Ideal (presheafValue D₀)),
      (nhds (0 : presheafValue D₀)).HasBasis (fun _ => True) (fun k => (I k : Set _)) ∧
      (∀ k, IsOpen ((I k : Set (presheafValue D₀)))) ∧
      (⨅ k, I k = ⊥)
```

Without this, the proof of step 5 cannot proceed in Lean even though it's trivially true mathematically.

### Step 3: `c^N · I^k ⊆ I^k` is standard

Trivial since `I^k` is an ideal. Lean: `Ideal.mul_mem_left (I^k) (c^N) _`.

## What's been tried / ruled out

- **Direct use of `epsilonHom_gen_injective` without `[IsDomain]`**: not possible; the proof at LaurentCoverExact.lean:307 explicitly uses `Ideal.iInf_pow_eq_bot_of_isDomain`.
- **Using only the first projection**: gives `a ∈ ⋂(f)^n`, but without domain, Krull only gives `a = fc · a`, which doesn't imply `a = 0` without further input (the second projection).
- **Using only the second projection**: `f^n · a → 0` in topology doesn't imply `a = 0` unless we have the first-projection condition `a = fc·a` for some fixed `c` (then iterate).
- **Noetherian + Hausdorff without both projections**: insufficient — need both to bootstrap.

## Repo primitives available

| Primitive | Location | Status |
|---|---|---|
| `LaurentCover.epsilonHom_gen` | `LaurentCoverExact.lean:231` | def, no sorry |
| `LaurentCover.epsilonHom_gen_injective` | `LaurentCoverExact.lean:315` | theorem, `[IsDomain]` req'd |
| `LaurentCover.algebraMap_mem_span_fSubX_eq_zero` | `LaurentCoverExact.lean:261` | theorem, uses Krull-domain |
| `MvPowerSeries.IsRestricted` | `RestrictedPowerSeries.lean:65` | def |
| `TateAlgebra` | `TateAlgebra.lean:75` | = `restrictedMvPowerSeriesSubring 1 A` |
| `Ideal.mem_iInf_smul_pow_eq_bot_iff` | Mathlib Filtration.lean:399 | general Krull (no domain) |
| `Ideal.iInf_pow_eq_bot_of_isDomain` | Mathlib Filtration.lean:474 | domain-only Krull |
| `presheafValue_isAdic` | `PresheafTateStructure.lean:804` | IsAdic on ringOfDef subring |
| `presheafValue_ringOfDef_isOpen` | `PresheafTateStructure.lean:84` | open subring |
| `TateAlgebra.flat_quotient_fSubX_general` | `TateAlgebra.lean:2591` | general flatness (no domain) |
| `TateAlgebra.flat_quotient_oneSubfX_general` | `TateAlgebra.lean:2601` | general flatness (no domain) |
| `TateAlgebra.mul_fSubX_regular` | `TateAlgebra.lean:946` | regularity, only noetherian |
| `TateAlgebra.mul_oneSubfX_regular` | `TateAlgebra.lean:976` | regularity, only noetherian |

## Question to ChatGPT Pro

**Can the proof I sketched above (algebraic steps 1-3 + topological steps 4-5) be closed in Lean without invoking Cor 8.32 / Stacks 00MA / faithful flatness?**

Specifically:

1. **Is there a Mathlib or project lemma** for "MvPowerSeries.IsRestricted + pointwise coefficient recurrence `coeff n c'' = g^n · a` ⟹ `g^n · a → 0` in B's topology"? Or is this just a direct consequence of `Tendsto ... cofinite ...` with a bit of unfolding?

2. **Is there a Mathlib or project lemma** giving a sequence-of-ideals 0-neighborhood basis for `presheafValue D₀` (or more generally for any Hausdorff Tate ring with a pair of definition)? This would formalize "Tate topology = I-adic for some ideal basis".

3. **Alternative non-domain proof strategies** — is there a cleaner argument that avoids the topology-vs-algebra gymnastics? E.g.:
   - A direct flatness argument: `B → B⟨X⟩/(g-X) × B⟨X⟩/(1-gX)` is **faithfully flat** for noetherian Tate `B` — perhaps provable via `tateAlgebra_flat P` + `flat_quotient_{f,oneSubf}X_general` + a direct 1-cocycle argument, without going through `row3_exact`?
   - A spectrum argument: `Spec(B⟨g⟩) ∪ Spec(B⟨1/g⟩) = Spec(B)` (surjective), combined with flatness, gives faithful flatness directly?
   - A mapping-cone / 2-term complex argument using the existing `Module.Flat` infrastructure?

4. **Is the Hübner route fundamentally equivalent to Cor 8.32** for non-domain Tate rings, or is there a genuinely simpler proof for the Laurent case that doesn't go through Stacks 00MA?

5. **Reference verification**: Does Hübner arXiv 2405.06435 Lemma 3.8 itself use faithful flatness, or does it prove Laurent-cover separation by algebraic means? If algebraic, what's the key lemma?

## Specific Lean signatures I'd accept

Any of:

- (A) A complete proof of `laurentCover_separation_presheaf_viaRow3_noetherian` (above).
- (B) A complete proof of `epsilonHom_gen_injective_noetherian_tate` (above).
- (C) A complete proof of a weaker form: e.g., assuming `B` is `IsAdicComplete` (which gives `I ≤ Jacobson ⊥`, so Krull ⟹ `⋂(g)^n = 0` only if `(g) ⊆ I`, which is NOT generally the case for arbitrary `g` — but it works if `g` is topologically nilpotent).
- (D) A clear argument that Hübner is EQUIVALENT to Cor 8.32 for non-domain Tate, so the route doesn't help; in that case, Cor 8.32 / Stacks 00MA must stay.
- (E) An alternative route (flatness + spectrum, or mapping cone) that avoids both Krull-domain and Cor 8.32.

## Downstream consequences

If H1-general (non-domain) is provable:
- **H2** (iterated Laurent separation) composes H1-general through the Wedhorn 8.34 induction (~100 lines).
- **H3** (final Part 1 wrapper) composes H2 with existing sorry-free infrastructure (`separation_of_finer_rational`, `refines_by_standard_cover_per_E`).
- **Result**: `tateAcyclicity` Part 1 closed without Cor 8.32.

If H1-general is NOT provable without Cor 8.32 / Stacks 00MA:
- The Hübner route **does not decouple** Part 1 from Cor 8.32.
- **Decision point**: accept domain-only Hübner for a restricted `tateAcyclicity_for_domains` theorem, OR keep pushing on Cor 8.32 / Stacks 00MA.
