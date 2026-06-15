# ChatGPT Pro escalation packet: `locIdeal ≤ Ideal.jacobson ⊥` is FALSE for uncompleted Tate localizations

**Question.** The unconditional statement `locIdeal D.P D.T D.s ≤ Ideal.jacobson (⊥ : Ideal (locSubring D.P D.T D.s))` — the open residual flagged in `AdicCompletionFaithfullyFlat.lean` — is **false in general for uncompleted Tate localization rings**. This packet documents the concrete counterexample and asks whether (a) the Jacobson path can be salvaged under additional hypotheses, or (b) Lane B's unconditional closure requires a different route to `coeRingHom_preserves_proper` not routed through `locIdeal ≤ Jac` in the incomplete ring.

Date: 2026-04-20. Project: Lean 4 formalization of Wedhorn's *Adic Spaces*.

## Context (1-paragraph)

Project: `/Users/mcu22seu/Documents/GitHub/Adic spaces`. We have landed a Mathlib-compatible generic Stacks 00MA (`AdicCompletion.faithfullyFlat_of_le_jacobson_bot`, sorry-free) and three Jacobson-conditional wrappers connecting it to `coeRingHom_preserves_proper` via the existing T-COMP-FF chain. The remaining residual is the unconditional Jacobson hypothesis `locIdeal ≤ Jac ⊥` in `locSubring`. This session audits the direct proof attempt; it fails, and I found a concrete counterexample showing the statement itself is false.

## Concrete counterexample

**Setup.**
- `A := ℚ_p⟨X⟩` (Tate algebra over ℚ_p = restricted power series convergent on `|X| ≤ 1`).
- `A₀ := ℤ_p⟨X⟩` (ring of power-bounded elements, an open subring of A).
- `P.I := (p) ⊆ A₀`. Then `(A₀, P.I)` is a valid pair of definition: `A₀` open, `I` f.g., subspace topology on `A₀` is `(p)`-adic.
- `p ∈ A` is topologically nilpotent (`p^n → 0` in the `(p)`-adic topology on A) and a unit (`1/p ∈ ℚ_p ⊆ A`). So `A` is Tate in the project's sense (`IsTateRing A` via Huber + top-nilp unit `p`).
- Rational data: `T := {X}`, `s := p`. The `hopen` condition holds: for any `b ∈ P.I^N = (p^N)` with `N ≥ 1`, `divByS b p = b/p = p^(N-1)·c ∈ A₀ ⊆ locSubring P T s`.
- `locSubring P T s = A₀[X/p] = ℤ_p⟨X⟩[X/p]` as a sub-algebra of `Localization.Away p = A[1/p] = A` (since `p` is already a unit in A).
- `locIdeal P T s = Ideal.map algebraMapD P.I = (p) · locSubring`.

**Claim 1: `X ∈ locIdeal`.**

`X = p · (X/p)` with `p ∈ P.I ⊆ A₀` (image via `algebraMapD` gives the generator of `locIdeal`) and `X/p ∈ locSubring` (by definition of `locSubring = A₀[X/p]`). Therefore `X ∈ (p) · locSubring = locIdeal`.

**Claim 2: `X` is topologically nilpotent in `locSubring`'s subspace topology.**

Direct from the project's
`ValuationSpectrum.locIdeal_forall_isTopologicallyNilpotent`
(`IdealLocalization.lean:339`, sorry-free): every element of `locIdeal` is top-nilp in the
induced subspace topology (which equals the `locIdeal`-adic topology by
`locSubring_isAdic`). Since `X ∈ locIdeal` from Claim 1, `X` is top-nilp.

**Claim 3: `1 + X` is NOT a unit in `locSubring`.**

Two independent arguments:

(i) The formal inverse `(1 + X)^{-1} = 1 - X + X² - X³ + …` has coefficients alternating `±1`, with p-adic absolute value `|±1|_p = 1` for all indices. These coefficients do NOT tend to `0` in the p-adic topology on ℚ_p. Therefore this series is **not a restricted power series**, so it is not in `ℚ_p⟨X⟩`.

(ii) `1 + X` has a zero at `X = -1 ∈ ℤ_p` (a valid point in the closed unit disc `|X| ≤ 1` since `|-1|_p = 1`). Any unit in `ℚ_p⟨X⟩` must be non-vanishing on the disc. So `1 + X` is not a unit in `ℚ_p⟨X⟩`.

Since `locSubring ⊆ ℚ_p⟨X⟩` (as the sub-algebra `ℤ_p⟨X⟩[X/p]`), and units in a subring are inherited, `1 + X` is not a unit in `locSubring`.

**Claim 4: `X ∉ Ideal.jacobson ⊥` in `locSubring`.**

`Ideal.mem_jacobson_bot`: `x ∈ Ideal.jacobson ⊥ ↔ ∀ y, IsUnit (x·y + 1)`. Take `y := 1`. Then `X·1 + 1 = 1 + X`, which is not a unit in `locSubring` (Claim 3). Therefore `X ∉ Ideal.jacobson ⊥`.

**Conclusion.**

`X ∈ locIdeal` (Claim 1) and `X ∉ Ideal.jacobson ⊥` (Claim 4), so:

> `locIdeal P T s ⊄ Ideal.jacobson (⊥ : Ideal (locSubring P T s))`

in this concrete Tate setup. The unconditional Jacobson residual is **FALSE**.

## Why the geometric-series argument inherently fails

`ValuationSpectrum.locIdeal_forall_isTopologicallyNilpotent` supplies top-nilpotence of `X` in `locSubring`. If `locSubring` were **complete** in its `locIdeal`-adic topology, then `IsTopologicallyNilpotent.isUnit_one_sub` (project file `GeometricSeries.lean:43`, Wedhorn Prop 5.38, **explicitly requires `[CompleteSpace A]`**) would give `1 - (-X) = 1 + X` a unit. The inverse is `Σ (-X)^n`, and its convergence requires completeness.

In our counterexample, the partial sums `s_n = 1 - X + X² - … + (-X)^n ∈ ℤ_p⟨X⟩ ⊆ locSubring` form a Cauchy sequence in the `locIdeal`-adic topology (differences lie in `locIdeal^(m+1)` for indices `n > m`). The sequence's would-be limit is the non-restricted series `1 - X + X² - …`, which is **not** in `locSubring` (nor in `ℚ_p⟨X⟩`). So `locSubring` is **not adic-complete**, and the geometric-series step breaks down exactly as predicted.

## Implications for T-IDEAL-2 Lane B

The unconditional Jacobson statement cannot close Lane B. The three equivalent entry points we've landed:

1. `..._of_stacks00MA` (raw `Module.FaithfullyFlat locSubring (AdicCompletion …)` hypothesis).
2. `..._of_locIdeal_le_jacobson` (the now-disproved-unconditional form).
3. `..._of_ringOfDef_faithfullyFlat` (`RingHom.FaithfullyFlat (locSubringToRingOfDef D)` hypothesis).

are all equivalent to the same open content. Since (2) is false unconditionally, the other two are also not unconditionally provable by this route. An unconditional closure of Lane B would need a genuinely different argument.

## Request to ChatGPT Pro

**Primary question.** Given the concrete counterexample above (`A = ℚ_p⟨X⟩`, `T = {X}`, `s = p`, so `locSubring = ℤ_p⟨X⟩[X/p]`), what is the correct formalization strategy?

Acceptable response forms:

**(A)** Identify a hidden additional hypothesis in Wedhorn's setup that rules out this counterexample. For example: does Wedhorn/Huber implicitly require `locSubring` to be adic-complete, or require the rational open to satisfy a "non-degeneracy" condition that the above example violates? If yes, restate the Lean hypothesis accordingly and verify the counterexample no longer applies.

**(B)** Confirm that Wedhorn's Cor 8.32 / Thm 8.28 in fact uses faithful-flatness of the COMPLETION `presheafValue_ringOfDef D` (which IS adic-complete) directly, not of `locSubring` itself. If yes, identify the correct formalization target: the faithful-flatness `Module.FaithfullyFlat (presheafValue_ringOfDef) (something)`. Our `Cor832.presheafValue_isAdicComplete` gives `IsAdicComplete` on the completed ring, so Mathlib's `IsAdicComplete.le_jacobson_bot` + our new `AdicCompletion.faithfullyFlat_of_le_jacobson_bot` would directly give `Module.FaithfullyFlat (presheafValue_ringOfDef) (AdicCompletion of that)`. But this is trivial since the ring is already complete — does it help?

**(C)** Provide a genuinely different route to `coeRingHom_preserves_proper`: not via Jacobson/locSubring-FF/adic-completion faithful-flatness, but via some other argument (e.g., direct spectrum surjectivity, flatness + dimension, tensor-product surjectivity on specific classes of ideals, something involving the Tate-ring structure specifically).

**(D)** Identify an additional hypothesis on `A` (not just Noetherian Tate) that makes `locIdeal ≤ Jac(locSubring)` hold. Candidates:
- `A` satisfies a "Jacobson ring" property (every prime = intersection of maximals containing it).
- `A` finitely generated over its pair of definition (affinoid condition).
- `A` of Krull dimension ≤ 1 (rules out the `ℚ_p⟨X⟩` counterexample).
- Some bound on T or s excluding pathological rational opens.

**(E)** Confirm that the Jacobson route is fundamentally not viable for Lane B, and the correct mathematical strategy is to DECOUPLE `tateAcyclicity` from `coeRingHom_preserves_proper` (e.g., via the Hübner route already explored in `.mathlib-quality/chatgpt-packet-hubner-nondomain.md`, or a different reduction).

## Specific Lean signatures

```lean
-- The unconditional claim I tried to prove, now disproven by counterexample:
theorem locIdeal_le_jacobson_bot_unconditional
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D : RationalLocData A) [IsNoetherianRing (locSubring D.P D.T D.s)] :
    locIdeal D.P D.T D.s ≤ Ideal.jacobson (⊥ : Ideal (locSubring D.P D.T D.s))
-- Counterexample: A = ℚ_p⟨X⟩, T = {X}, s = p, witness X ∈ locIdeal with 1 + X
-- not a unit in locSubring.

-- Existing conditional forms (both landed, both circular wrt Lane B):
theorem locIdeal_le_jacobson_bot_of_isAdicComplete
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    [IsAdicComplete (locIdeal P T s) (locSubring P T s)] :
    locIdeal P T s ≤ Ideal.jacobson (⊥ : Ideal (locSubring P T s))

theorem locIdeal_le_jacobson_bot_of_ringOfDef_faithfullyFlat
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D : RationalLocData A) [IsNoetherianRing (locSubring D.P D.T D.s)]
    (hff : RingHom.FaithfullyFlat (locSubringToRingOfDef D)) :
    locIdeal D.P D.T D.s ≤ Ideal.jacobson (⊥ : Ideal (locSubring D.P D.T D.s))
```

## Repo primitives relevant to any fix

| Primitive | Location | Status |
|---|---|---|
| `ValuationSpectrum.locIdeal_forall_isTopologicallyNilpotent` | `IdealLocalization.lean:339` | sorry-free, unconditional |
| `IsTopologicallyNilpotent.isUnit_one_sub` (Wedhorn 5.38) | `GeometricSeries.lean:43` | sorry-free, **requires `[CompleteSpace A]`** |
| `PairOfDefinition.isTopologicallyNilpotent_of_mem` | `HuberRings.lean:101` | sorry-free |
| `Ideal.mem_jacobson_bot` (Mathlib) | Mathlib `RingTheory/Jacobson/Ideal.lean:288` | available, `⟺ ∀ y, IsUnit (x*y + 1)` |
| `IsAdicComplete.le_jacobson_bot` (Mathlib) | Mathlib `RingTheory/AdicCompletion/Basic.lean:847` | available, needs `IsAdicComplete` |
| `AdicCompletion.faithfullyFlat_of_le_jacobson_bot` (project-new) | `AdicCompletionFaithfullyFlat.lean` | sorry-free, **generic Stacks 00MA** |
| `ValuationSpectrum.locSubringToRingOfDef_faithfullyFlat_of_residual` | `IdealLocalizationCompletion.lean:414` | sorry-free, conditional on `Module.FaithfullyFlat locSubring (AdicCompletion …)` |
| `Cor832.presheafValue_isAdicComplete` | `Cor832.lean` | sorry-free: **the completion IS adic-complete**, but locSubring is not |

## What I won't land this session

Per the reviewer's instruction, **no new critical-path sorries**. I am NOT landing a `sorry`'d `locIdeal_le_jacobson_bot_unconditional` since the statement is demonstrably false. The three Jacobson-conditional wrappers from the previous session remain valid conditional infrastructure; their Jacobson hypothesis is not supplied by this session.

## Next session (pending ChatGPT Pro input)

If ChatGPT Pro gives response type **(A), (C), or (D)**, implement accordingly.

If response type **(B)**: the completion IS adic-complete, but this trivializes to self-faithful-flatness and doesn't help unless the "source" ring of a DIFFERENT map is the completion. Revisit Wedhorn's exact Cor 8.32 statement to see which ring-hom's faithful-flatness is the actual content.

If response type **(E)**: pivot back to the Hübner / non-Cor-8.32 route, accepting that Lane B is parked pending the Hübner-route resolution (whose own non-domain obstruction is documented in `chatgpt-packet-hubner-nondomain.md`).
