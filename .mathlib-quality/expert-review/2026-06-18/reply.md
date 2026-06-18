# Reviewer reply — 2026-06-18

## Verdict: the encoding gap is genuine; the fix is an interface change, not a new theorem.

Make "ring of integral elements" part of the **affinoid-ring interface**. A bare arbitrary subring is not enough data for any theorem about `Spa`. Pair of definition (controls topology/continuity/completion/localisation topology) and ring of integral elements (controls which continuous valuations are `Spa` points) are **separate** and **need not contain one another**.

## Q1 — encoding (answer: hybrid (a))
- Keep `PlusSubring A` as a low-level carrier only (for construction / generic algebra).
- Add `IsRingOfIntegralElements A⁺` : open + integrally closed + `A⁺ ≤ A°`.
- Add `AffinoidRing A` bundling/installing both.
- Require an `IsRingOfIntegralElements` instance in the affinoid object **and in all `Spa`-level theorems**. Do NOT thread the three axioms manually; do NOT rederive them. Mirrors Wedhorn; safer for morphisms, base change, completion, quotients, perfectoids.

## Q2 — completion is affinoid (answer: YES, via Wedhorn 7.19 + 7.47 + 8.16)
The completed rational localisation is canonically affinoid. **Critical**: the plus-ring is the closure of the **correct precompletion ring** `C = IntCl_{A_s}(A⁺[t₁/s,…,tₙ/s])` (integral closure of `A⁺` adjoined the fractions `T/s`), NOT merely the closure of the image of `A⁺`.
- Prop 7.19 (affinoid rational-localisation): `C` is a ring of integral elements in the uncompleted `A_s`.
- Lemma 7.47 (completion correspondence: rings of integral elements ↔ rings of integral elements under completion): `Ĉ ⊆ A⟨T/s⟩` is a ring of integral elements.
- Prop 8.16 identifies `Ĉ` with `𝒪_X⁺(U)`.
Iterates with no new subtlety — repeat at each stage.

## Q3 — exact vs containment for maximal 𝔪 (answer: my argument is correct)
`𝔪 ⊆ supp v`, `𝔪` maximal, `supp v` a proper prime ⟹ `supp v = 𝔪`. No rank-1 theorem. Containment suffices for the whole sheaf proof (nonunit f vanishes at a Spa point; maximal-ideal extension to a cover factor is proper). Exact support for a NON-maximal prime is not needed on this path — keep it a separate theorem.

## Q4 — pair-free routing (answer: faithful, but ONE correction)
**The brief's sentence "any continuous valuation is ≤ 1 on A°" is FALSE in higher rank.** The bound on `A°` holds for **height-one analytic** continuous valuations. Correct proof of the non-open-prime Spa point:
```
construct continuous analytic valuation with supp ⊇ p
→ take its HEIGHT-ONE vertical generization (Lemma 7.45 / Remark 4.12)
→ Prop 7.41 gives v(a) ≤ 1 for all a ∈ A°
→ A⁺ ≤ A° gives v(A⁺) ≤ 1
→ v ∈ Spa(A, A⁺).
```
(For open support, the trivial valuation has values 0/1, bounded on every plus-subring.) `A⁺ ⊆ A₀` is an artifact of the current formal proof, NOT a hypothesis of Wedhorn's theory. No single ring of definition containing `A⁺` is needed for 8.28(b).

## Q5 — strategy (answer: cleanest faithful route, confirmed)
Prop 8.30/Cor 8.32 (separation + faithful-flat descent) ∧ Lemma 8.33/8.34 (Čech gluing + higher rational acyclicity) ∧ OMT on the equalizer (embedding). "Direct Tate acyclicity" = 8.33–8.34 renamed; descent-only still needs the same infrastructure.

## Lean-facing next steps (reviewer's 8)
1. Activate `IsRingOfIntegralElements (Aplus : Subring A)` : isOpen + isIntegrallyClosed + le_powerBounded.
2. Main affinoid context provides it automatically; bare `PlusSubring` stays low-level data.
3. Restate the pair-free Spa-point theorem with `[IsRingOfIntegralElements Aplus]` (not `Aplus ≤ P.A₀`, not bare).
4. Refactor the non-open-prime proof: height-one point → 7.41 → bounded on A° → bounded on A⁺. Do NOT use "every continuous valuation bounded on A°".
5. Rational-localisation plus-ring = integral closure of `A⁺` image together with fractions `T/s`; prove ring-of-integral-elements in uncompleted localisation (Prop 7.19).
6. Completed plus-ring = closure corresponding under Lemma 7.47; expose `presheafValue_plus_isRingOfIntegralElements`, reusable under iteration.
7. Replace `CompatiblePlusSubring` in the inner/completion critical path (may stay as optional stronger convenience for old lemmas; not in the Wedhorn-clean theorem).
8. Helper `support_eq_maximal_of_le (hm : m.IsMaximal) (h : m ≤ v.supp) : v.supp = m`.

## Risks (reviewer's 4)
1. **Defining the completed plus-ring incorrectly** (closing only the image of `A⁺`, omitting the rational generators `T/s` and integral closure). Source ring must be `IntCl(A⁺[T/s])`.
2. Relying on a generic "`A°` closed ⟹ closures of power-bounded stay power-bounded". Unnecessary + may have extra hypotheses. Lemma 7.47 is the precise source and also supplies openness + integral closedness.
3. Erasing the **height-one step** from Lemma 7.45. The weak `A⁺ ⊆ A°` suffices ONLY because the valuation is made height-one before Prop 7.41. Higher-rank continuous valuations need not be ≤ 1 on `A°`.
4. Global typeclass churn — changing the bare `PlusSubring` class itself may break low-level declarations needing only a carrier. Prefer adding a proof class / bundled affinoid context and migrating `Spa`-level theorems.
