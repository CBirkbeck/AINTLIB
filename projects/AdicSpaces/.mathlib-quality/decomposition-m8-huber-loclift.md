# Decomposition — M8: `HasLocLiftPowerBounded` at full Huber generality

Goal: `hasLocLiftPowerBounded_huber` — both fields of `HasLocLiftPowerBounded A` for every
complete Huber (f-adic) ring `A` (T2, nonarchimedean, complete for the right uniformity,
`A⁺` a ring of integral elements) — **no `[IsTateRing A]`**. This discharges `IsSheafy`'s
class parameter at the generality where Wedhorn's own Prop 8.2 lives.

## Skeleton location (`lake build` green, sorries only — verified 2026-07-17)
- `Adic spaces/PresheafTateStructure.lean` — `presheafValue_isHuberRing_huber`
- `Adic spaces/SpvAI.lean` — `cofinalValue_ideal_pow_lt_of_le_one_on_ideal`,
  `Spv.isContinuous_of_isInSpvAI_of_lt_one_AOO`
- `Adic spaces/SpvAITopology.lean` — `restrictIdeal_le_one`, `restrictIdeal_one_lt`,
  `restrictIdeal_lt_one`, `restrictIdeal_bot_isMicrobial`,
  `ofValuation_restrictIdeal_bot_isInSpvAI`
- `Adic spaces/FaithfulLocLift.lean` — `mem_plus_of_forall_spa_vle_one_huber`,
  `isPowerBounded_of_forall_vle_one_spa_of_complete_huber`, `isUnit_canonicalMap_s_huber`,
  `locLift_divByS_isPowerBounded_huber`, `hasLocLiftPowerBounded_huber`

## Where Tate-ness enters the current (faithful) chain — the audit result

Exactly **two** places (verified by reading every proof body in `FaithfulLocLift.lean`
and the signatures of everything it calls):

1. **`IsHuberRing (presheafValue D')` supply** (unit side + instances):
   `presheafValue_isTateRing_concrete D' |>.toIsHuberRing`. The five concrete-pair
   ingredients (`presheafValue_ringOfDef/idealOfDef/_isOpen/_fg/_isAdic`) are already
   Tate-free (file context `[CommRing][TopologicalSpace][PlusSubring][IsHuberRing]
   [HasLocLiftPowerBounded]`; no circularity — `FaithfulLocLift` calls them without the
   class in scope and compiles). Only the *bundling* (`presheafValue_concretePair`) and
   `presheafValue_isAdicComplete` carry vestigial `[IsTateRing A]` binders.
2. **The continuity engine in the [Hu2] 3.3(i) witness** (`mem_plus_of_forall_spa_vle_one`
   lines 454-530): `IsTateRing.principalPair` + `restrictIdealSingle` at the topologically
   nilpotent **unit** `π` + `isContinuous_of_isInSpvAI_of_lt_one_principal`. General Huber
   rings have no `π`; the general ideal of definition is f.g. non-principal, and the
   witness may vanish on it (open support), so `restrictIdealSingle`'s `w g ≠ 0` is
   unavailable.

Everything else is already general: the unit criterion
`isUnit_iff_forall_not_vle_zero_of_completePair` (= Wedhorn 7.52(2), via
`exists_spa_point_supp_eq_maxIdeal_of_complete'`, open + non-open maximal-ideal branches)
is Tate-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`, checked
2026-07-17), as are `comap_canonicalMap_mem_rationalOpen`, the HU-a…d facts (adjoin /
localization / dominating-valuation / place-extension), `restrictIdeal` + API, and
`presheafValue_completeSpace_rightUniformSpace`.

## Result R: `hasLocLiftPowerBounded_huber`

### Plain-English proof (transcribed from the sources)

Wedhorn constructs the restriction maps (Prop 8.2(1)) from Lemma 8.1, whose proof reads:

> "As Spa(ϕ) factors through U, we have |ϕ(t)|w ≤ |ϕ(s)|w ≠ 0 for all w ∈ Spa B and
> for all t ∈ T. This implies ϕ(s) ∈ B× by Proposition 7.52. Moreover, for all w ∈ Spa B
> we have |ϕ(t)/ϕ(s)|w ≤ 1. This implies ϕ(t)/ϕ(s) ∈ B⁺ by Proposition 7.52."
> (wedhorn.txt:3701-3706)

with B := 𝒪(V) complete. Prop 7.52 (wedhorn.txt:3472-3477) is unconditional for
(complete) affinoid rings:

> "Proposition 7.52. Let A = (A, A+) be an affinoid ring, and f ∈ A.
> (1) Then |f(x)| ≤ 1 for all x ∈ Spa A if and only if f ∈ A+.
> (2) Assume that A is complete. Then f is a unit if and only if |f(x)| ≠ 0 for all
> x ∈ Spa A."

7.52(2) reduces to Prop 7.51 (wedhorn.txt:3457-3470: A× open via 1 + A°° ⊆ A× from
completeness; maximal ideals closed; Spa(A/m) ≠ ∅ by Prop 7.49) — **already formalized
Tate-free** (`exists_spa_point_supp_eq_maxIdeal_of_complete'`). 7.52(1) is [Hu2]
Lemma 3.3(i) (huber2.txt:633-658), whose proof constructs, for `a ∉ G` (G open integrally
closed): a prime `p ∋ a⁻¹` of `G[a⁻¹]`, a minimal prime `q ⊆ p`, a dominating valuation
`s` (supp = q, ≤ 1 on G, < 1 on p), an extension `t` to the localization, and then

> "Put u = t|A ∈ Spv A and v = u|cΓ_u ∈ Spv A. Then (a) v(a) > 1, (b) v(g) ≤ 1 for all
> g ∈ G, (c) v(x) < 1 for all x ∈ A°°, (d) v ∈ Spv(A, A°°·A). … We conclude from (3.1)
> and (c), (d) that v is a continuous valuation" (huber2.txt:647-657)

— the restriction is by the **characteristic subgroup** `cΓ_u`, and (d) holds by Lemma
2.5(ii)'s *first* disjunct (`Γ_v = cΓ_v`), i.e. microbially — no nonvanishing generator
needed. Continuity is [Hu2] Thm 3.1's reverse direction for a general f-adic ring
(huber2.txt:586-604): per-generator cofinality (its step (1)), then

> "Let U be a subset of A and T a finite subset of U such that {Uⁿ | n ∈ ℕ} is a
> fundamental system of neighbourhoods of 0 in A and T·U = U² ⊆ U. Let γ ∈ Γv be given.
> Since U ⊆ A°° we have v(u) < 1 for every u ∈ U. By (1) there exists a n ∈ ℕ with
> (max {v(t) | t ∈ T})ⁿ < γ. Then v(a) < γ for every a ∈ Tⁿ·U = U^{n+1}. Hence v is
> continuous." (huber2.txt:598-604)

— decay through the **max-value generator** (cf. Lemma 2.4, huber2.txt:432-438: the
convex subgroup generated by `h := max{v(t) | t ∈ T}`). Note the hypothesis is on
`U ⊆ A°°` only — **not** on the ring of definition; this is why the existing A₀-form
engine cannot serve.

### Lemmas (leaves; all stated in the skeleton)

- **L1.1** (relax in place): `presheafValue_concretePair` — drop `[IsTateRing A]`.
  - The five ingredients are Tate-free (verified by signature read); the binder is
    vestigial bundling. Compiler-verified relaxation, same pattern as the T604
    de-noetherianization.
  - Attacks: [circularity] class-in-context refuted (see audit above); [ingredient
    drift] each of the five signatures read directly — none mentions Tate; [source]
    Wedhorn 8.1: "The pair (D, I·D) is a pair of definition of A(T/s)"
    (wedhorn.txt:3673-3675) — stated for f-adic A, no Tate. SURVIVED.
- **L1.2** (leaf): `presheafValue_isHuberRing_huber` := ⟨⟨concretePair⟩⟩.
  - `IsHuberRing` is literally `Nonempty (PairOfDefinition ·)` (HuberRings.lean:71) plus
    `IsTopologicalRing` (instance-available for the completion). Discharge: L1.1 + the
    class constructor. Attacks: [discharge] constructor shape verified against
    HuberRings.lean:71-75. SURVIVED.
- **L1.3** (relax in place): `presheafValue_isAdicComplete` — drop `[IsTateRing A]`
  (keep `[T2Space A]` if consumed). Proof body greps show no Tate/π usage; verify by
  compiler. Attacks: [hidden use] grep for Tate/topNil/π in the proof body — none.
  SURVIVED (final arbiter: the compiler at ticket time).
- **L2.1-3** (leaves): `restrictIdeal_le_one` / `restrictIdeal_one_lt` /
  `restrictIdeal_lt_one` — general-I mirrors of the `restrictIdealSingle` trio
  (SpvAITopology.lean:809-843), by the same case analysis on
  `restrictIdeal_apply_of_mem/of_not_mem/apply_zero` (CharacteristicSubgroup.lean:359-385)
  with `vUnit_mem_cGammaIdeal` (:187) for the ≥1-case.
  - Source: Huber (2.2)-(2.3) `v|H` mechanics (huber2.txt:393-414): values in H kept,
    values outside sent to 0 — monotone transfer is formal.
  - Attacks: [statement] the ≥1-case needs `Units.mk0 (w a) _ ∈ cGammaIdeal w I` for
    `w a ≥ 1` — supplied by `vUnit_mem_cGammaIdeal` for EVERY I ✓; [edge] `w a = 0`
    handled by `apply_zero` branch as in the Single-proofs; [mirror-check] Single-proofs
    compile with the identical skeleton. SURVIVED.
- **L2.4** (leaf): `restrictIdeal_bot_isMicrobial` — the characteristic restriction is
  microbial.
  - Source: [Hu2] 3.3(i)(d) quote above + Lemma 2.5 (huber2.txt:454-460): "(i)
    Γv = cΓv(I). (ii) Γv = cΓv or v(i) is cofinal…". At `I = ⊥`, `cGammaIdealPos`'s ideal
    branch (`∃ a ∈ I, 0 < v a ∧ …`) is empty (only a = 0, v 0 = 0), so the subgroup is
    exactly the characteristic one; each positive γ of the subgroup carries, by
    definition of `cGammaIdealPos`, a witness `a` with `1 ≤ v a ∧ (v a)⁻¹ ≤ γ ≤ v a`,
    and `v a ≥ 1` survives restriction (L2.2 mechanics) — which is `IsMicrobial`
    verbatim (CharacteristicSubgroup.lean:93).
  - Attacks: [generalization attack] the general-I version is FALSE — ideal-branch
    elements γ < 1 need not be bounded below by surviving `v(a)⁻¹` (this is the recorded
    2026-06-22 falsity of `ofValuation_restrictIdeal_isInSpvAI`; our statement is at ⊥
    only, where the branch is empty) — prior-B2 addressed; [edge] trivial characteristic
    subgroup (v ≤ 1 everywhere): positive γ forced = 1, witness a := 1 ✓; [encoding]
    `IsMicrobial` quantifies over the RESTRICTED value group `WithZero (cGammaIdeal w
    ⊥).toSubgroup` — witnesses transfer because their values are ≥ 1 hence kept.
    SURVIVED.
- **L2.5** (leaf): `ofValuation_restrictIdeal_bot_isInSpvAI` — `Or.inr` of L2.4 through
  `isMicrobial_canon_of_restricted` (exists, used at SpvAITopology.lean:804). Holds for
  EVERY ideal I (the microbial disjunct of `Spv.IsInSpvAI` doesn't mention I).
  - Attacks: [discharge] `isMicrobial_canon_of_restricted` signature verified at its use
    site; [shape] `IsInSpvAI` def (SpvAI.lean:83) is a disjunction whose right side is
    I-free ✓. SURVIVED.
- **L3.1** (leaf): `cofinalValue_ideal_pow_lt_of_le_one_on_ideal` — the A°°-form decay.
  - Source: Huber 3.1 decay quote above (huber2.txt:598-604) + Lemma 2.4's max-generator
    (432-438). Source proves it in ~6 lines; expected ~100-150 Lean lines (the existing
    A₀-form analogue `cofinalValue_ideal_pow_lt` is ~165).
  - Proof route (coefficient-free, replacing the A₀-bound): (i) helper claim by
    induction on n: every `a ∈ (span S)·J` satisfies `v a ≤ M · (bound J)` via
    `Submodule.mul_induction_on` (no scalar case!) with a `∀ z ∈ J`-strengthened
    `span_induction` on the left factor whose smul-case reassociates
    `(r • y)·z = y·(r • z)` into the J-factor; iterating from J := P.I (base: h_le_one)
    gives `v ≤ Mⁿ` on `I^{n+1}` with `M := max_{c ∈ S} v c`; (ii) M is attained at some
    generator `c*` (S finite), and `CofinalValue v c*` supplies n with `Mⁿ < γ`.
  - Attacks: [duplicate] `cofinalValue_ideal_pow_lt` requires `h_le_one` on ALL of
    `P.A₀` — unavailable for the 3.3(i) witness (A₀ = closure of the D-image is NOT
    inside B⁺; the witness t is bounded only on B⁺[x⁻¹]) — not a duplicate;
    [edge S = ∅] I = ⊥, `I^n = ⊥` for n ≥ 1, `v 0 = 0 < γ` ✓; [smul-leak] the only
    scalar entry points are `mul_induction_on` (none) and the left-factor span-induction
    (reassociated away) — no bare coefficient survives; [hypothesis strength] `≤ 1` on
    P.I suffices (strictness not needed — decay comes from Mⁿ < γ, not from the
    I-factor). SURVIVED.
- **L3.2** (leaf): `Spv.isContinuous_of_isInSpvAI_of_lt_one_AOO` — the general A°°-form
  engine.
  - Source: [Hu2] Thm 3.1 reverse (huber2.txt:586-604). Assembly mirrors
    `isContinuous_of_isInSpvAI_of_lt_one` (SpvAI.lean:332): per-generator cofinality from
    the `IsInSpvAI` disjuncts — cofinal branch direct; microbial branch is the EXISTING
    argument (SpvAI.lean:360-414), verified (grep) to consume only `h_lt_one` +
    `PairOfDefinition.exists_pow_mul_mem_A₀` — then L3.1 +
    `Valuation.isContinuous_of_ideal_pow_lt`.
  - Attacks: [duplicate 1] `isContinuous_of_isInSpvAI_of_lt_one` needs the A₀-bound —
    unavailable (above); [duplicate 2] `Spv.isContinuous_of_lt_one_general`
    (SpvAITopology.lean:2035) requires `h_lt_one` on the full A-image ideal
    `Ideal.map subtype P.I` — unsatisfiable for the witness (`rs(x·i) = rs(x)·rs(i)`
    with `rs(x) > 1` can exceed 1); it is the vanishing-on-I engine (cf.
    `lt_one_of_le_supp` beside it) — not a duplicate; [h_le_AOO necessity] possibly
    droppable (decay needs only P.I-bounds; microbial branch needs only h_lt_one) —
    worker should attempt the proof without consuming it and note the outcome; keeping
    it is sound either way. SURVIVED.
- **L4** (leaf): `mem_plus_of_forall_spa_vle_one_huber` — the de-Tate'd witness.
  - Source: [Hu2] 3.3(i) full proof (huber2.txt:633-658), already mirrored step-for-step
    by the Tate version's HU-a…d blocks (all Tate-free). Changes only: `rs :=
    restrictIdeal (t.comap algB) ⊥` (Huber's `v = u|cΓ_u` — the Tate version's
    `restrictIdealSingle g` at the unit π was a principal-case surrogate); Spa-membership
    via L2.1 (≤1 on B⁺) and the vle-bridge (same `Compatible.ofValuation` plumbing);
    continuity via L3.2 at `P := presheafValue_concretePair D'` with `h_in` from L2.5,
    `h_le_AOO` from `hW_lt_AOO` (≤ via .le), `h_lt_one` from
    `PairOfDefinition.isTopologicallyNilpotent_of_mem` + `hW_lt_AOO` + L2.3; witness
    `w(x) > 1` via L2.2.
  - Attacks: [restriction fidelity] Huber restricts by cΓ_u, we restrict by
    cGammaIdeal(⊥) = the characteristic subgroup — same object (L2.4's analysis);
    [support-open edge] if W vanishes on the ideal of definition the characteristic
    restriction still works (no nonvanishing hypothesis) and continuity holds with all
    generator values 0 (CofinalValue trivially) — matches Wedhorn 7.51's open-branch
    philosophy; [B⁺-membership of A₀?] NOT needed anywhere in this route (the engine's
    A₀-bound is gone — that was the point). SURVIVED.
- **L4.1** (leaf): `isPowerBounded_of_forall_vle_one_spa_of_complete_huber` — one-liner
  via `IsRingOfIntegralElements.subset_powerBounded` (same as the Tate version).
- **L5** (leaf): `isUnit_canonicalMap_s_huber` — same body as `_faithful` with
  `haveI : IsHuberRing (presheafValue D') := presheafValue_isHuberRing_huber D'` (L1.2),
  pair L1.1, `IsAdicComplete` L1.3; criterion already Tate-free.
  - Attacks: [criterion axioms] `isUnit_iff_forall_not_vle_zero_of_completePair` and
    `exists_spa_point_supp_eq_maxIdeal_of_complete'` axiom-checked clean 2026-07-17;
    [signature drift] both quantify over general `[IsHuberRing A]` contexts ✓. SURVIVED.
- **L6** (leaf): `locLift_divByS_isPowerBounded_huber` — same body as `_faithful`
  (verified criterion-driven: comap-pullback + mk'_spec + unit-cancel; no Tate).
- **L7** (assembly): `hasLocLiftPowerBounded_huber where isUnit… := L5; locLift… := L6`
  + `instance` (no `[IsNoetherianRing]` — the faithful instance's noetherian binder is
  vestigial and this subsumes it).

### Prior-B2 consultation (b2_log.jsonl, 79 entries, + docstring-recorded B2s)
- #11 `cont_to_ideal_le_supp`, #12 `Spv.isContinuous_of_lt_one_general` (unrestricted-I
  falsity), #14 `cont_iff_ideal_le_supp`, #64 `cont_to_ideal_le_supp_microbial`: all
  about I ≠ ideal-of-definition or supp-encodings. Our engine fixes
  I = `Ideal.map subtype P.I` throughout — addressed.
- Docstring-recorded 2026-06-22 falsity of `ofValuation_restrictIdeal_isInSpvAI`
  (general-I restriction not in Spv(A,I)): our L2.4/L2.5 are at I = ⊥ where the
  cGammaIdeal ideal-branch is empty — addressed (see L2.4 attacks).
- #36 `convexSubgroup_from_PI_image`: different shape (dominating-subring split); not
  matched.

### Confidence gate
1. Every leaf discharged from mathlib/project or an explicit skeleton sorry ✓
2. Skeleton compiles (lake build green, sorries only) ✓
3. Verbatim source quotes present per leaf ✓
4. Adversarial pass logged per leaf ✓
5. Prior-B2 log consulted, matches addressed ✓
6. Tree mirrors the sources' proof structure (Wedhorn 8.1→7.52→7.51 / [Hu2] 3.3(i)→3.1
   →2.4/2.5), LOC estimates anchored to source line counts ✓
7. All leaves single-conclusion (L7 is the standard two-field class assembly) ✓
