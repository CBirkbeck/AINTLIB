# Decomposition — the 4 residual leaves of Thm 8.28(b) (sheafiness)

**Mode:** `/develop --decompose` adversarial. **Sources:** all local in `references/`
(`wedhorn.txt`, `huber1.txt`=[Hu1] Habilitation, `huber1994.txt`=[Hu3], BGR, Henkel PDFs).
Source mapping verified against Wedhorn's bibliography (`wedhorn.txt:5725-5745`), NOT memory:
**[Hu1]** = Bewertungsspektrum (Habilitation), **[Hu2]** = Continuous valuations (1993),
**[Hu3]** = A generalization (1994). Build is green (3190 jobs); these are the only
critical-path sorries.

## ★ REVISED per /expert-review (2026-06-19) — read this first

The reviewer (adic-spaces expert) checked the 4-leaf plan against the source. Net effect:
**one leaf's red flag is eliminated, one leaf is greatly simplified, two are confirmed.**
Reply: `.mathlib-quality/expert-review/2026-06-19/reply.md`. Source-verified by us.

- **Leaf #4 — RED FLAG WITHDRAWN.** The correct source is **Wedhorn 7.52(1) = 7.18(1)**
  ("`f ∈ A⁺ ⟺ v(f) ≤ 1 ∀v ∈ Spa(A,A⁺)`", `wedhorn.txt:3619` / `:3161`), which is **stated
  for any affinoid ring — no completeness, Tate, or noetherian ring of definition.** Our
  earlier ℂ_p concern came from conflating it with the *density* converse 7.18(3) (the only
  part needing a noetherian ring of definition). New target: prove 7.52(1) (the τ∘σ=id
  direction, hypothesis-free, content in [Hu1] §3 / [Hu2] 3.3 parts i–ii — NOT iii) and
  wrap the leaf as `v(x)≤1 ∀v∈Spa ⟹ x∈A⁺ ⟹ x∈A°` (the second ⟹ is our already-built
  `IsRingOfIntegralElements.subset_powerBounded`). NUANCE vs reviewer: 7.52(1) is *not* yet
  an in-project lemma (only 7.52(2) `wedhorn_7_52_2_isUnit_iff_forall_not_vle_zero` is), so
  it is a small **hypothesis-free** sub-leaf, not a pure deletion.
- **Leaf #1 — SIMPLIFIED (no Prop 6.18).** Corestrict `ρ : R=𝒪_X(U) → P=∏𝒪_X(Uᵢ)` to the
  closed equalizer `E` of the overlap maps; separation+gluing give a continuous bijection
  `ρ̃ : R → E`; `E` is closed (kernel of the overlap difference map) hence complete +
  countably-based; apply the **already-landed Theorem 6.16** (`BanachOMT.lean`: complete
  target + surjective ⟹ open) to `ρ̃`; continuous+injective+open ⟹ homeomorphism; compose
  with `E ↪ P`. Prop 6.18 (the "Proof. Missing" functional analysis) is **not needed**.
  RISK: do not apply 6.16 to `ρ` into the full `P` (not surjective) — corestrict to `E` first.
- **Leaf #2 — CONFIRMED; openness is automatic.** `A⁺` open ⟹ `Iⁿ ⊆ A⁺` ⟹ `IⁿA₀[T/s]` is an
  open nbhd of 0 in the loc topology, `⊆ A⁺[T/s]`, so `A⁺[T/s]` open ⟹ its integral closure
  `G` open ⟹ `G` is a ring of integral elements of `A[1/s]` (+ 7.19/7.20 for `G ⊆ (A[1/s])°`)
  ⟹ `closure(G)` a ring of integral elements of the completion by **7.47(4)**. RISK: the
  localized plus-ring must contain the generators `T/s` and be integrally closed (it does:
  our def is `closure(image of IntCl(locPlusSubring))`).
- **Leaf #3 — CONFIRMED; only the general (non-noetherian) branch of 7.45 is needed.** Add a
  one-line maximality lemma (for maximal `p`, `p ⊆ supp x` + supp prime ⟹ `supp x = p`).
  Prop 7.41 is the height-1-bound-on-A° step. ℂ_p-safe.
- **Gluing dependency correction (Q4b).** Gluing needs neither leaf #1 nor the former leaf
  #4, but it DOES depend on leaf #2 (relative use over `𝒪_X(U)`) and **leaf #3** (Lemma 7.54
  uses Cor 7.53, whose proof uses maximal-ideal Spa points from Prop 7.51). Record leaf #3
  as upstream of gluing — not "gluing is wholly independent."

**Revised residual: 3 leaves** — #1 (equalizer+6.16 assembly, tractable), #2 (7.47(4)
completion + openness chain), #3 (general 7.45 + maximality). Former #4 → small
hypothesis-free 7.52(1) sub-leaf (possibly mergeable with the leaf #3 / Cont(A) work, since
both are [Hu1] §3 valuation theory). The original per-leaf analysis below is retained for
record; the **revised** statements above supersede it where they differ.

---

## Skeleton location (existing — these are the live sorries, not new decls)
- Leaf #1: `StructureSheaf.lean:1384` `productRestrictionSub_isInducing_tate := sorry`
- Leaf #2: `Presheaf.lean:505-507` `presheafValuePlus_isRingOfIntegralElements` 3 sorry fields
- Leaf #3: `Presheaf.lean:2785` `exists_cont_supp_ge_powerBounded_of_nonOpen_prime := sorry`
- Leaf #4: `FaithfulLocLift.lean:92` `isPowerBounded_of_forall_vle_one_spa_of_complete := sorry`

---

## Leaf #1 — topological inducing of `productRestrictionSub` (Wedhorn Prop 6.18)

### Source situation — RED FLAG (rule 4): Wedhorn does NOT prove this
`wedhorn.txt:2596-2621`: Thm 6.16 (Banach for Tate rings), Prop 6.17 (noeth ⟺ ideals
closed), Prop 6.18 (f.g. modules: unique complete topology + continuity/openness) — **all
three say literally "Proof. Missing"**. Wedhorn defers the entire Banach/noetherian-Tate
functional analysis to the primary literature. So the faithful route transcribes **[Hu1]**
(§3.5 "Tate-Ringe mit noetherschem Definitionsring", `huber1.txt:146`) and/or **BGR**
(classical Banach for affinoid algebras), NOT Wedhorn.

### Verbatim (Wedhorn `wedhorn.txt:2615-2621`)
> "Proposition 6.18. Let A be a complete noetherian Tate ring. (1) Every finitely
> generated A-module has a unique A-module topology that is complete and that has a
> countable fundamental system of open neighborhoods of 0. (2) Let f : M → N be an
> A-linear map of finitely generated modules ... Then f is continuous and the map
> f : M → f(M) is open. Proof. Missing"

### Decomposition (must mirror [Hu1]/BGR, not invent)
- **L1.1 — Thm 6.16 (Banach OMT, units→0 form).** Status: *already landed sorry-free* in
  the project (`wedhorn_6_16_of_topNilpUnit`, per the faithful-OMT work). Source for the
  units→0 strengthening: Henkel 2014 (`Henkel-...pdf`). VERIFY this claim against the code.
- **L1.2 — Prop 6.17 (noeth ⟺ every submodule closed).** Source: [Hu1] §3.5 / BGR.
- **L1.3 — Prop 6.18(1) (unique complete f.g.-module topology).** Source: [Hu1] §3.5.
  Wedhorn Remark 6.19 (`wedhorn.txt:2622`) gives the explicit basis `{sⁿM₀}`.
- **L1.4 — Prop 6.18(2) ⟹ `productRestrictionSub` inducing.** The Lean leaf is the
  inducing of `productRestrictionSub A C : O_X(C.base) → ∏ O_X(Dᵢ)`; 6.18(2) gives that an
  A-linear map of f.g. modules is continuous + open-onto-image. NEEDS: identify `O_X(C.base)`
  and the product as f.g. modules + apply 6.18(2). **This is the genuine in-project assembly.**

### Adversarial attacks
- **[A4 source-drift / A-structure]** 6.18 requires **complete *noetherian* Tate**. Our
  headline has `[IsStronglyNoetherian A]` + `[IsNoetherianRing A]` + complete Tate — OK at
  base. But `productRestrictionSub` lives over completions; need 6.18's hypotheses to hold
  for the completed structure rings (they're strongly-noeth Tate, established). CHECK.
- **[A5 discharge]** Is `wedhorn_6_16_of_topNilpUnit` genuinely sorry-free and does its type
  match what 6.18(2)→inducing needs? Must `lean_verify` / `#print axioms`.
- **[A1 deepest-leaf]** The "Proof Missing" is the tell: 6.18(2)→inducing is real
  functional analysis. Risk that the in-repo assembly needs the f.g.-module-topology
  uniqueness (6.18(1)), which is itself unproved. **This is the deepest leaf.**
- Verdict: **NOT a clean leaf** — it is an internal node whose sub-leaves (6.16✓, 6.17, 6.18(1),
  6.18(2)→inducing) need their own decomposition from [Hu1] §3.5 / BGR. Ticket as a sub-tree.

---

## Leaf #2 — `(presheafValue D)⁺ = Ĉ` is a ring of integral elements (Wedhorn 7.47(4))

### Source situation — proof IS available ([Hu1] 2.4.3, German, concrete)
Wedhorn 7.47(4) (`wedhorn.txt:3557`) "Rings of integral elements of A ↔ of Â. Proof.
[Hu1] 2.4.3." The proof is `huber1.txt:7465-7560` (German, §2.4.3).

### Verbatim ([Hu1] `huber1.txt:7491-7512`, German, lightly de-OCR'd)
> "iv) die Ganzheitsringe von A und die Ganzheitsringe von Â [correspond].
> Beweis: ... Ist H ein in Â ganz abgeschlossener Unterring von Â, so ist natürlich
> i⁻¹(H) ganz abgeschlossen in A. Zu zeigen bleibt noch: Ist G ein in A ganz
> abgeschlossener und offener Unterring von A, so ist Ĝ ganz abgeschlossen in Â.
> Sei a ein Element von Â, das ganz über Ĝ ist. Wir zeigen a ∈ Ĝ = î(G). Dazu ist zu
> zeigen, daß U ∩ î(G) ≠ ∅ für jede Umgebung U von a in Â. ..."

### Decomposition (mirrors [Hu1] 2.4.3's structure)
- **L2.1 — bounded/top-nilpotent transfer:** `i⁻¹(Â°)=A°` ([Hu1] 7492-7495). This is the
  Lean `subset_powerBounded` field route (Ĉ ⊆ Â° via Â° = closure-stable). Needs:
  continuous-hom preserves power-bounded (`IsPowerBounded.map`, exists `Presheaf.lean:3612`)
  + Â° clopen (`isOpen_powerBoundedSubring` `HuberRings.lean:257` → open subgroup closed).
- **L2.2 — easy half:** H integrally closed in Â ⟹ i⁻¹(H) integrally closed in A (7505).
  (Not directly the Lean field, but the bijection's other direction.)
- **L2.3 — hard half (`isIntegrallyClosed` field):** G integrally-closed + **open** in A ⟹
  Ĝ = closure(G) integrally closed in Â (`huber1.txt:7510-7560`). The density argument:
  a integral over Ĝ ⟹ show every nbhd U of a meets î(G), via H = integral closure of G in
  A (open since G open) and the monic relation `i(b)ⁿ + cₙ₋₁i(b)ⁿ⁻¹ + … = 0`.
- **L2.4 — `isOpen` field:** Ĝ open (closure of an open subgroup is open).

### Adversarial attacks
- **[A4 source-drift — IMPORTANT]** Our Lean def is `completedPlusSubring D :=
  closure(image of IntCl(locPlusSubring))` — i.e. Ĝ with **G = IntCl(locPlusSubring)**, the
  *precompletion* ring of integral elements of `A_s`. [Hu1] 2.4.3(iv) requires G to be a
  ring of integral elements of `A_s` (= integrally closed + open + ⊆ A_s°). So leaf #2
  **transitively requires the precompletion fact** (Wedhorn 7.19/7.20: `(A⁺[T/s])^int` is a
  ring of integral elements of `A_s`) as a SEPARATE sub-leaf. Is `IntCl(locPlusSubring)`
  open in `A_s`? (needs `locPlusSubring` open ⟹ IntCl open). **Flag: add precompletion
  sub-leaf; verify "open" holds.**
- **[A3 hidden hyp]** [Hu1] 2.4.3 needs **G open** (used to make H open). Our G =
  IntCl(locPlusSubring): is it open? Only if locPlusSubring open in A_s. CHECK — possible
  gap.
- **[A5 discharge]** `IsPowerBounded.map` + `isOpen_powerBoundedSubring` exist (verified by
  grep); the density argument (L2.3) is new infra (~the Huber proof, faithful).
- Verdict: **internal node**, 4 sub-leaves; faithful (proof available in [Hu1]); but the
  precompletion 7.19/7.20 + the "open" check are real sub-obligations.

---

## Leaf #3 — analytic Spa-point of a non-open prime (Wedhorn 7.45 + 7.41)

### Source situation — Wedhorn-INTERNAL (fully proved; the most tractable leaf)
Full proof at `wedhorn.txt:3438-3535`. NOT deferred to Huber.

### Verbatim (Wedhorn `wedhorn.txt:3438-3444`, Prop 7.41)
> "Proposition 7.41. Let A be an f-adic ring and let x ∈ Cont(A)ᵃ be of height 1. Then
> x(a) ≤ 1 for all a ∈ A°. ... Proof. Let a ∈ A° and assume that x(a) > 1. Choose b ∈ A°°
> with x(b) ≠ 0 ... As Γx has height 1, it is archimedean (Proposition 1.14). Hence there
> exists n ∈ N with x(aⁿ) > x(b)⁻¹, i.e., x(aⁿb) > 1. But as a is power-bounded, aⁿb ∈ A°°
> and thus the continuity of x implies x(aⁿb) < 1. Contradiction."

### Decomposition (mirrors Wedhorn 7.45's proof chain)
- **L3.1 — Prop 7.41** (height-1 ⟹ x(a)≤1 on A°). `wedhorn.txt:3438`, 4-line proof.
  Needs: `Γx` archimedean from height 1 (Prop 1.14 analogue), A°°-continuity, A°° def.
  PROVABLE.
- **L3.2 — Lemma 7.44(3)** (`wedhorn.txt:3469`): for B open ⊆ A, `Cont(A)ᵃ ≅ Cont(B)ᵃ`
  preserving Γ. PROVABLE (the Bₛ→Aₛ iso for non-open primes).
- **L3.3 — Remark 7.42(2)/4.12** (`wedhorn.txt:3450`): analytic ⟹ microbial ⟹ ∃ height-1
  vertical generization. The `restrictToConvex`-to-height-1 step.
- **L3.4 — the 7.1.2 retraction `r : Spv(B₀) → Spv(B₀,I)`** + **Theorem 7.10** (Cont
  characterization). In-repo this is `restrictToConvex` — **already present but with a
  sorry**. This is leaf #3's deepest dependency.
- **Assembly — Lemma 7.45 general case** (`wedhorn.txt:3491-3506`): u dominating m ⊇ p₀ →
  r(u) ∈ Cont(B₀) non-analytic (Thm 7.10, Lemma 7.5(3)) → v analytic on A (7.44(3)) →
  x height-1 (4.12) → x ∈ Spa (7.41).

### Adversarial attacks
- **[A3 hidden hyp — GOOD NEWS]** Wedhorn 7.45's *general case* needs only "complete
  affinoid" — NO noetherian ring of definition. (The noeth-ring-of-def is only for the
  *additional* "discrete valuation, supp x = p" refinement, which the leaf does NOT need.)
  So leaf #3 is ℂ_p-safe. ✓
- **[A5 discharge]** Deepest dependency = `restrictToConvex` (7.1.2 retraction), in-repo
  with a sorry; + Theorem 7.10. CHECK their status — leaf #3 reduces to those.
- **[A1]** Prop 1.14 (height-1 ⟹ archimedean value group) — is it in repo/mathlib? CHECK.
- Verdict: **internal node, Wedhorn-faithful, most tractable**; bottoms at the in-repo
  `restrictToConvex` sorry + Thm 7.10 + Prop 1.14. Strong ticket candidate.

---

## Leaf #4 — power-bounded from Spa-bound (`isPowerBounded_of_forall_vle_one_spa`)

### Source situation + ADVERSARIAL RED FLAG
The Lean leaf: `∀v∈Spa, v(x)≤1 ⟹ x ∈ A°` (power-bounded). Cited to [Hu2] 3.3. Wedhorn's
σ(A⁺) remark (`wedhorn.txt:3168-3174`, "Proof. [Hu2] Lemma 3.3"):
> "(2) Let A⁺ ... be a ring of integral elements. Then every point of Cont(A) is a vertical
> specialization of a point in σ(A⁺); ... σ(A⁺) is dense in Cont A.
> **(3) If A is a Tate ring and has a noetherian ring of definition, then also the converse
> of (2) does hold:** if A′ ∈ RA such that σ(A′) is dense in Cont A then A′ ⊆ A°."

**The leaf is the CONVERSE direction (something-bounded-on-Spa ⟹ power-bounded), which
Wedhorn's part (3) supplies ONLY under "Tate + noetherian ring of definition"** — the
ℂ_p-FALSE noeth-ring-of-definition hypothesis (the exact defect this project has been
purging). Run the ℂ_p test: ℂ_p is complete Tate, NO noetherian ring of definition, and
the leaf's statement (v≤1 on Spa ⟹ power-bounded) — does it hold for ℂ_p? If part (3) is
the only route and it needs noeth-ring-of-def, the leaf may be **false-as-stated for ℂ_p**,
or need a different (pair-free) route.

### Decomposition — DEFERRED pending the ℂ_p verdict
Do NOT decompose until the adversarial flag is resolved:
1. Re-read [Hu2] 3.3 (content in [Hu1] §3, `huber1.txt` Cont(A)) — is the converse really
   noeth-ring-of-def-only, or is there a complete-affinoid route (à la 7.45)?
2. Re-examine the Lean leaf's USE site (FaithfulLocLift flatness): does the flatness chain
   genuinely need the full converse, or only `x ∈ A⁺ ⟹ v(x)≤1` (the EASY direction)?
3. If the leaf as stated needs noeth-ring-of-def → B2 candidate (restate or re-route).

### Adversarial attacks
- **[A2 ℂ_p edge case]** ℂ_p: complete Tate, no noeth ring of def. Leaf must hold here
  (8.28(b) holds for ℂ_p). If the only proof needs noeth-ring-of-def → leaf false-for-ℂ_p.
- **[A4 source-drift]** Does the Lean statement match the EASY direction (7.41-style, A° via
  Spa-bound) or the HARD converse (3.3(3), noeth-only)? CRITICAL to pin.
- Verdict: **REVIEW-PENDING / B2-candidate** — strongest `/expert-review` question.

---

## Feasibility assessment (first pass)

The decomposition is **source-grounded and feasible to plan**, with these honest findings:
- **Leaf #3** (analytic Spa-point) is the most tractable: Wedhorn-internal, ℂ_p-safe, bottoms
  at the in-repo `restrictToConvex` sorry + Thm 7.10 + Prop 1.14.
- **Leaf #2** (ring-of-integral-elements completion) has a concrete [Hu1] 2.4.3 proof;
  decomposes into 4 sub-leaves + a precompletion (7.19/7.20) obligation; the "G open" check
  is a possible gap.
- **Leaf #1** (6.18 inducing) is the deepest: Wedhorn says "Proof Missing"; the real proof
  is [Hu1] §3.5 + BGR functional analysis (6.16 landed; 6.17 + 6.18(1)/(2)→inducing remain).
- **Leaf #4** is a genuine ADVERSARIAL CATCH: its cited source ([Hu2] 3.3 converse) needs
  "noetherian ring of definition", the ℂ_p-false hypothesis — must resolve (ℂ_p test +
  use-site analysis + `/expert-review`) before it can be ticketed; possible B2.

**Recommended order:** #3 (tractable, Wedhorn-faithful) → #2 (concrete [Hu1] proof) → #1
(deep, [Hu1]§3.5/BGR) ; #4 to `/expert-review` first (ℂ_p red flag).

**NOT done (this is decompose-pass-1):** the full 5-attack-per-sub-leaf treatment, the Lean
skeleton refinement, and the per-leaf provability `lean_verify`s — to be completed per leaf
before ticketing, and after `/expert-review` settles leaf #4.
