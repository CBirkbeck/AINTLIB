# Review brief — Formalising the cyclotomic Iwasawa Main Conjecture: can the ramified-CFT input be avoided?

*Prepared 2026-06-18 for an Iwasawa-theory specialist. Self-contained: no repository access required. The question is a **formalisation-strategy** one — we want to know whether a particular class-field-theory input can be avoided or reduced to ingredients we have already mechanised in Lean.*

## 1. Goal

We are formalising (in Lean 4 / Mathlib) the cyclotomic Iwasawa Main Conjecture following Rodrigues-Jacinto–Williams (*An introduction to p-adic L-functions*, arXiv:2309.15692), §13. The analytic half — the construction of `ζ_p` and the cyclotomic-unit/local-unit description of it — is essentially complete. The remaining work is the **arithmetic (Galois) half**, and it currently rests on **one** input we have not mechanised: the ramified class-field-theory exact sequence relating semi-local units to the Galois group of the maximal abelian p-extension unramified outside p. **We would like to know whether that single input is genuinely necessary, or whether the Main Conjecture (Vandiver case and/or general case) can be reached by a route that uses only the class-field-theoretic facts we already have formalised.**

## 2. Setting and notation

Standard cyclotomic setup. `p` an odd prime, `F_n = ℚ(μ_{p^n})`, `F_∞ = ∪ F_n`, `F_n⁺`/`F_∞⁺` the maximal totally real subfields. `𝒢 = Gal(F_∞/ℚ) ≅ ℤ_p^× = Δ × Γ`, `Δ = Gal(F_1/ℚ) ≅ (ℤ/p)^×` (order prime to p), `Γ ≅ ℤ_p`. `𝒢⁺ = 𝒢/⟨c⟩` (c = complex conjugation). `Λ(𝒢) = ℤ_p⟦𝒢⟧`, `Λ(𝒢⁺) = ℤ_p⟦𝒢⁺⟧`; after fixing the prime-to-p part, `Λ(𝒢⁺) ≅ 𝒪⟦T⟧` on each Δ-isotypic component. We work with coefficients in `𝒪 = 𝒪_L`, `L/ℚ_p` finite, large enough to contain the relevant character values.

The two Iwasawa modules at issue:

- **`𝒴_∞ = Gal(𝓛_∞/F_∞)`**, `𝓛_∞` = maximal **unramified** abelian pro-p extension of `F_∞`. By **unramified** class field theory, `𝒴_∞ ≅ lim_n A_n` where `A_n = Cl(F_n) ⊗ ℤ_p` is the p-part of the class group (norm maps). Likewise `𝒴_∞⁺`, `A_n⁺`.
- **`𝒳_∞ = Gal(𝓜_∞/F_∞)`**, `𝓜_∞` = maximal abelian pro-p extension of `F_∞` **unramified outside p**. Likewise `𝒳_∞⁺`. This is the module the Main Conjecture is stated about.

The Λ(𝒢)-action on both is by the inner-automorphism (conjugation-by-lift) action.

`I(𝒢⁺)ζ_p ⊂ Λ(𝒢⁺)` is the "analytic" ideal cut out by the p-adic zeta pseudo-measure (encoding the zeros of `ζ_p`).

**Main Conjecture (RJW Thm IMC).** `𝒳_∞⁺` is a finitely generated torsion `Λ(𝒢⁺)`-module and
`ch_{Λ(𝒢⁺)}(𝒳_∞⁺) = I(𝒢⁺)ζ_p`.

**Vandiver case (RJW thm:vandiver).** If `p ∤ h_1⁺` (Vandiver) then `𝒳_∞⁺ ≅ Λ(𝒢⁺)/I(𝒢⁺)ζ_p`, whence the Main Conjecture.

## 2.2. References

- [RJW23] J. Rodrigues-Jacinto, C. Williams. *An introduction to p-adic L-functions*. arXiv:2309.15692. (Our primary source; §13 is the Iwasawa-theory chapter.)
- [Wa97] L. Washington. *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83. (RJW cite Cor 13.6 for the ramified-CFT sequence, Prop 13.22 for coinvariants, Ch. 15 for the Euler-system/Thaine material.)
- [CS06] J. Coates, R. Sujatha. *Cyclotomic Fields and Zeta Values*, Springer Monographs. (RJW follow §4.5; App. A.1 for the equivariant characteristic-ideal formalism.)
- [MW84] B. Mazur, A. Wiles. *Class fields of abelian extensions of ℚ*. Invent. Math. 76. (First proof of the Main Conjecture.)
- [Ru91]/[Lang] K. Rubin, "The main conjecture" (appendix to Lang, *Cyclotomic Fields I and II*). (Euler-system proof à la Kolyvagin–Rubin–Thaine.)
- [Gr89] R. Greenberg. *Iwasawa theory for p-adic representations*. Adv. Stud. Pure Math. 17. (Selmer-group formulation; RJW §13.4 sketches it.)

## 3. What is already formalised (the inventory that matters for the question)

This is a monorepo: several number-theory projects share one Lean build and can import each other. The relevant already-mechanised, machine-checked (sorry-free unless noted) ingredients are:

**Analytic / unit side (complete):**
- The **Coleman map** for the cyclotomic tower (explicit local reciprocity: local units → power series / measures), with its main theorem.
- **Iwasawa's theorem** (the unit-side Main Conjecture): an isomorphism of `Λ(𝒢⁺)`-modules
  `𝒰_{∞,1}⁺ / 𝒞_{∞,1}⁺ ≅ Λ(𝒢⁺)/I(𝒢⁺)ζ_p`, where `𝒰_{∞,1}⁺` = (inverse limit of) principal semi-local units and `𝒞_{∞,1}⁺` = (closure of) cyclotomic units. This is the analytic input the Galois side must connect to.
- The full p-adic `ζ_p` pseudo-measure, the ideal `I(𝒢⁺)ζ_p`, the ±-decomposition of `Λ(𝒢)`.

**Λ-module structure theory (complete):** characteristic ideals of finitely generated torsion `Λ`-modules via length at height-one primes; multiplicativity in exact sequences; pseudo-isomorphism invariance; the equivariant characteristic ideal `ch_{Λ(𝒢)}` via the isotypic (character-idempotent) decomposition `M = ⊕_ω M^{(ω)}`.

**Class-field-theory facts available in sibling projects (sorry-free):**
- **Unramified CFT / Hilbert 94**: for an unramified cyclic extension of odd prime degree, `[L:K] ∣ |Cl(𝓞_K)|`, plus the capitulation statement; and the Hilbert p-class field isomorphism `Gal(H_p(L)/L) ≅ Cl(𝓞_L)/Cl^p`. **This gives the `𝒴`-side (class groups ↔ unramified extension) for free.**
- Class-group `±` structure: the injection `Cl(F⁺) ↪ Cl(F)`, `h = h⁺ h⁻`, `p ∣ h⁻ ⟺ p ∣` a relevant Bernoulli numerator (one direction of Herbrand–Ribet); the Δ-action and ω^i-eigenspace projectors on class groups and on units.
- **Hilbert 90** (cohomological and algebraic forms).
- **Cyclotomic/circular units**: Sinnott's group, the index `[𝒱 : 𝒟]` via an explicit regulator determinant.
- **Euler-system / Thaine machinery (finite level)**: Thaine's theorem (annihilation of class groups by circular units), Kolyvagin-derivative classes, single-character descent, auxiliary-prime selection. (Built for an FLT/Vandiver application at fixed level, not yet assembled into a tower-level Euler system.)
- **Chebotarev density** (full statement; Dirichlet primes in APs; infinitude of primes with prescribed Frobenius).
- **Vandiver's conjecture proven for p = 37** (plus side), as a worked instance.

**What is NOT formalised anywhere (monorepo or Mathlib):**
- **Ramified class field theory**: ray class groups, conductors, the global Artin reciprocity map for **ramified** abelian extensions, and in particular the exact sequence (RJW Prop CFTunits1, [Wa97, Cor 13.6])
  `0 → 𝓔_{∞,1}⁺ → 𝒰_{∞,1}⁺ → Gal(𝓜_∞⁺/𝓛_∞⁺) → 0`,
  where `𝓔_{∞,1}⁺` is the (inverse limit of the) p-adic closure of the global units inside the semi-local units. Note `𝓜⁺` is ramified at p, so this is genuinely ramified CFT — distinct from the Hilbert class field (unramified everywhere) that we do have.
- Selmer/Galois-cohomology infrastructure over the tower (H¹ exists in Mathlib for finite groups / `groupCohomology`, but not the global arithmetic-duality apparatus).

## 4. How RJW's proof uses the missing input

RJW's Vandiver-case proof (which we were about to formalise) is:

1. Galois theory: `0 → Gal(𝓜_∞⁺/𝓛_∞⁺) → 𝒳_∞⁺ → 𝒴_∞⁺ → 0` (fundamental theorem of Galois theory). *(elementary)*
2. **Ramified CFT** ([Wa97, Cor 13.6], inverse limit): `0 → 𝓔_{∞,1}⁺ → 𝒰_{∞,1}⁺ → Gal(𝓜_∞⁺/𝓛_∞⁺) → 0`. *(the missing input)*
3. Splice 1+2 via the third isomorphism theorem to get the four-term sequence
   `0 → 𝓔_{∞,1}⁺/𝒞_{∞,1}⁺ → 𝒰_{∞,1}⁺/𝒞_{∞,1}⁺ → 𝒳_∞⁺ → 𝒴_∞⁺ → 0`. *(elementary)*
4. Coinvariants ([Wa97, Prop 13.22]): `(𝒴_∞⁺)_{Γ_n} ≅ A_n⁺`; with Vandiver + Nakayama ⟹ `𝒴_∞⁺ = 0` and `𝓔_{∞,1}⁺/𝒞_{∞,1}⁺ = 0`. *(have the ingredients: unramified CFT + Nakayama + class-number index)*
5. Hence `𝒳_∞⁺ ≅ 𝒰_{∞,1}⁺/𝒞_{∞,1}⁺ ≅ Λ(𝒢⁺)/I(𝒢⁺)ζ_p` by Iwasawa's theorem. *(have Iwasawa's theorem)*

So **step 2 is the sole obstruction.** It is the local-global reciprocity isomorphism `𝒰_{∞,1}⁺/𝓔_{∞,1}⁺ ≅ Gal(𝓜_∞⁺/𝓛_∞⁺)` — the statement that semi-local units modulo global units compute the Galois group of the maximal-abelian-unramified-outside-p extension. It is what binds the analytic side (units, where `ζ_p` lives) to the arithmetic module `𝒳_∞⁺`.

## 5. The state of the art (for orientation)

The Main Conjecture has two classical proofs: Mazur–Wiles (Eisenstein ideal / modular curves) and Kolyvagin–Rubin–Thaine (Euler systems). RJW present Iwasawa's original *conditional* (Vandiver) argument via the sequences above. All standard treatments we know route the "arithmetic side" through class field theory in some form; our question is which **form** is unavoidable for a formalisation, given that we already possess unramified CFT, explicit local reciprocity (Coleman), the Euler-system machinery at finite level, and Chebotarev.

## 6. Where we're stuck (the precise obstruction)

**Stuck point.** We need `0 → 𝓔_{∞,1}⁺ → 𝒰_{∞,1}⁺ → Gal(𝓜_∞⁺/𝓛_∞⁺) → 0` (step 2 above). Building it the "textbook" way means formalising ramified global CFT (ray class groups, conductors, Artin reciprocity for ramified abelian extensions) — a very large undertaking absent from Mathlib and the monorepo. We want to avoid that. The structural observations that make us optimistic:

- The only ramification involved is **at p**, and the tower is completely explicit. The map `𝒰_{∞,1}⁺ → Gal(𝓜_∞⁺/𝓛_∞⁺)` is a (semi-)local Artin map. We *have* explicit local reciprocity in the form of the **Coleman map** and the Coates–Wiles homomorphisms.
- We *have* the entire `𝒴`-side (class groups ↔ unramified extensions) via Hilbert 94.
- We *have* the Euler-system/Thaine machinery (finite level) and Chebotarev.
- RJW §13.4 themselves reformulate `𝒳_∞⁺` as a **Selmer group** (Greenberg), defined purely by **local conditions on Galois cohomology** — and `H¹` is comparatively tractable to formalise.

## 7. Questions for the reviewer

**Q1 (avoid the input, keep the `𝒳⁺` formulation).** The obstruction is the global reciprocity map `𝒰_{∞,1}⁺/𝓔_{∞,1}⁺ → Gal(𝓜_∞⁺/𝓛_∞⁺)`. Since ramification is only at p and we have the Coleman map / explicit local reciprocity and the unramified `𝒴`-side, is there a **semi-local** construction of this isomorphism that bypasses general ramified global CFT? Concretely: can `Gal(𝓜_∞⁺/𝓛_∞⁺)` be obtained as (the Λ-dual of, or directly as) a quotient of semi-local units via the Coleman/Coates–Wiles map and Kummer theory at p, with the global input limited to the unramified part (Hilbert 94) and a finiteness/Chebotarev argument? If so, what is the cleanest such formulation, and what reference carries it out in that style?

**Q2 (wholesale reformulation, minus side).** Is it cleaner to prove the Main Conjecture entirely on the `𝒴`-side, which we already have via unramified CFT? I.e. prove the **minus-part** Main Conjecture `ch_{Λ(𝒢⁻)}(𝒴_∞⁻) = (` Stickelberger / θ-element `)` (or its Λ-adjoint) via the Euler system of Gauss sums or cyclotomic units, then transfer to the plus-part statement about `𝒳_∞⁺` by reflection (Spiegelung) / Iwasawa-adjoint duality. Does this route ever need the ramified sequence of step 2, or only: (i) `𝒴_∞ ≅ lim A_n` (unramified CFT — have), (ii) the Euler-system divisibility, (iii) the analytic class-number formula / unit index (have)? What is the cleanest reference for the minus-MC ⟹ plus-MC transfer at the level of Λ-modules, and is that transfer itself CFT-dependent?

**Q3 (Euler-system route, full IMC).** The monorepo has Thaine's theorem and Kolyvagin-derivative machinery at finite level. In the Kolyvagin–Rubin–Thaine proof of the *full* Main Conjecture, is the ramified sequence (step 2) used at all, or does that proof produce `ch(𝒳_∞⁺) | I(𝒢⁺)ζ_p` (and the reverse via the class-number formula) using only the Euler-system bound on class groups (`𝒴`-side) plus Iwasawa's index theorem? Put differently: can one prove the Main Conjecture **without ever forming the ramified extension `𝓜_∞⁺`** — working only with class groups, units, and the characteristic-ideal formalism we have?

**Q4 (genuine necessity vs. expository choice).** Is the ramified-CFT input intrinsic to the Main Conjecture *as a statement about `𝒳_∞⁺`*, or an artifact of RJW's exposition (following [CS06, §4.5])? Which standard reference reaches the Main Conjecture with the *least* class-field-theory overhead — and in particular, is there a treatment a formaliser should prefer precisely because it minimises the global-CFT surface?

**Q5 (Selmer/Greenberg reformulation).** RJW §13.4 recasts `𝒳_∞⁺` as a Greenberg Selmer group, defined by local conditions on `H¹(F_∞⁺, ·)`. Since Galois cohomology `H¹` is far more tractable to formalise than ramified ray-class CFT: can the Main Conjecture be set up so that the arithmetic side **is** a Selmer group by definition, with the bridge to units provided by Poitou–Tate / local Tate duality and the Coleman map, rather than by the reciprocity sequence of step 2? What is the minimal cohomological input (which duality statements, at which generality) such a route requires, and is any of it within reach of `groupCohomology` + explicit local computations?

**Q6 (if we must axiomatise).** Supposing we accept the single sequence of step 2 as an axiom (a clearly-labelled hypothesis bundling [Wa97, Cor 13.6]) and prove everything else: is that an honest and standard "black box" to take for an Iwasawa-theory formalisation at this stage, in your judgement — i.e. is step 2 the *right* place to draw the formalised/assumed boundary, or is there a smaller / more fundamental statement we should be assuming instead?

## 8. Document metadata

- Project: cyclotomic Iwasawa Main Conjecture (Lean 4 / Mathlib; RJW arXiv:2309.15692 §13).
- Brief generated: 2026-06-18.
- Build status: analytic side + Λ-structure theory + isotypic/characteristic-ideal API compile cleanly (sorry-free, axiom-clean); Galois side (Stage G) decomposed into tickets, blocked on the step-2 input above.
- The mechanised inventory in §3 is current as of this date.
