# Review brief — Arithmetic moduli of elliptic curves and modular curves: full-programme status and statement-drift audit

*Prepared 2026-07-07 for the reviewer of the v8 (Weierstrass-atlas/quotient-stack) round. Self-contained: no repo access required. This is the second full brief; where it references your earlier advice it restates the relevant content.*

## 1. Goal

We are formalising, in Lean 4 over mathlib, the arithmetic theory of modular curves in the style of Katz–Mazur, following the concrete road-map of Buzzard's "Rough notes on modular curves" and Loeffler's lecture notes. The programme's headline targets are:

1. **Y₁(N) and Y(N) as fine moduli schemes**: for N ≥ 4 (resp. N ≥ 3) and N invertible on the base, the moduli problems "elliptic curve + point of exact order N" (resp. "+ full level-N structure") are representable by smooth affine curves.
2. **The twisted modular curve Y(ρ̄)**: for a continuous representation ρ̄ : Gal(ℚ̄/ℚ) → GL₂(ℤ/N) with cyclotomic determinant and a pairing normalisation, the moduli problem of elliptic curves with ρ̄-twisted level structure is representable over ℚ (Buzzard p. 33). This is the destination of the programme's "F stream".
3. **The moduli stack**: following your v8 guidance, the moduli of elliptic curves is organised as a concrete quotient stack [U/G], where U is the affine scheme of nonsingular Weierstrass equations and G is the coordinate-change group, with the abstract (genus-one-fibration) description demoted to a later comparison theorem.

The purpose of THIS brief is threefold: (a) a **statement-drift audit** — we reproduce the definitions and the statements of everything we have proved or frozen, in mathematical language and (in the appendix) in the exact formal syntax, so you can check that nothing has drifted from the intended mathematics; (b) a **status check across all work streams** after roughly two weeks of parallel execution; (c) **strategy and priority confirmation** post-v8.

## 2. Background, conventions, references

### 2.1 Setting

Everything is over schemes; "elliptic curve over S" is a datum (E, π : E → S, z : S → E) with π z = id. The definition of record (your v8 recommendation, now implemented) is **locally Weierstrass**: every point of S has an affine open neighbourhood U = Spec R and a Weierstrass equation W over R with an isomorphism of the restriction E|U ≅ ProjModel(W) over U carrying the section to the point at infinity, where ProjModel(W) denotes the projective plane model Proj R[X,Y,Z]/(W-homogeneous) of the Weierstrass cubic. The predicate additionally requires the discriminant Δ(W) to be a unit (equivalently, smoothness).

Notation fixed throughout:
- [N] : E → E is multiplication by N for the group structure on E over S; E[N] is its kernel, a closed subscheme of E.
- μ_N = Spec R[T]/(T^N − 1) over a base ring R, the group scheme of N-th roots of unity.
- A **Drinfeld ℤ/N-structure** (Γ₁(N)-structure) on E/S is a section P of *exact order N*: the **degree-N** Cartier divisor Σ_{a ∈ ℤ/N} [aP] is a subgroup-scheme divisor of E (Deligne's exact-order condition — this divisor has degree N, so it is a subgroup divisor, **not** an equality with the degree-N² divisor E[N]); a **full level-N structure** (Γ(N)-structure) is a pair (P,Q) with the **degree-N²** divisor Σ_{(a,b) ∈ (ℤ/N)²} [aP+bQ] = E[N] as Cartier divisors (Katz–Mazur Ch. 1 & 3 formulation via "full sets of sections").
- Gal(ℚ̄/ℚ) denotes the automorphism group of a fixed algebraic closure with the Krull topology; ℚ^sep ⊂ ℚ̄ the separable closure (equal to ℚ̄ in characteristic zero — the formalisation distinguishes the two *types* and carries an explicit continuous isomorphism between the two Galois groups).

### 2.2 References

- [KM] N. Katz, B. Mazur. *Arithmetic Moduli of Elliptic Curves.* Annals of Mathematics Studies 108, Princeton University Press, 1985. (Chapters 1–4 are the backbone: full sets of sections; Drinfeld structures; E[N] finite locally free of rank N²; relative representability and rigidity.)
- [Buz] K. Buzzard. *Rough notes on modular curves* (unpublished course notes). Pages 30–34 are the specification for the ρ̄-twisted curve Y(ρ̄).
- [Loe] D. Loeffler. *Modular curves* (LSGNT/TCC lecture notes). Prop 3.3.4 (Tate normal form), Prop 3.8.3 (rigidity for N ≥ 3), §3.6 (étale descent of morphisms).
- [GME] H. Hida. *Geometric Modular Forms and Elliptic Curves*, 2nd ed. World Scientific, 2012. §1.9–1.10, §2.1–2.2 (cohomology & base change; duality/RR for relative curves; the Weierstrass atlas computation).
- [Sil] J. Silverman. *The Arithmetic of Elliptic Curves*, 2nd ed. GTM 106, Springer, 2009. (III.1–III.6: Weierstrass forms, group law, torsion counting.)
- [DR] P. Deligne, M. Rapoport. *Les schémas de modules de courbes elliptiques.* In Modular Functions of One Variable II, LNM 349, Springer 1973.
- [SGA1] A. Grothendieck. *Revêtements étales et groupe fondamental.* LNM 224, Springer 1971. Exposé V (Galois categories) — the axiomatics implemented for the F stream.
- [Len] H. W. Lenstra. *Galois theory for schemes* (course notes) — the (G1)–(G6) axiom list used by the formal Galois-category framework.
- [Con] B. Conrad. *Arithmetic moduli of generalized elliptic curves.* J. Inst. Math. Jussieu 6 (2007) — background for the compactified theory (out of scope this phase).

### 2.3 Where this sits

The classical results are all known; the formalisation questions are about *statement selection and architecture*. Mathlib (2026) has: affine Weierstrass curves and their group law over fields and rings; the coordinate-change group; schemes, morphism properties (finite, flat, étale, smooth of relative dimension d), fibre products; Galois categories with fiber functors and fundamental groups (abstract); the Krull topology and its compactness for infinite Galois groups; finite étale algebras over a field with the fiber functor to finite sets (added to mathlib this spring by an active contributor whose development we consume and extend). Mathlib does **not** have: relative (scheme-level) elliptic curves, Cartier divisors as a mature API, Drinfeld level structures, the étale fundamental group of Spec k as an instance of the Galois-category machinery (we built exactly this), coherent cohomology / base change / Riemann–Roch for relative curves.

## 3. Post-v8 strategy (as executed)

Your v8 staging correction was adopted wholesale and is now reflected in the code and the board:

1. **`LocallyWeierstrass` is the definition of record** for elliptic curves over a base (the abstract fibrewise definition is retained only as a derived predicate/goal of a later comparison). Its base-change stability is proved.
2. **Stream W** (new): the universal Weierstrass atlas U = Spec ℤ[a₁,…,a₆][Δ⁻¹], the coordinate-change group G as a group action, quotient-stack vocabulary [U/G] with the torsor description of its groupoid of points; M_ell^W := [U/G]. Group law and [N] to come from mathlib's Weierstrass charts + descent (T-W7), NOT from Abel/Pic⁰; Abel canonicity (T-A6) is off the critical path, parked in the parallel COH stream.
3. **Cartier/Drinfeld machinery (Stream D)** proceeds unchanged — it cuts out the level loci.
4. **The F stream** (Y(ρ̄)) was unblocked by a self-contained sub-development: we implemented the full **Grothendieck–Galois correspondence for a field** inside the project (on top of mathlib's finite-étale-algebra fiber functor), obtaining the equivalence (FiniteÉtale k)^op ≃ (continuous finite Gal(k^sep/k)-sets) for every field k, and then CONSTRUCTED V_ρ̄ := Spec of the algebra corresponding to the ρ̄-twisted (ℤ/N)² — with its ℚ̄-points description, the Galois-equivariance of that description, finite-étaleness, and (this week) the scheme-level addition morphism. The registered "data sorry" DS5 for V_ρ̄ is discharged: V_ρ̄ is a real construction, not an axiom.

The five-lane worker fleet (A foundations / B torsion / D Drinfeld / E moduli+representability / F twisted curve, plus the new Q quotients and H levels and W atlas lanes) has run in parallel throughout; the board's dependency discipline (statements frozen first, proofs backfilled; explicit named black boxes) is unchanged from the last brief.
## 4. The definitions (drift-audit part I)

Each definition below is stated as the code states it (mathematically rendered; exact formal text in Appendix A). Definitions marked ◆ are the ones whose exact form carries mathematical risk and deserve your closest reading.

**Definition 4.1 (elliptic curve over a scheme; the v8 definition of record). ◆**
The definition is layered. The *geometric datum* over a scheme S consists of: a total space E, a structure morphism π : E ⟶ S, a section zero : S ⟶ E with zero ∘ π-compatibility (zero ≫ π = id); the properties *smooth of relative dimension 1* and *proper* (kept as fields although derivable — the deliberate redundancy pattern); and the **local-model condition**: π is *locally Weierstrass*, i.e. for every point s of S there exist an affine open U ∋ s, a Weierstrass equation W over Γ(U) with unit discriminant, and a pointed U-isomorphism E|_U ≅ ProjModel(W) carrying zero to the point at infinity. An *elliptic curve* is the geometric datum together with `grp`: a group-object structure on (E, π) in schemes over S (addition, unit = zero, inverse, group laws as scheme identities), with commutativity and unit-equals-zero recorded as proved base-change-stable properties.
*(Provenance note: until v7 the geometric layer instead carried "geometrically connected genus-one fibres" data; per your v8 instruction the fibrewise condition is now a derived predicate — `fibrewiseElliptic`, proved FROM the local-model field — with the converse deferred to the Phase-4 comparison T-W-cmp.)*

**Definition 4.2 (the projective Weierstrass model).**
For a Weierstrass equation W over a commutative ring R, ProjModel(W) is Proj of R[X,Y,Z] by the homogeneous ideal generated by the homogenised Weierstrass cubic. It comes with: the structure morphism to Spec R; the section at infinity [0:1:0]; and the *universal property of points* (Theorem 5.3 below) identifying its sections over an R-algebra with the affine Weierstrass solutions plus infinity. `IsWeierstrassModel` is the predicate on (E, π, z) over Spec R recording a pointed R-isomorphism to ProjModel(W).

**Definition 4.3 (multiplication by N; torsion subscheme).**
[N] : E ⟶ E is the N-fold sum built from the group data; E[N], written `torsion N`, is the equalizer/pullback of [N] against the zero section — a closed subscheme of E with structure map `torsionπ : E[N] ⟶ T`, with its ideal sheaf `torsionIdeal` recorded. The *points functor*: for t : Spec K ⟶ T, E.Point t is the set of lifts Spec K ⟶ E over t; N-torsion points are those killed by [N] in the evident sense.

**Definition 4.4 (μ_N and the constant group (ℤ/N)).**
μ_N over R is Spec R[T]/(T^N − 1) with its Hopf structure; the wiring to mathlib's roots-of-unity and the (ℤ/N)-constant group scheme (as Spec of the function algebra ℤ/N → R) is fixed once and consumed everywhere. The rank of μ_N is N, and μ_N is étale iff N is invertible (proved).

**Definition 4.5 (full set of sections; Drinfeld structures). ◆**
Following KM 1.8: for a finite locally free T-scheme Z of rank N and sections P₁,…,P_N of Z, "(Pᵢ) is a *full set of sections* of Z" means: for every affine T′ → T and every function f on Z_{T′}, the characteristic polynomial of multiplication-by-f on the (locally free rank-N) pushforward algebra equals ∏ᵢ (X − f(Pᵢ)). (Equivalently, the Cartier divisor Σᵢ[Pᵢ] equals Z as a divisor — the charpoly form is the definition of record; the divisor form is a proved reformulation, and over a *reduced* base the pointwise criterion KM 1.9.2 is proved.)
A *Drinfeld Γ₁(N)-structure* on E/T is a section P of *exact order N* (KM 1.4.1): the **degree-N** Cartier divisor Σ_{a ∈ ℤ/N} [aP] is a **subgroup divisor** of E — this is `IsGammaOne` = `HasExactOrder` in the code, `(orderDivisor P N).IsSubgroup E`, a subgroup divisor of degree N, **not** an equality with the degree-N² divisor E[N]. (The public record additionally requires the global killing clause N·P = 0; the code carries an adversarial-fix note that omitting it makes the moduli functor strictly larger than h_{Y₁(N)}.) A *full level-N (Γ(N)-)structure* is (P,Q), both killed by N, with the **degree-N²** divisor Σ_{(a,b) ∈ (ℤ/N)²} [aP+bQ] equal to E[N] (`IsFullLevel`: the N² sections aP+bQ are a full set of sections of E[N]/T). The comparisons "Drinfeld = naive (a group isomorphism (ℤ/N)² ≅ E[N] on points) when N is invertible" are proved in the Γ(N), Γ₁(N) and étale-criterion forms (KM 1.4.4 (1)⇔(3)⇔(4), Theorem 5.7).

**Definition 4.6 (moduli problems; relative representability; rigidity).**
A *moduli problem* is a contravariant functor on elliptic-curves-over-schemes (implemented on the category whose objects are pairs (T, E/T)); `RelativelyRepresentable` and `Rigid` are as in KM 4.2/4.3 — for each E/T the relative problem is representable by a T-scheme, and (rigidity) the only automorphism of E/T fixing a level structure is the identity. The set-valued problem is complemented (Stream W, in progress) by a groupoid-valued variant so that M_ell is not pretended to be set-valued.

**Definition 4.7 (the Galois-representation datum for Y(ρ̄)). ◆**
GalQ := Aut_ℚ(ℚ̄) with the Krull topology. A datum D consists of:
- ρ : GalQ → GL₂(ℤ/N), a group homomorphism;
- continuity in the form: ker ρ is open;
- cyclotomic determinant: det∘ρ equals the mod-N cyclotomic character of ℚ (mathlib's `modularCyclotomicCharacter`, fed by the proved count |μ_N(ℚ̄)| = N);
- a pairing normalisation p : ℤ/N ≅ μ_N(ℚ̄) (written multiplicatively) which is Galois-equivariant when ℤ/N carries the action through the cyclotomic character — Buzzard's "alternating Gal-equivariant perfect pairing to μ_N", rendered as the equivariant identification of Λ²(ρ) with μ_N.

**Definition 4.8 (the twisted torsor V_ρ̄ and its structure). ◆**
Let Ω := the separable closure of ℚ (a subfield of ℚ̄; in char 0 the inclusion is an isomorphism and the code carries the explicit continuous group isomorphism Gal(Ω/ℚ) ≅ GalQ). The *ρ̄-twisted Galois set* is (ℤ/N)² as a finite discrete set with the continuous Gal(Ω/ℚ)-action through ρ (kernel open ⟹ continuous). Then:
- V_ρ̄ := Spec A_ρ̄, where A_ρ̄ is the finite étale ℚ-algebra corresponding to the twisted Galois set under the Galois correspondence of §6.3 (the equivalence's inverse applied to the twisted set);
- the structure morphism V_ρ̄ ⟶ Spec ℚ is Spec of the algebra unit;
- addition: the twisted set's coordinatewise addition is Galois-equivariant (ρ(σ) acts linearly), giving a morphism of Galois sets; transporting through the correspondence and identifying the product's algebra with A_ρ̄ ⊗_ℚ A_ρ̄ (§6.3) yields the *comultiplication* A_ρ̄ → A_ρ̄ ⊗ A_ρ̄ and thence the addition morphism V_ρ̄ ×_ℚ V_ρ̄ ⟶ V_ρ̄ (zero and negation analogous, in progress).

**Definition 4.9 (ρ̄-level structures and the twisted moduli problem).**
For an elliptic curve E over a ℚ-scheme T: a *ρ̄-level structure* is an isomorphism of T-schemes E[N] ≅ V_ρ̄ ×_ℚ T over T, subject to (i) coordinate-compatibility: through the ℚ̄-points description of V_ρ̄, the induced coordinates of ℚ̄-valued torsion points are recorded by the `coord` function; and (ii) the pairing compatibility relating the Weil pairing of x,y to p(a₁b₂ − a₂b₁) of their coordinates — the latter held as a frozen relation (T-F3) pending the C-stream's pairing of record. `RepresentsYRho` packages: a smooth affine relative curve Y → Spec ℚ whose T-points are naturally the isomorphism classes of pairs (E, ρ̄-level structure), where isomorphisms must match coordinates. Representability (T-F4) and geometric irreducibility (T-F5) are the frozen phase-3 milestones.

**Definition 4.10 (quotient/atlas layer; Stream Q and W vocabulary).**
Spec-side group actions: an action of a finite group G on Spec A is recorded by an action on A; the invariants inclusion A^G ↪ A induces Spec A ⟶ Spec A^G, and the proved universal property (Theorem 5.9) is that this is the categorical quotient among affine targets, compatibly with localization at invariant elements. The W-stream vocabulary (in progress, Q-lane): G-torsors over a base, the trivialization functor from G-sets, its faithfulness, clopen decomposition of components — building to the [U/G] groupoid description: maps S → [U/G] are G-torsors P → S with an equivariant P → U.

## 5. Established results (drift-audit part II — statements with sketches)

Ordered mathematically. Every item is kernel-checked; "modulo boxes" flags consumption of §8 boxes.

**Theorem 5.1 (Tate normal form, over any commutative ring).** Let W be a Weierstrass equation over R with Δ(W) a unit, and (x,y) a solution such that the section it defines is nowhere of order ≤ 3 (unit-condition on ψ₂ψ₃-evaluation). Then there is a unique coordinate change v with (v•W) in Tate normal form (a₃ = a₂, a₄ = a₆ = 0 normalisation) fixing the section's image at the origin.
*Sketch.* Translate (x,y) to (0,0); the not-2-torsion unit condition gives the tangent-slope shear killing a₄; not-3-torsion makes a₂ a unit, and scaling by u = a₂/a₃ reaches a₂ = a₃. Uniqueness: a coordinate change between two Tate forms fixing the origin forces u = 1, r = s = t = 0 by comparing coefficients. All literal ring algebra; no locality. ∎

**Theorem 5.2 (the universal Tate curve represents, ring level).** Ring homomorphisms from the Tate coefficient ring ℤ[b,c][Δ⁻¹] to A correspond exactly to pairs (b,c) ∈ A² with unit discriminant; combined with 5.1 this is the ring-level core of Y₁(N)-representability.
*Sketch.* Polynomial universal property + localization away from Δ. ∎

**Theorem 5.3 (points of the projective model).** For a Weierstrass equation W over R and an R-algebra, sections of ProjModel(W) correspond exactly to: affine solutions of W, plus the point at infinity — i.e. the model's functor of points is the Weierstrass points functor. (This is the content making Definition 4.2 usable; proved via a three-chart analysis with the Z-chart carrying the affine curve and the X/Y-charts contributing only infinity.)

**Theorem 5.4 (smoothness ⟺ unit discriminant).** ProjModel(W) → Spec R is smooth if and only if Δ(W) is a unit.
*Sketch.* Chartwise standard-smooth presentations of the localized hypersurfaces; the Jacobian ideal of the Weierstrass cubic is comaximal with the cubic exactly when Δ is invertible (certificate-free comaximality computation), and smoothness glues along the three charts. ∎

**Theorem 5.5 (base change).** The formation of ProjModel commutes with base change (with the comparison map an isomorphism); `LocallyWeierstrass` is stable under base change; fibres of a pullback along a residue-field extension are the base-changed fibres; and the group-structure Props (commutativity, unit) are preserved. Consequently E ×_T T′ is again an elliptic curve in the sense of 4.1.

**Theorem 5.6 (E[N] structure; modulo boxes).** E[N] ⟶ T is: a closed immersion into E (unconditional); finite locally free of rank N² (modulo BB-QF/FLAT/DEG); étale when N is invertible (modulo the same boxes plus BB-DIFF).
**Theorem 5.6′ (geometric fibres; the counting route — unconditional given the boxes' fibre inputs).** Over an algebraically closed field k with N invertible, E[N](k) ≅ (ℤ/N)² as abelian groups.
*Sketch (self-contained, replaces the earlier plan of importing a sibling development).* (i) For a finite étale k-algebra with k separably closed, the number of k-points of its Spec equals its k-dimension ("sections = rank", proved from the classification of étale algebras as finite products of copies of k). (ii) The N-torsion algebra has the right dimension and the multiplication-by-M kernels have sizes M² by degree counting. (iii) A finite abelian group killed by N in which every m | N has exactly m² solutions of mx = 0 is (ℤ/N)² — proved by CRT-reduction to prime powers and a two-generator pigeonhole. ∎

**Theorem 5.7 (Drinfeld ⟺ naive, KM 1.4.4; modulo BB-DELIGNE where marked).** For N invertible on T: a pair (P,Q) of N-torsion sections is a full level-N structure iff the induced map (ℤ/N)² → E[N] is an isomorphism of group schemes iff the étale-local criterion holds ((1)⇔(3)⇔(4)); a section of exact order N is killed by N (KM 1.4.2; modulo BB-DELIGNE); the Γ₁ and Γ forms are proved, the Γ₀ (fppf-local cyclicity) statement is frozen with its proof gated on quote-mining KM 6.1.
*Sketch.* The charpoly definition is compared with the divisor form; over reduced bases the pointwise criterion (KM 1.9.2, proved: a family is a full set of sections iff it exhausts geometric fibres with multiplicity) reduces to fibre counting; étale-locally E[N] is constant and the comparison is the finite-abelian-groups statement 5.6′(iii). ∎

**Theorem 5.8 (moduli-functor foundations).** The Ell-category plumbing (base-change functoriality of elliptic curves; the moduli problems Γ(N)/Γ₁(N)/Γ_H as functors) satisfies the functor laws; relatively representable moduli problems are fppf-separated (an injectivity-of-restriction statement along fppf covers, proved via flat-epimorphism cancellation).

**Theorem 5.9 (affine quotients, Stream Q).** For a finite group G acting on a commutative ring A: Spec(A^G) has the universal property of the categorical quotient of Spec A among affine schemes; the invariants inclusion localizes correctly at invariant elements (the fixed elements of a localization come from invariants over a power; the localized inclusion is again an invariants inclusion). This is the algebraic core the [U/G]-layer builds on.

**Theorem 5.10 (rigidity input, Stream H, in progress).** The GL₂(ℤ/N)-action on full level structures is total (proved); the current sub-development shows full level is *not* rigid for N ≤ 2 by exhibiting [−1] ≠ id: on a fibre with a geometric point, odd torsion (order-3 or -5 points, via the fibre count 5.6′) separates [−1] from the identity; combined with the existence of geometric points on nonempty ℚ-schemes this yields the honest non-rigidity statement (completing).

## 6. The Grothendieck–Galois tower and V_ρ̄ (drift-audit part III — the F-stream's new mathematics)

This is the largest single addition since the last brief: a complete, kernel-checked implementation of the Galois correspondence for a field, culminating in the construction of V_ρ̄. Everything in this section is proved with the standard three axioms only — there are no boxes and no sorries anywhere in the tower.

### 6.1 The Galois category of finite étale algebras

Fix a field k. Work in the opposite of the category of finite étale k-algebras (finite-dimensional, étale commutative k-algebras; morphisms are k-algebra maps).

**Theorem 6.1.1 (PreGaloisCategory, axioms G1–G3 of [SGA1 V]/[Len 3.1]).** The opposite category of finite étale k-algebras has: a terminal object (k itself, initial among algebras); pullbacks (pushouts of algebras = tensor products, constructed with their universal property); finite coproducts (finite products of algebras); quotients by finite group actions (fixed-point subalgebras — for ANY finite monoid action, via the fixed subalgebra being étale); and every monomorphism is the inclusion of a direct summand.
*Sketch of the last (the substantive axiom).* A mono in the opposite is an epi of algebras; epis of finite étale algebras are **surjective** — proved by a counting pigeonhole: # Hom_k(A, k^sep) = dim_k A for étale A (base-change to the separable closure plus "sections = rank"), and a non-surjective epi would factor points through a proper subalgebra of strictly smaller dimension, contradicting the epi property via two distinct k^sep-points agreeing on the range (they generate a common finite étale subfield of k^sep, providing the contradicting parallel pair). Its kernel is then complemented: a finite étale algebra is semisimple (artinian + reduced), every ideal is idempotent-generated and radical, so A ≅ A/I × A/J by CRT with both factors étale (étale passes to arbitrary quotients — every ideal is complemented, hence radical, hence the quotient is reduced with separable elements). ∎
Along the way, three self-standing algebra results (stated at mathlib generality): *every element of a finite étale algebra over a field is separable*; *subalgebras of finite étale algebras are étale*; *quotients of finite étale algebras are étale*.

**Theorem 6.1.2 (FiberFunctor, axioms G4–G6).** The functor F = Hom_k(−, Ω), Ω = k^sep, from the opposite category to finite sets, is a fiber functor: it preserves terminal objects, pullbacks, finite coproducts, epimorphisms, and quotients by finite groups, and reflects isomorphisms.
*Sketch.* mathlib supplies F together with the natural isomorphism F ≅ (base change to Ω) ∘ (fiber functor of Ω), and the Ω-level fiber functor is an equivalence for separably closed Ω. Hence every exactness property reduces to one for the base-change functor A ↦ Ω ⊗_k A, proved directly: it preserves the initial object (Ω ⊗ k ≅ Ω), finite products (Ω ⊗ ∏Aᵢ ≅ ∏(Ω ⊗ Aᵢ)), tensor pushouts (associativity of ⊗, via the universal property), monomorphisms (monos of finite étale algebras are injective — the kernel-pair is an étale subalgebra of the square whose two projections are equalised — and flat base change preserves injectivity), and fixed points of finite monoid actions (fixed points are the equalizer of the action against the diagonal, and flat base change commutes with equalizers). Reflection of isomorphisms is again counting: a map inducing a bijection on Ω-points has zero kernel and full range by comparing dimensions. ∎

### 6.2 The fundamental group

**Theorem 6.2.1 (IsFundamentalGroup).** Gal(Ω/k) = Aut_k(Ω) with the Krull topology (compact by mathlib's profinite theory, using that Ω/k is Galois) acts naturally on the fibers F(A) = Hom_k(A, Ω) by post-composition, and this exhibits it as *the* fundamental group of the fiber functor in the sense of the mathlib Galois-category framework: the action is continuous on each (discrete) fiber — stabilizers are the fixing subgroups of the finite subextensions given by images of points, which are open; it is transitive on the fibers of connected objects; and only the identity acts trivially on all fibers.
*Key inputs.* (i) **Connected finite étale algebras over k are fields**: a connected object has nontrivial idempotent-free coordinate ring; quotienting by a maximal ideal gives an étale field quotient whose corresponding mono must be an isomorphism by connectedness. (ii) **Transitivity = conjugacy of embeddings**: two k-embeddings of a finite subextension into Ω are conjugate by an automorphism of Ω, via the normal-extension lifting theorem applied to the isomorphism between their images. (iii) Non-triviality: an automorphism fixing all fibers fixes every finite subextension k(ω), hence every ω. ∎

### 6.3 The correspondence, and V_ρ̄

**Theorem 6.3.1 (the Galois correspondence).** For every field k there is an equivalence of categories between (finite étale k-algebras)^op and (finite discrete sets with continuous Gal(k^sep/k)-action). It is the composite of mathlib's equivalence with the automorphism group of the fiber functor (available once 6.1–6.2 hold) with restriction along the comparison isomorphism of topological groups between Gal(k^sep/k) and that automorphism group.

**Construction 6.3.2 (V_ρ̄; Definition 4.8 realised).** Given a datum D (Definition 4.7): the ρ̄-twisted (ℤ/N)² is a continuous Gal(ℚ^sep/ℚ)-set (kernel of ρ open; the char-0 comparison isomorphism transports the GalQ-action); A_ρ̄ := the corresponding algebra; V_ρ̄ := Spec A_ρ̄ with structure map to Spec ℚ. Then, all proved:
- **(T-F1a)** V_ρ̄ ⟶ Spec ℚ is finite and étale.
- **(T-F1b, points)** The set of Spec ℚ̄-points of V_ρ̄ over Spec ℚ is in bijection with (ℤ/N)² — the bijection being: points = ℚ-algebra maps A_ρ̄ → ℚ̄ = (via the char-0 comparison and the correspondence's counit) the twisted set itself.
- **(T-F1b, equivariance)** The bijection is Galois-equivariant: precomposing a point with (Spec of) σ ∈ GalQ corresponds to acting by ρ(σ) on (ℤ/N)². *Sketch:* three layers — translated points correspond to post-composed algebra maps; the char-0 comparison conjugates the actions; the correspondence counit is equivariant because it is a morphism of continuous Galois sets. ∎
- **(T-F1c, group structure — addition done)** Coordinatewise addition on the twisted set is equivariant (linearity of ρ(σ)); the twisted square is the categorical product of Galois sets; transport through the correspondence identifies its algebra with A_ρ̄ ⊗_ℚ A_ρ̄ (the tensor product is the coproduct of finite étale algebras — proved); Spec of the resulting comultiplication, composed with the standard pullback-of-Spec ≅ Spec-of-tensor isomorphism, is the addition morphism V_ρ̄ ×_ℚ V_ρ̄ ⟶ V_ρ̄. Zero and negation morphisms exist at the Galois-set level (proved equivariant); their Spec-side transport and the group laws are the remaining (mechanical) tail, after which the ρ̄-level-structure layer (Definition 4.9) can be upgraded to group-scheme isomorphisms.

**Corollary 6.3.3 (cross-stream reuse).** The C stream's characteristic-zero Weil-pairing route consumes this tower: its "descent heart" — a Galois-equivariant map of fibers comes from a unique map of finite étale algebras — is precisely full faithfulness of the correspondence, and has been instantiated and proved by the C-lane against our instances.
## 7. Programme statistics (status check)

**Code volume.** 54 formal files, ~23,600 lines, 859 public declarations (enumerated verbatim in Appendix A), organised as: foundations of relative elliptic curves (5 files), torsion & group structure, Weil pairing (3), Drinfeld/Cartier level structures (4), moduli & representability (9), the twisted curve Y(ρ̄) (2), quotient/atlas infrastructure, and a 28-file "for-mathlib" layer of general-purpose material (graded quotients, standard-smooth presentations, étale section counts, finite abelian group counting, the Galois-category instances, flat-equalizer transport, torsor vocabulary, …) written at mathlib generality for eventual upstreaming.

**Verification bar.** Everything marked "proved" below compiles with kernel-checked proofs whose axiom footprint is exactly mathlib's three classical axioms (propositional extensionality, choice, quotient soundness) — we machine-check this with axiom probes on every headline result. "Proved modulo boxes" means: kernel-checked except that the proof consumes one or more of the *registered black boxes* of §8 (each an explicitly stated unproved lemma, never a silent assumption).

**Sorry census** (unproved placeholder statements, by design of the frozen-statement workflow): 66 textual occurrences across 17 files; the real ones concentrate in (i) statement-frozen specifications awaiting their stream's proofs (Weil pairing specs, representability milestones, coarse-moduli comparisons), (ii) the registered black boxes themselves, (iii) in-flight worker scaffolding. None are hidden: each corresponds to a board ticket.

**Stream scoreboard** (done / total substantive tickets, headline items):

| Stream | State | Highlights done | Open/blocked |
|---|---|---|---|
| A foundations | ~90% of phase | Projective Weierstrass model constructed with its universal property; smooth ⟺ Δ unit; full base-change theory (model, fibres, group Props); `LocallyWeierstrass` definition-of-record swap (v8) | T-A4 **statement found FALSE** (§9.1); T-A6 canonicity parked (COH stream, per v8) |
| B torsion | done modulo boxes | μ_N wired; E[N] closed immersion; E[N] rank N² and étaleness statements; **geometric fibres of E[N] ≅ (ℤ/N)² proved via a self-contained counting route** (étale point-counts = rank; finite abelian group with the right N- and count-data is (ℤ/N)²) | the four torsion boxes BB-QF/FLAT/DEG/DIFF (§8) |
| C Weil pairing | early | char-0 étale-descent construction started by the H-lane worker **on top of the F-stream's Galois correspondence**: the descent heart (a Galois-equivariant map of fibers comes from a finite-étale-algebra map) is proved axiom-clean | scheme-level pairing of record (KM 2.8 gated), bilinearity/nondegeneracy specs open |
| D Drinfeld | far along | full sets of sections (reduced-base criterion KM 1.9.2); divisor sums; exact-order ⟹ killed (mod BB-DELIGNE); Drinfeld ⟺ naive for N invertible in the Γ(N), Γ₁(N), étale-criterion forms (KM 1.4.4); incidence/subgroup loci; charpoly form of full sections (KM 1.1.4/1.8.2) | Γ₀(N) fppf-local cyclicity (statement frozen); one base-change naturality in flight |
| E moduli | ring layer done | Tate normal form ∃! (Loe 3.3.4) over any ring; universal Tate curve represents (ring level); Ell-category and moduli-functor laws; fppf separatedness of relatively representable problems | the milestones: KM 4.7 (representable ⟺ rel.rep + rigid), Y₁(N), Y(N) representability — phase-2 targets, statements frozen |
| F twisted curve | **construction done** | The entire Grothendieck–Galois tower (§6): V_ρ̄ constructed, finite étale, points ≅ (ℤ/N)² Galois-equivariantly, scheme-level addition; DS5 discharged | pairing-compat relation (T-F3, needs C-stream), symplectic Isom-scheme (T-F6), representability of Y(ρ̄) (T-F4), irreducibility (BB-IRR) |
| Q quotients | core done | Spec-side G-action vocabulary; Spec(A^G) universal property incl. localization theory; now executing the W-stream torsor/quotient-stack layer (trivialization functor faithful, clopen component analysis) | [U/G] groupoid description (T-W3) completion |
| H levels | in progress | GL₂-action on full level structures total; non-rigidity of full level for N ≤ 2 underway ([−1] ≠ id via odd fibre torsion; geometric points of nonempty schemes) | remaining H7 sub-lemmas |

**Fleet activity**: ≈480 commits in the last ~48 hours across seven concurrent worker lanes; every commit is built green before merge into the shared branch (transient cross-lane breakage is handled by wait-and-rebuild discipline).

## 8. Registered black boxes (complete list)

Owner directive in force: only BB-RR may remain assumed; all others must eventually be proved in-project. Your v8 restaging moved the starred ones off the critical path to the open curves.

| Box | Statement (informal) | Status / consumer |
|---|---|---|
| BB-RR ★ | Grothendieck–Serre duality + (relative) Riemann–Roch for relative curves, exactly GME 2.1.2/2.1.3/2.1.6 | assumed by directive; consumers now only in the COH comparison stream |
| BB-COHBC ★ | cohomology & base change (GME 1.10.4) + Γ(E,O)=Γ(S,O) (GME 1.9.12) | COH stream only, post-v8 |
| BB-QF | [N] on an elliptic curve over a field is quasi-finite | bounded; consumed by E[N] rank |
| BB-FLAT | fibrewise flatness criterion (EGA IV 11.3.10 shape) | bounded; consumed by E[N] rank N² |
| BB-DEG | degree of [N] is N² fibrewise | bounded; same consumer |
| BB-DIFF | invariant differential / [N] étale iff N invertible input | currently *gated on a genuine mathlib gap*: no usable relative-differentials sheaf API exists yet |
| BB-DELIGNE | a finite locally free commutative group scheme of rank N is killed by N | bounded (norm argument); consumed by exact-order theory |
| BB-DESC | fppf/torsor descent of levelled elliptic curves (the cocycle-free general form was found FALSE and deleted; the torsor form stands) | consumed by stack packaging & Y(N) route |
| BB-IRR | geometric irreducibility of Y(N), Y(ρ̄) | phase-3; owner sanctioned deferring; statement is a hypothesis-carrying theorem, not an axiom |

## 9. Drift findings and decision points (the audit's own catches)

**9.1 T-A4 (KM 2.2.5, "uniqueness of the Weierstrass model") — statement was FALSE; owner decision pending.** As originally frozen, the statement said: a smooth projective S-scheme with Weierstrass-model data whose K-point cardinalities agree with E's for every field K is pointed-isomorphic to the projective model. The adversarial pass produced a counterexample: over ℚ, a 2-isogenous non-isomorphic pair (y² = x³ − 36x vs y² = x³ + 144x) has equal (infinite) point cardinalities over every characteristic-0 field, defeating the reconstruction. The KM source (2.2.5, full text mined) is in fact *uniqueness of adapted coordinates for a fixed (E, ω) up to the affine substitutions x ↦ x+a, y ↦ y+ax+b* — a different, weaker statement. The board holds this as "blocked-B2" awaiting a re-freeze. **Question 10.Q2 below asks you to confirm the correct replacement statement.**

**9.2 The abstract fibrewise definition** of elliptic curve is retained as a *predicate* (`FibrewiseElliptic`, now a theorem-target implied by `LocallyWeierstrass`, not a structure field) — matching your v8 instruction that the comparison is Phase-4.

**9.3 A previously-registered "descent" statement was deleted as false** (the cocycle-free fppf descent of levelled curves; the torsor-datum form replaces it) — caught in an earlier adversarial pass, recorded here for completeness.

**9.4 Everything else**: the statement inventory of §§4–6 and the appendix is, to our knowledge, faithful to [KM]/[Buz]/[Loe]; the point of this brief is for you to falsify that claim where you can.

## 10. Questions for the reviewer

**Q1 (drift audit — the main ask).** Please read §4–§6 (and spot-check the appendix) against the intended mathematics. Specifically: (a) Is the *locally Weierstrass* definition (4.1) exactly what you intended in v8 — in particular the pointwise ∃-neighbourhood form, the unit-discriminant normalisation, and the pointed-isomorphism-to-ProjModel packaging? (b) Do the Drinfeld/full-level definitions (4.x) match KM Ch. 1/3 — most importantly the "full set of sections" formulation and its reduced-base criterion? (c) Is the Galois-representation datum for Y(ρ̄) (4.x: continuity as open kernel; cyclotomic determinant via the mod-N cyclotomic character; the pairing normalisation p as an equivariant identification Λ²ρ ≅ μ_N) the right formal rendering of Buzzard p. 33?

**Q2 (T-A4 re-freeze).** Given §9.1, we propose to replace T-A4 by KM 2.2.5 as actually stated: for a fixed elliptic curve with chosen invariant differential (E/S, ω), adapted coordinate systems (x, y) exist Zariski-locally and are unique up to x ↦ x + a, y ↦ y + ax + b (a, b functions on the base). Two sub-questions: (i) do you endorse this as the replacement (it is what the atlas route actually consumes)? (ii) at what generality should ω enter — as a chosen trivialisation of the conormal sheaf along the zero section (our plan), or is there a lighter-weight rendering adequate for the Ch. 2 uses?

**Q3 (strategy re-check).** The post-v8 execution: Stream W is building [U/G] bottom-up (torsor description first), the group law will come from Weierstrass charts + descent (T-W7), D-stream Cartier machinery is unchanged, and the F-stream reached V_ρ̄ through a full in-project Grothendieck–Galois correspondence. Does this remain the sequencing you'd recommend, and is there anything in §5–§6 you would *stop* doing?

**Q4 (priorities).** Our reading of the critical path to Y₁(N)/Y(N): (i) finish W3/W4/W5 (atlas + action), (ii) T-W7 group law by descent, (iii) E-stream KM 4.7 + rigidity, (iv) D-stream level loci over the atlas (T-W8), with B-stream boxes (BB-QF/FLAT/DEG) discharged in parallel to de-box E[N]. Where would you put the marginal worker-lane? In particular: is discharging BB-DELIGNE early worth it (it unlocks exact-order theory unconditionally), or is it safely late?

**Q5 (mathlib generality of the for-mathlib layer).** The Galois-category work (§6.1–6.3) is stated for an arbitrary field k with values in Ω := its separable closure: PreGaloisCategory and FiberFunctor instances for finite étale k-algebras, IsFundamentalGroup for Gal(k^sep/k), and the equivalence with continuous finite Galois sets. Two generality questions before we propose upstreaming: (i) should the fiber functor be parameterised over an arbitrary separably closed geometric point Ω with a structure map (i.e. an `IsSepClosure k Ω`-style hypothesis) rather than THE separable closure — our current statements hard-code the latter, and we hit concrete-instance friction (documented) suggesting the parameterised form is more robust; (ii) is "connected finite étale algebra over a field = field" (6.2.x) with its idempotent-splitting proof the right mathlib-facing decomposition, or would you factor through the primitive-idempotent decomposition of artinian rings?

**Q6 (Weil pairing route).** The C stream's construction of record is still open. Post-v8 options: (a) KM 2.8's Cartier-divisor construction (quote-gated: we do not formalise it from memory; the full text is available); (b) the char-0-first étale-descent route now unblocked by the Galois correspondence (its descent heart is already proved); (c) a duality-based construction consuming BB-RR (would confine the pairing to the COH stream's assumptions). Given that Y(ρ̄)'s pairing-compatibility (T-F3) is the only near-term consumer and it lives over ℚ, we lean (b) then (a). Do you concur, and is there a reference you'd pin for (b) done carefully at scheme level (we know Loeffler §3.6's sketch)?

**Q7 (unanswered from v8).** The v8 round left one of our questions unaddressed: whether the coarse-moduli layer (j-line) should be built in this phase at all, or deferred entirely until after the fine curves. Our current plan defers it (only statement skeletons exist). Confirm?

## 11. Auxiliary technical results (appendix pointer)

Appendix A (following) lists the exact formal statements — every public definition and theorem of the programme, organised by stream and file, each tagged PROVED / PROVED-MODULO-BOXES / SORRY(frozen statement) / DATA. This is the drift-audit ground truth; §§4–6's prose renders the load-bearing subset.

## 12. Document metadata

- Programme: arithmetic moduli of elliptic curves / modular curves, Lean 4 + mathlib, single shared branch, multi-agent worker fleet with statement-freeze discipline.
- Brief generated: 2026-07-07. Previous brief: 2026-07-05 (answered by your v8 review; integrated same day).
- Build status at time of writing: project compiles; the frozen-statement sorries and registered boxes enumerated above are the only unproved content.
- Scale: ~23.6k lines, 859 public declarations, 54 files; ≈480 commits since the previous brief.

---

# Appendix A — the complete formal statement inventory (drift-audit ground truth)

Every public declaration of the programme, verbatim from the formal source (proof bodies omitted), organised by area. Tags: [PROVED] kernel-checked with no unproved content; [SORRY] statement frozen, proof pending (each corresponds to a board ticket or registered box); [DATA]/[DATA-SORRY] definitions (real construction / registered data-placeholder). Context lines record binder-carrying namespace/section variables. The formal names here are the ticket-board names; the prose sections above cite them where load-bearing.

# Verbatim Lean signature inventory — ModularCurves (batch A)

Scope: `projects/ModularCurves/ModularCurves/{EllipticCurve,GroupScheme,WeilPairing,LevelStructure}/`, plus `ModularCurves/Basic.lean` and the root `ModularCurves.lean`. Every top-level public `def`/`theorem`/`lemma`/`structure`/`abbrev`/`instance` is listed with its verbatim signature (binders + full statement, proof bodies omitted). `private` declarations are not listed. Status markers: [PROVED] (no sorry in body), [SORRY] (body is/contains sorry), [DATA] (def with real data body), [DATA-SORRY] (def whose body is sorry).

---

## ModularCurves.lean  (18 lines)

Root import file: imports `ModularCurves.Basic` and all `EllipticCurve`, `GroupScheme`, `LevelStructure`, `WeilPairing.Basic`, `Moduli`, and `ModularCurve.YRho` modules. No declarations.

Declarations: 0

---

## ModularCurves/Basic.lean  (33 lines)

Entry-point stub for the AINTLIB modular-curves formalisation: fixes the module root and pins the core mathlib imports (upper half plane, `SL(2,ℤ)` action, congruence subgroups); real development happens in sibling files. Contains only `namespace ModularCurves … end ModularCurves`.

Declarations: 0

---

## ModularCurves/EllipticCurve/Basic.lean  (273 lines)

The geometric record of an elliptic curve over a base scheme: `EllipticCurveGeom` (morphism smooth of relative dimension 1 and proper, a section, and the Zariski-local-Weierstrass condition as definition of record), with the fibrewise genus-1 condition kept as the derived comparison target.

Context: `open AlgebraicGeometry CategoryTheory Limits`, `universe u`, `namespace ModularCurves`.

-- The point of the fibre `π.fiber s` induced by a section `z : S ⟶ E` of `π`.
[DATA]
```lean
noncomputable def sectionFiberPoint {E S : Scheme.{u}} (π : E ⟶ S) (z : S ⟶ E)
    (hz : z ≫ π = 𝟙 S) (s : S) : Spec (S.residueField s) ⟶ π.fiber s :=
```

-- **The fibre condition** (bridge form, per expert review Q2): every fibre of `π`, pointed by the zero section, is *pointed-isomorphic as a `κ(s)`-scheme* to the projective Weierstrass model of some elliptic (unit-discriminant) Weierstrass curve over the residue field.
[DATA]
```lean
def FibrewiseElliptic {E S : Scheme.{u}} (π : E ⟶ S) (z : S ⟶ E) (hz : z ≫ π = 𝟙 S) :
    Prop :=
  ∀ s : S, ∃ W : WeierstrassCurve (S.residueField s), W.IsElliptic ∧
    ∃ e : π.fiber s ≅ projModel W,
      e.hom ≫ projModelπ W = π.fiberToSpecResidueField s ∧
      sectionFiberPoint π z hz s ≫ e.hom = projModelZero W
```

-- **(T-A5b)** Fibrewise ellipticity is stable under base change: the fibre of the pulled-back family at `t` is the fibre at `g t` extended to `κ(t)`, and the projective Weierstrass model base-changes accordingly.
[PROVED]
```lean
lemma FibrewiseElliptic.baseChange {E S T : Scheme.{u}} {π : E ⟶ S} {z : S ⟶ E}
    {hz : z ≫ π = 𝟙 S} (h : FibrewiseElliptic π z hz) (g : T ⟶ S) :
    FibrewiseElliptic (pullback.snd π g)
      (pullback.lift (g ≫ z) (𝟙 T)
        (by rw [Category.assoc, hz, Category.comp_id, Category.id_comp]))
      (pullback.lift_snd _ _ _) :=
```

-- **The local-model condition** (v2, owner-directed 2026-07-06): every point of `S` has an affine open neighbourhood `U` over which `E`, pointed by the zero section, is isomorphic — as a scheme over `Γ(S, U)` (via `U ≅ Spec Γ(S, U)`), compatibly with `π` and the section — to the projective Weierstrass model of some elliptic Weierstrass curve `W / Γ(S, U)`.
[DATA]
```lean
def LocallyWeierstrass {E S : Scheme.{u}} (π : E ⟶ S) (z : S ⟶ E) (hz : z ≫ π = 𝟙 S) :
    Prop :=
  ∀ s : S, ∃ (U : S.affineOpens) (_ : s ∈ U.1) (W : WeierstrassCurve Γ(S, U.1)),
    W.IsElliptic ∧
    ∃ e : pullback π U.1.ι ≅ projModel W,
      e.hom ≫ projModelπ W = pullback.snd π U.1.ι ≫ U.2.isoSpec.hom ∧
      (U.2.isoSpec.inv ≫ pullback.lift (U.1.ι ≫ z) (𝟙 _)
          (by rw [Category.assoc, hz, Category.comp_id, Category.id_comp])) ≫ e.hom =
        projModelZero W
```

-- **(T-A8a)** The local-model condition is stable under base change: shrink the model's affine open `U ∋ g t` to an affine `V ∋ t` inside `g⁻¹ U`, transport the Weierstrass curve `W` along `Γ(S, U) → Γ(T, V)` (`g.appLE`), and paste the pullbacks.
[PROVED]
```lean
lemma LocallyWeierstrass.baseChange {E S T : Scheme.{u}} {π : E ⟶ S} {z : S ⟶ E}
    {hz : z ≫ π = 𝟙 S} (h : LocallyWeierstrass π z hz) (g : T ⟶ S) :
    LocallyWeierstrass (pullback.snd π g)
      (pullback.lift (g ≫ z) (𝟙 T)
        (by rw [Category.assoc, hz, Category.comp_id, Category.id_comp]))
      (pullback.lift_snd _ _ _) :=
```

-- The **geometric record** of an elliptic curve over the scheme `S`: a smooth proper relative curve with a section whose fibres are (pointed) genus-1 curves, the latter expressed via `FibrewiseElliptic`.
[DATA] (structure; `EllipticCurveGeom.smooth`/`.proper` are registered as instances via `attribute [instance]`)
```lean
structure EllipticCurveGeom (S : Scheme.{u}) where
  /-- The total space. -/
  E : Scheme.{u}
  /-- The structure morphism. -/
  π : E ⟶ S
  /-- The zero section. -/
  zero : S ⟶ E
  zero_π : zero ≫ π = 𝟙 S
  smooth : SmoothOfRelativeDimension 1 π
  proper : IsProper π
  localModel : LocallyWeierstrass π zero zero_π
```

Declarations: 6

---

## ModularCurves/EllipticCurve/GroupLaw.lean  (299 lines)

The working record: elliptic curves with their commutative group-object structure in `Over S` (unit = zero section), the `[n]` endomorphisms, `T`-points and their group structure, and base change of the whole record.

Context: `open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj`; `attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory CategoryTheory.Over.braidedCategory`; `universe u`; `namespace ModularCurves`; `variable {S : Scheme.{u}}`; inside `namespace EllipticCurve`: `variable (E : EllipticCurve S)`.

-- The **working record**: an elliptic curve over `S` together with its commutative group-scheme structure, normalised so the unit is the zero section.
[DATA] (structure)
```lean
structure EllipticCurve (S : Scheme.{u}) extends EllipticCurveGeom S where
  /-- The group-object structure on `E` in `Over S`. -/
  grp : GrpObj (Over.mk π)
  /-- The group law is commutative. -/
  comm : letI := grp; IsCommMonObj (Over.mk π)
  /-- The unit of the group structure is the zero section. -/
  one_eq_zero :
    letI := grp
    (η[Over.mk π] : _ ⟶ Over.mk π).left = (𝟙_ (Over S)).hom ≫ zero
```

-- `E/S` as an object of `Over S`.
[DATA]
```lean
noncomputable abbrev asOver : Over S := Over.mk E.π
```

[DATA]
```lean
noncomputable instance grpObj : GrpObj E.asOver := E.grp
```

[DATA]
```lean
instance isCommMonObj : IsCommMonObj E.asOver := E.comm
```

-- **(T-A6b, canonicity — Abel/KM 2.1.2; deferred purity project)** Every geometric elliptic curve admits an enrichment to the working record.
[SORRY]
```lean
theorem abelEnrichment_exists (G : EllipticCurveGeom S) :
    ∃ E : EllipticCurve S, E.toEllipticCurveGeom = G :=
```

-- **(T-A6c, uniqueness — KM 2.1.2 + rigidity; deferred purity project)** The enrichment is unique: two working records with the same geometry are equal.
[SORRY]
```lean
theorem abelEnrichment_unique (E E' : EllipticCurve S)
    (h : E.toEllipticCurveGeom = E'.toEllipticCurveGeom) : E = E' :=
```

-- Multiplication by `n` on `E/S`, as an endomorphism over `S`: the `n`-th power of the identity in the group `Hom_{Over S}(E, E)` induced by the group structure.
[DATA]
```lean
noncomputable def mulBy (n : ℤ) : E.asOver ⟶ E.asOver :=
```

-- The underlying scheme morphism of `mulBy`.
[DATA]
```lean
noncomputable abbrev mulByHom (n : ℤ) : E.E ⟶ E.E := (E.mulBy n).left
```

[PROVED]
```lean
@[simp]
theorem mulByHom_π (n : ℤ) : E.mulByHom n ≫ E.π = E.π :=
```

-- The `T`-points of `E/S` along `g : T ⟶ S`: morphisms `T ⟶ E` lifting `g`.
[DATA]
```lean
abbrev Point {T : Scheme.{u}} (g : T ⟶ S) : Type u :=
  { h : T ⟶ E.E // h ≫ E.π = g }
```

-- The zero `T`-point.
[DATA]
```lean
def zeroPoint {T : Scheme.{u}} (g : T ⟶ S) : E.Point g :=
```

-- Points of `E` over `g` are the `Over S`-morphisms `Over.mk g ⟶ E.asOver`.
[DATA]
```lean
noncomputable def pointEquivOverHom {T : Scheme.{u}} (g : T ⟶ S) :
    E.Point g ≃ (Over.mk g ⟶ E.asOver) where
```

-- The additive commutative group structure on `T`-points, transported from the hom-group into the group object `E` (mathlib `Hom.commGroup`), commutativity from the `comm` field.
[DATA]
```lean
noncomputable instance pointAddCommGroup {T : Scheme.{u}} (g : T ⟶ S) :
    AddCommGroup (E.Point g) :=
```

-- `pointEquivOverHom` carries point-addition to multiplication of `Over`-homs (the transport that defines `pointAddCommGroup`).
[PROVED]
```lean
theorem pointEquivOverHom_add {T : Scheme.{u}} (g : T ⟶ S) (P Q : E.Point g) :
    letI : CommGroup (Over.mk g ⟶ E.asOver) := Hom.commGroup
    (E.pointEquivOverHom g) (P + Q) =
      (E.pointEquivOverHom g) P * (E.pointEquivOverHom g) Q :=
```

-- **(T-A6d, specification)** Scalar multiplication on points is composition with `mulBy`: `(n • P) = P ≫ [n]`.
[PROVED]
```lean
theorem point_smul_eq_comp_mulBy {T : Scheme.{u}} (g : T ⟶ S) (n : ℤ) (P : E.Point g) :
    ((n • P : E.Point g) : T ⟶ E.E) = (P : T ⟶ E.E) ≫ E.mulByHom n :=
```

-- Restriction of a point along `k : T' ⟶ T` (functoriality of the points functor).
[DATA]
```lean
def Point.restrict {T T' : Scheme.{u}} {g : T ⟶ S} (k : T' ⟶ T) (P : E.Point g) :
    E.Point (k ≫ g) :=
```

-- **(T-A5)** Base change of the working record along `g : T ⟶ S`: total space `E ×_S T`; the group structure is mathlib's group-object structure on the pullback (`Over.grpObjMkPullbackSnd`).
[DATA]
```lean
noncomputable def baseChange {T : Scheme.{u}} (g : T ⟶ S) : EllipticCurve T where
```

-- **(T-D6a-ii)** Multiplication by `n` commutes with base change: on the base-changed curve `E ×_S T`, the endomorphism `[n]` is the image of `E`'s `[n]` under the monoidal functor `Over.pullback g`.
[PROVED]
```lean
theorem mulBy_baseChange {T : Scheme.{u}} (g : T ⟶ S) (n : ℤ) :
    (E.baseChange g).mulBy n =
      (Over.pullback g).map (E.mulBy n) :=
```

-- The underlying scheme morphism of `[n]` on the base-changed curve is the pullback of `E`'s `[n]` (the `.left` of `mulBy_baseChange`, in explicit `pullback.lift` form).
[PROVED]
```lean
theorem mulByHom_baseChange {T : Scheme.{u}} (g : T ⟶ S) (n : ℤ) :
    (E.baseChange g).mulByHom n =
      Limits.pullback.lift (Limits.pullback.fst E.π g ≫ E.mulByHom n)
        (Limits.pullback.snd E.π g) (by simp [Limits.pullback.condition]) :=
```

[PROVED]
```lean
@[reassoc (attr := simp)]
lemma mulByHom_baseChange_fst {T : Scheme.{u}} (g : T ⟶ S) (n : ℤ) :
    (E.baseChange g).mulByHom n ≫ pullback.fst E.π g =
      pullback.fst E.π g ≫ E.mulByHom n :=
```

[PROVED]
```lean
@[reassoc (attr := simp)]
lemma mulByHom_baseChange_snd {T : Scheme.{u}} (g : T ⟶ S) (n : ℤ) :
    (E.baseChange g).mulByHom n ≫ pullback.snd E.π g = pullback.snd E.π g :=
```

-- A point of `E` over `g : T ⟶ S`, viewed as a section of the base-changed curve `E ×_S T / T`.
[DATA]
```lean
noncomputable def Point.asSection {T : Scheme.{u}} (g : T ⟶ S) (P : E.Point g) :
    (E.baseChange g).Point (𝟙 T) :=
```

[PROVED]
```lean
@[simp]
lemma Point.asSection_coe {T : Scheme.{u}} (g : T ⟶ S) (P : E.Point g) :
    (Point.asSection E g P).1 =
      pullback.lift P.1 (𝟙 T) (by rw [P.2, Category.id_comp]) :=
```

[PROVED]
```lean
@[reassoc (attr := simp)]
lemma Point.asSection_val_fst {T : Scheme.{u}} (g : T ⟶ S) (P : E.Point g) :
    (Point.asSection E g P).1 ≫ pullback.fst E.π g = P.1 :=
```

[PROVED]
```lean
@[reassoc (attr := simp)]
lemma Point.asSection_val_snd {T : Scheme.{u}} (g : T ⟶ S) (P : E.Point g) :
    (Point.asSection E g P).1 ≫ pullback.snd E.π g = 𝟙 T :=
```

-- **(T-D6a-ii, final ingredient)** `asSection` intertwines integer scalar multiplication. (PARKED 2026-07-09: blocked on the `(E.baseChange g).E` vs `pullback E.π g` defeq-spelling heterogeneity; structural-refactor-gated.)
[SORRY]
```lean
theorem Point.asSection_zsmul {T : Scheme.{u}} (g : T ⟶ S) (n : ℤ) (P : E.Point g) :
    Point.asSection E g (n • P) = n • Point.asSection E g P :=
```

Declarations: 26

---

## ModularCurves/EllipticCurve/Torsion.lean  (254 lines)

Torsion subgroup schemes `E[N]` as the kernel pullback of `[N]` against the zero section, with the KM 2.3.1 finiteness/flatness/rank statements and the Loeffler 3.4.2(2) étaleness for `N` invertible (three black boxes left as sorries).

Context: same opens/local instances as GroupLaw; `namespace ModularCurves`, `namespace EllipticCurve`, `variable {S : Scheme.{u}} (E : EllipticCurve S)`.

-- "`N` is invertible on the scheme `X`": `N` is a unit in the global sections.
[DATA]
```lean
def _root_.ModularCurves.NIsInvertible (X : Scheme.{u}) (N : ℕ) : Prop :=
  IsUnit (N : Γ(X, ⊤))
```

-- The `N`-torsion subscheme `E[N]`: the kernel of `[N]`, as the fibre product `E ×_{[N], E, 0} S` of `[N] : E ⟶ E` against the zero section.
[DATA]
```lean
noncomputable def torsion (N : ℕ) : Scheme.{u} :=
  pullback (E.mulByHom N) E.zero
```

-- The inclusion `E[N] ⟶ E`.
[DATA]
```lean
noncomputable def torsionι (N : ℕ) : E.torsion N ⟶ E.E :=
```

-- The structure morphism `E[N] ⟶ S`.
[DATA]
```lean
noncomputable def torsionπ (N : ℕ) : E.torsion N ⟶ S :=
```

-- A `T`-point of `E[N]`, from a point of `E` raw-killed by `N` (i.e. whose composite with `[N]` is the zero section over the base point).
[DATA]
```lean
noncomputable def pointToTorsion {N : ℕ} {T : Scheme.{u}} {g : T ⟶ S} (x : E.Point g)
    (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero) : T ⟶ E.torsion N :=
```

[PROVED]
```lean
@[simp]
theorem pointToTorsion_torsionπ {N : ℕ} {T : Scheme.{u}} {g : T ⟶ S} (x : E.Point g)
    (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero) :
    E.pointToTorsion x hx ≫ E.torsionπ N = g :=
```

[PROVED]
```lean
@[simp]
theorem pointToTorsion_torsionι {N : ℕ} {T : Scheme.{u}} {g : T ⟶ S} (x : E.Point g)
    (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero) :
    E.pointToTorsion x hx ≫ E.torsionι N = x.1 :=
```

-- **(T-B3)** `E[N] ⟶ E` is a closed immersion (kernels of group-scheme morphisms against proper separated bases; the zero section of a separated morphism is a closed immersion).
[PROVED]
```lean
theorem torsionι_isClosedImmersion (N : ℕ) :
    IsClosedImmersion (E.torsionι N) :=
```

-- The torsion inclusion followed by the structure morphism is the torsion structure morphism.
[PROVED]
```lean
@[reassoc]
theorem torsionι_π (N : ℕ) : E.torsionι N ≫ E.π = E.torsionπ N :=
```

-- `[n]` is proper: it is an `S`-endomorphism of the proper `S`-scheme `E` (cancellation along the separated `π`).
[PROVED]
```lean
instance mulByHom_isProper (n : ℤ) : IsProper (E.mulByHom n) :=
```

-- The zero morphism `[0]` factors through the base: it is `π` followed by the zero section.
[PROVED]
```lean
theorem mulByHom_zero : E.mulByHom 0 = E.π ≫ E.zero :=
```

-- **Black box `BB-QF` (fibre input of KM 2.3.1)**: `[N]` is (locally) quasi-finite for `N ≥ 1`.
[SORRY]
```lean
theorem mulByHom_locallyQuasiFinite (N : ℕ) [NeZero N] :
    LocallyQuasiFinite (E.mulByHom N) :=
```

-- **Black box `BB-FLAT` (flatness input of KM 2.3.1)**: `[N]` is flat for `N ≥ 1`.
[SORRY]
```lean
theorem mulByHom_flat (N : ℕ) [NeZero N] : Flat (E.mulByHom N) :=
```

-- **Black box `BB-DEG` (degree input of KM 2.3.1)**: `[N]` has rank `N²` at every point.
[SORRY]
```lean
theorem mulByHom_finrank (N : ℕ) [NeZero N] (x : E.E) :
    (E.mulByHom N).finrank x = N ^ 2 :=
```

-- **(KM 2.3.1, finiteness of `[N]`)** `[N]` is finite: proper + quasi-finite via Zariski's Main Theorem.
[PROVED]
```lean
theorem mulByHom_isFinite (N : ℕ) [NeZero N] : IsFinite (E.mulByHom N) :=
```

-- **(T-B4 = KM 2.3.1)** `E[N] ⟶ S` is finite and flat (finite locally free) — of rank `N²` by `torsion_rank`.
[PROVED]
```lean
theorem torsionπ_isFinite (N : ℕ) [NeZero N] : IsFinite (E.torsionπ N) :=
```

-- **(T-B4, flatness half of KM 2.3.1; BB-FLAT/stream FLAT consumer)** `E[N] ⟶ S` is flat.
[PROVED]
```lean
theorem torsionπ_flat (N : ℕ) : Flat (E.torsionπ N) :=
```

-- **(T-B4, rank part of KM 2.3.1)** `E[N]/S` has constant rank `N²`.
[PROVED]
```lean
theorem torsion_rank (N : ℕ) [NeZero N] (s : S) :
    (E.torsionπ N).finrank s = N ^ 2 :=
```

-- If `0` is invertible on a scheme then the scheme is empty (its global sections are the zero ring, and every stalk is a nontrivial local ring).
[PROVED]
```lean
theorem _root_.ModularCurves.isEmpty_of_nIsInvertible_zero {X : Scheme.{u}}
    (h : NIsInvertible X 0) : IsEmpty X :=
```

-- `[N]` is locally of finite presentation — an `S`-endomorphism of the locally-finitely-presented `E/S`, by the cancellation `ForMathlib.FinitePresentationCancel` (Stacks 01TX).
[PROVED]
```lean
theorem mulByHom_locallyOfFinitePresentation (N : ℕ) :
    LocallyOfFinitePresentation (E.mulByHom N) :=
```

-- **Black box `BB-DIFF` (T-B5 = Loeffler 3.4.2(2), unramifiedness)**: if `N` is invertible on `S` then `[N]` is formally unramified.
[SORRY]
```lean
theorem mulByHom_formallyUnramified (N : ℕ) (h : NIsInvertible S N) :
    FormallyUnramified (E.mulByHom N) :=
```

-- **(T-B5 = Loeffler 3.4.2(2))** If `N` is invertible on `S`, then `[N] : E ⟶ E` is étale (it induces multiplication by `N`, an isomorphism, on the invariant differential).
[PROVED]
```lean
theorem mulBy_etale (N : ℕ) (h : NIsInvertible S N) :
    Etale (E.mulByHom N) :=
```

-- **(T-B5′)** If `N` is invertible on `S`, then `E[N] ⟶ S` is (finite) étale.
[PROVED]
```lean
theorem torsionπ_etale (N : ℕ) (h : NIsInvertible S N) :
    Etale (E.torsionπ N) :=
```

Declarations: 23

---

## ModularCurves/EllipticCurve/TorsionFibre.lean  (400 lines)

Fibre comparison for the torsion subscheme (ticket T-B6): the kernel universal property `torsionPointsEquiv`, torsion commutes with base change, and the headline geometric statement that over an algebraically closed field with `N` invertible the `N`-torsion of the point group is `(ℤ/N)²`.

Context: same opens/local instances; `namespace ModularCurves`; inside `namespace EllipticCurve`: `variable {S : Scheme.{u}} (E : EllipticCurve S)`.

-- **(T-B6c)** On the spectrum of a field, `N` is invertible iff `N ≠ 0` in the field.
[PROVED]
```lean
theorem nIsInvertible_spec_iff (k : Type u) [Field k] (N : ℕ) :
    NIsInvertible (Spec (CommRingCat.of k)) N ↔ (N : k) ≠ 0 :=
```

-- The zero section of the base-changed curve projects to the zero section.
[PROVED]
```lean
@[reassoc]
theorem baseChange_zero_fst {T : Scheme.{u}} (g : T ⟶ S) :
    (E.baseChange g).zero ≫ pullback.fst E.π g = g ≫ E.zero :=
```

-- **(T-B6b, the comparison map)** The canonical morphism from the torsion of the base-changed curve to the torsion of `E`, lifting `torsionι ≫ pr₁` and `torsionπ ≫ g`.
[DATA]
```lean
noncomputable def torsionBaseChangeHom (N : ℕ) {T : Scheme.{u}} (g : T ⟶ S) :
    (E.baseChange g).torsion N ⟶ E.torsion N :=
```

[PROVED]
```lean
@[reassoc (attr := simp)]
theorem torsionBaseChangeHom_torsionι (N : ℕ) {T : Scheme.{u}} (g : T ⟶ S) :
    E.torsionBaseChangeHom N g ≫ E.torsionι N =
      (E.baseChange g).torsionι N ≫ pullback.fst E.π g :=
```

[PROVED]
```lean
@[reassoc (attr := simp)]
theorem torsionBaseChangeHom_torsionπ (N : ℕ) {T : Scheme.{u}} (g : T ⟶ S) :
    E.torsionBaseChangeHom N g ≫ E.torsionπ N =
      (E.baseChange g).torsionπ N ≫ g :=
```

-- **(T-B6b)** Torsion commutes with base change: the square `(E ×_S T)[N] ⟶ E[N]`, `(E ×_S T)[N] ⟶ T`, `E[N] ⟶ S`, `T ⟶ S` is cartesian.
[PROVED]
```lean
theorem torsion_baseChange_isPullback (N : ℕ) {T : Scheme.{u}} (g : T ⟶ S) :
    IsPullback (E.torsionBaseChangeHom N g) ((E.baseChange g).torsionπ N)
      (E.torsionπ N) g :=
```

-- The zero of the point group is the pulled-back zero section.
[PROVED]
```lean
theorem point_zero_val {T : Scheme.{u}} (g : T ⟶ S) :
    ((0 : E.Point g) : T ⟶ E.E) = g ≫ E.zero :=
```

-- Membership in the `N`-torsion of the point group, morphism-level form.
[PROVED]
```lean
theorem smul_eq_zero_iff_comp_mulByHom {T : Scheme.{u}} (g : T ⟶ S) (N : ℕ)
    (P : E.Point g) :
    (N : ℤ) • P = 0 ↔ (P : T ⟶ E.E) ≫ E.mulByHom (N : ℤ) = g ≫ E.zero :=
```

-- **(T-B6, kernel universal property)** `T`-points of the torsion subscheme `E[N]` over `t : T ⟶ S` are the `N`-torsion of the point group `E.Point t`.
[DATA]
```lean
noncomputable def torsionPointsEquiv (N : ℕ) {T : Scheme.{u}} (t : T ⟶ S) :
    { h : T ⟶ E.torsion N // h ≫ E.torsionπ N = t } ≃
      Submodule.torsionBy ℤ (E.Point t) (N : ℤ) where
```

-- **(T-B6 headline)** Over an algebraically closed field in which `N` is invertible, the `N`-torsion of the geometric point group is `(ℤ/N)²`.
[PROVED]
```lean
theorem torsion_geometricFibre_rank_two (N : ℕ) [NeZero N] (k : Type u) [Field k]
    [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S) (hN : (N : k) ≠ 0) :
    Nonempty (Submodule.torsionBy ℤ (E.Point t) (N : ℤ) ≃+ (Fin 2 → ZMod N)) :=
```

Declarations: 10

---

## ModularCurves/EllipticCurve/WeierstrassModel.lean  (2727 lines)

The projective Weierstrass model as a scheme: `projModel W = Proj (R[X,Y,Z]/(Weierstrass cubic))` with structure morphism and section at infinity `[0:1:0]`, its interface `IsWeierstrassModel` (properness, finite presentation, section, pointed field-points comparison), smoothness for elliptic `W`, and full base-change theory of the model.

Context: `open AlgebraicGeometry CategoryTheory`, `universe u`, `namespace ModularCurves`, `variable {R : Type u} [CommRing R]`. Section `ProjModel`: `open HomogeneousIdeal`, `attribute [local instance] MvPolynomial.gradedAlgebra`. Section `Points`: `open HomogeneousIdeal HomogeneousLocalization`. Section `BaseChangeGraded`: `variable {R' : Type u} [CommRing R'] (f : R →+* R')`. Section `TensorComparison`: `open scoped TensorProduct`, `variable {R' : Type u} [CommRing R'] [Algebra R R']`.

-- The `K`-points of an `R`-scheme `X`, for `K` an `R`-algebra: morphisms `Spec K ⟶ X` over `Spec R`.
[DATA]
```lean
def SpecPoints (X : Scheme.{u}) (f : X ⟶ Spec (.of R)) (K : Type u) [CommRing K] [Algebra R K] :
    Type u :=
  { g : Spec (.of K) ⟶ X // g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R K)) }
```

-- `IsWeierstrassModel W X f x₀` says that the pointed `R`-scheme `(X, f, x₀)` is *a* plane projective model of the Weierstrass curve `W`: proper, of finite presentation, with a section, and — **when `W` is elliptic** — its `K`-points over every `R`-algebra field `K` biject with the Weierstrass points `(W.baseChange K).toAffine.Point`, POINTEDLY (`x₀ ↦ 0`).
[DATA] (Prop-valued structure)
```lean
structure IsWeierstrassModel (W : WeierstrassCurve R) (X : Scheme.{u})
    (f : X ⟶ Spec (.of R)) (x₀ : Spec (.of R) ⟶ X) : Prop where
  isProper : IsProper f
  locallyOfFinitePresentation : LocallyOfFinitePresentation f
  section_comp : x₀ ≫ f = 𝟙 _
  /-- Pointed `K`-points comparison, for elliptic `W`. -/
  points : ∀ (_ : W.IsElliptic) (K : Type u) [Field K] [Algebra R K],
    ∃ e : SpecPoints X f K ≃ (W.baseChange K).toAffine.Point,
      e ⟨Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ x₀, by
        rw [Category.assoc, section_comp, Category.comp_id]⟩ = 0
```

-- The homogeneous Weierstrass cubic `Y²Z + a₁XYZ + a₃YZ² − (X³ + a₂X²Z + a₄XZ² + a₆Z³)` is homogeneous of degree `3`.
[PROVED]
```lean
theorem projective_polynomial_isHomogeneous (W : WeierstrassCurve R) :
    W.toProjective.polynomial.IsHomogeneous 3 :=
```

-- The homogeneous ideal `(W)` generated by the Weierstrass cubic.
[DATA]
```lean
noncomputable def projIdeal (W : WeierstrassCurve R) :
    HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 3) R) :=
```

[PROVED]
```lean
@[simp]
lemma projIdeal_toIdeal (W : WeierstrassCurve R) :
    (projIdeal W).toIdeal = Ideal.span {W.toProjective.polynomial} :=
```

-- The homogeneous coordinate ring `R[X,Y,Z]/(W)` of the plane Weierstrass cubic.
[DATA]
```lean
noncomputable abbrev projCoordRing (W : WeierstrassCurve R) : Type u :=
  MvPolynomial (Fin 3) R ⧸ (projIdeal W).toIdeal
```

-- **(T-A2, CONSTRUCTED 2026-07-06 — formerly DS1)** The plane projective model of a Weierstrass curve, as a scheme over `Spec R`: `Proj` of the homogeneous coordinate ring `R[X,Y,Z]/(W)`, graded by the quotient grading.
[DATA]
```lean
@[reducible] noncomputable def projModel (W : WeierstrassCurve R) : Scheme.{u} :=
  Proj (quotientGrading (projIdeal W))
```

-- **(T-A2)** The structure morphism of the projective Weierstrass model: `Proj.toSpecZero` followed by the degree-zero identification `R → (R[X,Y,Z]/(W))₀`.
[DATA]
```lean
noncomputable def projModelπ (W : WeierstrassCurve R) : projModel W ⟶ Spec (.of R) :=
  Proj.toSpecZero _ ≫ Spec.map (CommRingCat.ofHom (algebraMapGradeZero (projIdeal W)))
```

-- Evaluation of the homogeneous coordinate ring at the point at infinity `[0:1:0]`.
[DATA]
```lean
noncomputable def projModelZeroEval (W : WeierstrassCurve R) : projCoordRing W →+* R :=
```

[PROVED]
```lean
@[simp]
lemma projModelZeroEval_mk (W : WeierstrassCurve R) (p : MvPolynomial (Fin 3) R) :
    projModelZeroEval W (Ideal.Quotient.mk (projIdeal W).toIdeal p) =
      MvPolynomial.eval (fun i : Fin 3 => if i = 1 then 1 else 0) p :=
```

-- The class of `Y` lies in the irrelevant ideal of the quotient grading.
[PROVED]
```lean
lemma mk_Y_mem_irrelevant (W : WeierstrassCurve R) :
    Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.X 1) ∈
      (HomogeneousIdeal.irrelevant (quotientGrading (projIdeal W))).toIdeal :=
```

-- The evaluation at `[0:1:0]` maps the irrelevant ideal onto the unit ideal.
[PROVED]
```lean
lemma projModelZeroEval_irrelevant_map_top (W : WeierstrassCurve R) :
    (HomogeneousIdeal.irrelevant (quotientGrading (projIdeal W))).toIdeal.map
      ((Scheme.ΓSpecIso (.of R)).inv.hom.comp (projModelZeroEval W)) = ⊤ :=
```

-- **(T-A2)** The section at infinity `[0:1:0]` of the projective Weierstrass model, via `Proj.fromOfGlobalSections` at the evaluation `X ↦ 0, Y ↦ 1, Z ↦ 0`.
[DATA]
```lean
noncomputable def projModelZero (W : WeierstrassCurve R) : Spec (.of R) ⟶ projModel W :=
```

-- **(T-A2, PROVED)** The section at infinity is a section of the structure morphism: `[0:1:0]` lies over the identity of `Spec R`.
[PROVED]
```lean
@[reassoc (attr := simp)]
theorem projModelZero_projModelπ (W : WeierstrassCurve R) :
    projModelZero W ≫ projModelπ W = 𝟙 _ :=
```

-- Evaluation at `[0:1:0]` retracts the degree-zero inclusion: the composite `R → (R[X,Y,Z]/(W))₀ → R[X,Y,Z]/(W) → R` is the identity.
[PROVED]
```lean
@[simp]
lemma projModelZeroEval_algebraMapGradeZero (W : WeierstrassCurve R) (r : R) :
    projModelZeroEval W (algebraMap (↥(quotientGrading (projIdeal W) 0))
      (projCoordRing W) (algebraMapGradeZero (projIdeal W) r)) = r :=
```

[PROVED]
```lean
theorem algebraMapGradeZero_bijective (W : WeierstrassCurve R) :
    Function.Bijective (algebraMapGradeZero (projIdeal W)) :=
```

-- The degree-zero part of the homogeneous coordinate ring is `R` itself.
[DATA]
```lean
noncomputable def gradeZeroRingEquiv (W : WeierstrassCurve R) :
    R ≃+* ↥(quotientGrading (projIdeal W) 0) :=
```

[PROVED] (anonymous instance)
```lean
instance (W : WeierstrassCurve R) :
    IsIso (Spec.map (CommRingCat.ofHom (algebraMapGradeZero (projIdeal W)))) :=
```

[PROVED] (anonymous instance)
```lean
instance (W : WeierstrassCurve R) :
    Algebra.FiniteType (↥(quotientGrading (projIdeal W) 0)) (projCoordRing W) :=
```

-- **(T-A2, PROVED)** The projective Weierstrass model is proper over the base: mathlib's properness of `Proj` (valuative criterion) composed with the degree-zero identification.
[PROVED]
```lean
instance projModelπ_isProper (W : WeierstrassCurve R) : IsProper (projModelπ W) :=
```

-- The class of `X i` in the quotient grading, in degree one.
[PROVED]
```lean
lemma mk_X_mem_quotientGrading_one (W : WeierstrassCurve R) (i : Fin 3) :
    (quotientGradingHom (projIdeal W)) (MvPolynomial.X i) ∈
      quotientGrading (projIdeal W) 1 :=
```

-- Finite presentation of each chart of the Weierstrass model over `R`: the chart of `ℙ²` (a polynomial ring in two variables, via `chartRingEquiv`) modulo the principal dehomogenised cubic.
[PROVED]
```lean
theorem finitePresentation_awayQuotient (W : WeierstrassCurve R) (i : Fin 3) :
    RingHom.FinitePresentation
      ((HomogeneousLocalization.Away.map (quotientGradingHom (projIdeal W))
        (MvPolynomial.X i)).comp
          ((MvPolynomial.chartRingEquiv R i).symm :
            MvPolynomial {j : Fin 3 // j ≠ i} R →+*
              Away (MvPolynomial.homogeneousSubmodule (Fin 3) R) (MvPolynomial.X i))) :=
```

-- Every irrelevant polynomial lies in the ideal generated by the variables.
[PROVED]
```lean
lemma poly_irrelevant_le_idealOfVars :
    (HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (Fin 3) R)).toIdeal ≤
      MvPolynomial.idealOfVars (Fin 3) R :=
```

-- The classes of the three variables cut out the irrelevant ideal of the coordinate ring of the Weierstrass model.
[PROVED]
```lean
lemma quotient_irrelevant_le_span_mk_X (W : WeierstrassCurve R) :
    (HomogeneousIdeal.irrelevant (quotientGrading (projIdeal W))).toIdeal ≤
      Ideal.span (Set.range fun i : Fin 3 =>
        Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.X i)) :=
```

-- The two `R`-structurings of a chart agree: through the degree-zero part, or through the polynomial chart of `ℙ²`.
[PROVED]
```lean
theorem algebraMap_gradeZero_comp_eq (W : WeierstrassCurve R) (i : Fin 3) :
    (algebraMap (↥(quotientGrading (projIdeal W) 0))
        (Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)))).comp
      ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (projIdeal W) 0)) =
      ((HomogeneousLocalization.Away.map (quotientGradingHom (projIdeal W))
          (MvPolynomial.X i)).comp
        ((MvPolynomial.chartRingEquiv R i).symm :
          MvPolynomial {j : Fin 3 // j ≠ i} R →+*
            Away (MvPolynomial.homogeneousSubmodule (Fin 3) R)
              (MvPolynomial.X i))).comp
        (algebraMap R (MvPolynomial {j : Fin 3 // j ≠ i} R)) :=
```

-- Finite presentation of the canonical map from the degree-zero part into each chart of the Weierstrass model.
[PROVED]
```lean
theorem fp_algebraMap_gradeZero_away (W : WeierstrassCurve R) (i : Fin 3) :
    RingHom.FinitePresentation (algebraMap (↥(quotientGrading (projIdeal W) 0))
      (Away (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)))) :=
```

[PROVED] (anonymous instance)
```lean
instance (W : WeierstrassCurve R) :
    LocallyOfFinitePresentation (Proj.toSpecZero (quotientGrading (projIdeal W))) :=
```

-- **(T-A2d, PROVED)** The projective Weierstrass model is locally of finite presentation over the base.
[PROVED]
```lean
theorem projModelπ_lfp (W : WeierstrassCurve R) :
    LocallyOfFinitePresentation (projModelπ W) :=
```

-- Every `K`-point of the model factors through one of the three affine charts.
[PROVED]
```lean
lemma specPoint_factors_through_chart (W : WeierstrassCurve R)
    {K : Type u} [Field K] [Algebra R K] (g : Spec (.of K) ⟶ projModel W) :
    ∃ (i : Fin 3) (h : Spec (.of K) ⟶
        Spec (.of (Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i))))),
      h ≫ Proj.awayι (quotientGrading (projIdeal W)) _
        (mk_X_mem_quotientGrading_one W i) one_pos = g :=
```

-- The chart of the model as a quotient of the chart of `ℙ²`.
[DATA]
```lean
noncomputable def chartQuotientEquiv (W : WeierstrassCurve R) (i : Fin 3) :
    (Away (MvPolynomial.homogeneousSubmodule (Fin 3) R) (MvPolynomial.X i) ⧸
      Ideal.span {HomogeneousLocalization.Away.mk
        (MvPolynomial.homogeneousSubmodule (Fin 3) R)
        (MvPolynomial.X_mem_homogeneousSubmodule_one R i) 3 W.toProjective.polynomial
        (by simp [projective_polynomial_isHomogeneous W])}) ≃+*
    Away (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)) :=
```

-- The chart of the model as the plane coordinate ring modulo the dehomogenised cubic.
[DATA]
```lean
noncomputable def chartCoordEquiv (W : WeierstrassCurve R) (i : Fin 3) :
    (MvPolynomial {j : Fin 3 // j ≠ i} R ⧸
      Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial}) ≃+*
    Away (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)) :=
```

[PROVED]
```lean
@[simp]
lemma chartCoordEquiv_mk (W : WeierstrassCurve R) (i : Fin 3)
    (p : MvPolynomial {j : Fin 3 // j ≠ i} R) :
    chartCoordEquiv W i (Ideal.Quotient.mk
        (Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial}) p) =
      HomogeneousLocalization.Away.map (quotientGradingHom (projIdeal W))
        (MvPolynomial.X i) (MvPolynomial.homogenizeAt R i p) :=
```

[PROVED]
```lean
lemma chartCoordEquiv_mk_C (W : WeierstrassCurve R) (i : Fin 3) (r : R) :
    chartCoordEquiv W i (Ideal.Quotient.mk
        (Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial})
        (MvPolynomial.C r)) =
      (algebraMap (↥(quotientGrading (projIdeal W) 0))
        (Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i))))
        ((gradeZeroRingEquiv W) r) :=
```

-- Ring homomorphisms from a chart of the model, compatible with the `R`-structure, are the `K`-solutions of the dehomogenised cubic.
[DATA]
```lean
noncomputable def chartSolutionsEquiv (W : WeierstrassCurve R) (i : Fin 3)
    (K : Type u) [CommRing K] [Algebra R K] :
    { φ : Away (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)) →+* K //
      φ.comp ((algebraMap (↥(quotientGrading (projIdeal W) 0))
          (Away (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)))).comp
        ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (projIdeal W) 0))) =
        algebraMap R K } ≃
    { v : {j : Fin 3 // j ≠ i} → K //
      MvPolynomial.aeval v
        (MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial) = 0 } :=
```

-- Restricted to a chart, the structure morphism of the model is `Spec` of the `R`-structuring of the chart ring.
[PROVED]
```lean
lemma awayι_projModelπ (W : WeierstrassCurve R) (i : Fin 3) :
    Proj.awayι (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i))
      (mk_X_mem_quotientGrading_one W i) one_pos ≫ projModelπ W =
      Spec.map (CommRingCat.ofHom
        ((algebraMap (↥(quotientGrading (projIdeal W) 0))
          (Away (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)))).comp
        ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (projIdeal W) 0)))) :=
```

-- `K`-points of the model that factor through chart `i` are the `R`-compatible ring homomorphisms out of the chart ring.
[DATA]
```lean
noncomputable def chartHomEquiv (W : WeierstrassCurve R) (i : Fin 3)
    (K : Type u) [CommRing K] [Algebra R K] :
    { g : SpecPoints (projModel W) (projModelπ W) K //
      ∃ h : Spec (.of K) ⟶ Spec (.of (Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)))),
        h ≫ Proj.awayι (quotientGrading (projIdeal W)) _
          (mk_X_mem_quotientGrading_one W i) one_pos = g.1 } ≃
    { φ : Away (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)) →+* K //
      φ.comp ((algebraMap (↥(quotientGrading (projIdeal W) 0))
          (Away (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)))).comp
        ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (projIdeal W) 0))) =
        algebraMap R K } :=
```

-- The chart coordinate `Xⱼ/Xᵢ` is mathlib's localization element for the pair `(Xᵢ, Xⱼ)`.
[PROVED]
```lean
lemma chartCoordEquiv_mk_X (W : WeierstrassCurve R) (i : Fin 3)
    (j : {j : Fin 3 // j ≠ i}) :
    chartCoordEquiv W i (Ideal.Quotient.mk
        (Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial})
        (MvPolynomial.X j)) =
      HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one W i) (mk_X_mem_quotientGrading_one W j.1) :=
```

-- A `K`-point of the model sitting in chart `i` lies in chart `j` precisely when its `j`-th coordinate is nonzero.
[PROVED]
```lean
lemma chartPointOfHom_factors_iff (W : WeierstrassCurve R) (i j : Fin 3)
    {K : Type u} [Field K] [Algebra R K]
    (φ : { φ : Away (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)) →+* K //
      φ.comp ((algebraMap (↥(quotientGrading (projIdeal W) 0))
          (Away (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)))).comp
        ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (projIdeal W) 0))) =
        algebraMap R K }) :
    (∃ h' : Spec (.of K) ⟶ Spec (.of (Away (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j)))),
      h' ≫ Proj.awayι (quotientGrading (projIdeal W)) _
        (mk_X_mem_quotientGrading_one W j) one_pos = (chartPointOfHom W i φ).1.1) ↔
      φ.1 (HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one W i) (mk_X_mem_quotientGrading_one W j)) ≠ 0 :=
```

-- **(T-A2e)** The pointed `K`-points clause for elliptic `W`: `K`-points of the model biject with `(W.baseChange K).toAffine.Point`, sending `[0:1:0]` to `0`.
[PROVED]
```lean
theorem projModel_points (W : WeierstrassCurve R) (hell : W.IsElliptic)
    (K : Type u) [Field K] [Algebra R K] :
    ∃ e : SpecPoints (projModel W) (projModelπ W) K ≃ (W.baseChange K).toAffine.Point,
      e ⟨Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ projModelZero W, by
        rw [Category.assoc, projModelZero_projModelπ, Category.comp_id]⟩ = 0 :=
```

-- **(T-A3a)** Certificate-free Weierstrass Jacobian comaximality: for elliptic `W`, the dehomogenised cubic and its two partials generate the unit ideal.
[PROVED]
```lean
theorem span_dehomog_jacobian_eq_top (W : WeierstrassCurve R) [W.IsElliptic] :
    Ideal.span {MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial,
      MvPolynomial.pderiv ⟨0, by decide⟩
        (MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial),
      MvPolynomial.pderiv ⟨1, by decide⟩
        (MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial)} = ⊤ :=
```

-- **(T-A3c)** Jacobian comaximality on the `Y`-chart.
[PROVED]
```lean
theorem span_dehomog_jacobian_eq_top_one (W : WeierstrassCurve R) [W.IsElliptic] :
    Ideal.span {MvPolynomial.dehomogenizeAux R 1 W.toProjective.polynomial,
      MvPolynomial.pderiv ⟨0, by decide⟩
        (MvPolynomial.dehomogenizeAux R 1 W.toProjective.polynomial),
      MvPolynomial.pderiv ⟨2, by decide⟩
        (MvPolynomial.dehomogenizeAux R 1 W.toProjective.polynomial)} = ⊤ :=
```

-- **(T-A3c)** Jacobian comaximality on the `X`-chart.
[PROVED]
```lean
theorem span_dehomog_jacobian_eq_top_zero (W : WeierstrassCurve R) [W.IsElliptic] :
    Ideal.span {MvPolynomial.dehomogenizeAux R 0 W.toProjective.polynomial,
      MvPolynomial.pderiv ⟨1, by decide⟩
        (MvPolynomial.dehomogenizeAux R 0 W.toProjective.polynomial),
      MvPolynomial.pderiv ⟨2, by decide⟩
        (MvPolynomial.dehomogenizeAux R 0 W.toProjective.polynomial)} = ⊤ :=
```

-- The `R`-structuring of a chart factors through the plane-quotient chart identification.
[PROVED]
```lean
lemma algebraMap_chart_eq (W : WeierstrassCurve R) (i : Fin 3) :
    ((algebraMap (↥(quotientGrading (projIdeal W) 0))
      (Away (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)))).comp
      ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (projIdeal W) 0))) =
      ((chartCoordEquiv W i).toRingHom).comp
        (algebraMap R (MvPolynomial {j : Fin 3 // j ≠ i} R ⧸
          Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial})) :=
```

-- The structure map into each chart of the model is locally standard smooth of relative dimension 1, for elliptic `W`.
[PROVED]
```lean
theorem locally_isStandardSmooth_algebraMap_gradeZero_away (W : WeierstrassCurve R)
    [W.IsElliptic] (i : Fin 3) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      ((algebraMap (↥(quotientGrading (projIdeal W) 0))
        (Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)))).comp
        ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (projIdeal W) 0))) :=
```

-- The chart inclusion from the degree-zero part is locally standard smooth of relative dimension 1, for elliptic `W`.
[PROVED]
```lean
theorem locally_isStandardSmooth_algebraMap_gradeZero_away' (W : WeierstrassCurve R)
    [W.IsElliptic] (i : Fin 3) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap (↥(quotientGrading (projIdeal W) 0))
        (Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)))) :=
```

-- The `Proj`-to-degree-zero morphism of the model is smooth of relative dimension 1, for elliptic `W`.
[PROVED]
```lean
theorem toSpecZero_smoothOfRelativeDimension (W : WeierstrassCurve R)
    [W.IsElliptic] :
    SmoothOfRelativeDimension 1 (Proj.toSpecZero (quotientGrading (projIdeal W))) :=
```

-- **(T-A3)** The projective model of an *elliptic* Weierstrass curve (unit discriminant) is smooth of relative dimension 1 over the base.
[PROVED]
```lean
theorem projModel_smooth (W : WeierstrassCurve R) [W.IsElliptic] :
    SmoothOfRelativeDimension 1 (projModelπ W) :=
```

-- `MvPolynomial.map` as a graded ring homomorphism for the standard grading.
[DATA]
```lean
noncomputable def mvMapGraded : GradedRingHom
    (MvPolynomial.homogeneousSubmodule (Fin 3) R)
    (MvPolynomial.homogeneousSubmodule (Fin 3) R') where
```

[PROVED]
```lean
lemma projIdeal_le_comap (W : WeierstrassCurve R) :
    (projIdeal W).toIdeal ≤
      (projIdeal (W.map f)).toIdeal.comap (MvPolynomial.map f) :=
```

-- The graded base-change homomorphism between the homogeneous coordinate rings of the Weierstrass models of `W` and `W.map f`.
[DATA]
```lean
noncomputable def baseChangeGradedHom (W : WeierstrassCurve R) :
    GradedRingHom (quotientGrading (projIdeal W))
      (quotientGrading (projIdeal (W.map f))) :=
```

[PROVED]
```lean
lemma baseChangeGradedHom_irrelevant_le (W : WeierstrassCurve R) :
    (HomogeneousIdeal.irrelevant (quotientGrading (projIdeal (W.map f)))).toIdeal ≤
      Ideal.map (baseChangeGradedHom f W).toRingHom
        (HomogeneousIdeal.irrelevant (quotientGrading (projIdeal W))).toIdeal :=
```

-- **(T-A5a)** The base-change morphism between projective Weierstrass models: `Proj` of the graded base-change homomorphism.
[DATA]
```lean
noncomputable def projModelBaseChange (W : WeierstrassCurve R) :
    projModel (W.map f) ⟶ projModel W :=
```

-- **(T-A5a)** The base-change square of the model over its structure morphisms.
[PROVED]
```lean
theorem projModelBaseChange_π (W : WeierstrassCurve R) :
    projModelBaseChange f W ≫ projModelπ W =
      projModelπ (W.map f) ≫ Spec.map (CommRingCat.ofHom f) :=
```

-- **(T-A5a)** The comparison morphism from the model of `W.map f` into the base change of the model of `W`.
[DATA]
```lean
noncomputable def projModelBaseChangeLift (W : WeierstrassCurve R) :
    projModel (W.map f) ⟶
      Limits.pullback (projModelπ W) (Spec.map (CommRingCat.ofHom f)) :=
```

-- Scalar extension identifies the dehomogenised cubics.
[PROVED]
```lean
lemma dehomog_baseChange (W : WeierstrassCurve R) (i : Fin 3) :
    MvPolynomial.map (algebraMap R R')
        (MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial) =
      MvPolynomial.dehomogenizeAux R' i
        (W.map (algebraMap R R')).toProjective.polynomial :=
```

-- The scalar-extension map between the affine chart quotients.
[DATA]
```lean
noncomputable def sChartBaseChange (W : WeierstrassCurve R) (i : Fin 3) :
    (MvPolynomial {j : Fin 3 // j ≠ i} R ⧸
      Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial}) →ₐ[R]
    (MvPolynomial {j : Fin 3 // j ≠ i} R' ⧸
      Ideal.span {MvPolynomial.dehomogenizeAux R' i
        (W.map (algebraMap R R')).toProjective.polynomial}) :=
```

[PROVED]
```lean
@[simp]
lemma sChartBaseChange_mk (W : WeierstrassCurve R) (i : Fin 3)
    (p : MvPolynomial {j : Fin 3 // j ≠ i} R) :
    sChartBaseChange (R' := R') W i (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap R R') p) :=
```

-- Scalar extension of the chart quotient as a tensor identification.
[DATA]
```lean
noncomputable def sChartTensorEquiv (W : WeierstrassCurve R) (i : Fin 3) :
    (R' ⊗[R] (MvPolynomial {j : Fin 3 // j ≠ i} R ⧸
      Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial}))
      ≃ₐ[R'] (MvPolynomial {j : Fin 3 // j ≠ i} R' ⧸
      Ideal.span {MvPolynomial.dehomogenizeAux R' i
        (W.map (algebraMap R R')).toProjective.polynomial}) :=
```

-- The chart quotients form a pushout square over `R → R'`.
[PROVED]
```lean
lemma isPushout_sChart (W : WeierstrassCurve R) (i : Fin 3) :
    letI : Algebra
        (MvPolynomial {j : Fin 3 // j ≠ i} R ⧸
          Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial})
        (MvPolynomial {j : Fin 3 // j ≠ i} R' ⧸
          Ideal.span {MvPolynomial.dehomogenizeAux R' i
            (W.map (algebraMap R R')).toProjective.polynomial}) :=
      ((sChartBaseChange (R' := R') W i).toRingHom).toAlgebra
    Algebra.IsPushout R R'
      (MvPolynomial {j : Fin 3 // j ≠ i} R ⧸
        Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial})
      (MvPolynomial {j : Fin 3 // j ≠ i} R' ⧸
        Ideal.span {MvPolynomial.dehomogenizeAux R' i
          (W.map (algebraMap R R')).toProjective.polynomial}) :=
```

-- The categorical (CommRingCat) pushout square of the chart quotients.
[PROVED]
```lean
lemma isPushout_sChart_commRingCat (W : WeierstrassCurve R) (i : Fin 3) :
    IsPushout
      (CommRingCat.ofHom (algebraMap R R'))
      (CommRingCat.ofHom (algebraMap R
        (MvPolynomial {j : Fin 3 // j ≠ i} R ⧸
          Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial})))
      (CommRingCat.ofHom (algebraMap R'
        (MvPolynomial {j : Fin 3 // j ≠ i} R' ⧸
          Ideal.span {MvPolynomial.dehomogenizeAux R' i
            (W.map (algebraMap R R')).toProjective.polynomial})))
      (CommRingCat.ofHom ((sChartBaseChange (R' := R') W i).toRingHom)) :=
```

-- The `Spec` of the chart square is a pullback: the chart of the base-changed model is the base change of the chart.
[PROVED]
```lean
lemma isPullback_sChart_spec (W : WeierstrassCurve R) (i : Fin 3) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap R'
        (MvPolynomial {j : Fin 3 // j ≠ i} R' ⧸
          Ideal.span {MvPolynomial.dehomogenizeAux R' i
            (W.map (algebraMap R R')).toProjective.polynomial}))))
      (Spec.map (CommRingCat.ofHom ((sChartBaseChange (R' := R') W i).toRingHom)))
      (Spec.map (CommRingCat.ofHom (algebraMap R R')))
      (Spec.map (CommRingCat.ofHom (algebraMap R
        (MvPolynomial {j : Fin 3 // j ≠ i} R ⧸
          Ideal.span {MvPolynomial.dehomogenizeAux R i
            W.toProjective.polynomial})))) :=
```

-- The three-chart affine open cover of the projective Weierstrass model.
[DATA]
```lean
noncomputable def modelChartCover (W : WeierstrassCurve R) :
    (projModel W).AffineOpenCover :=
```

-- Each cover piece of the pulled-back model is `Spec` of the base-changed chart quotient: the pullback square at chart `j`.
[PROVED]
```lean
lemma isPullback_piece (W : WeierstrassCurve R) (j : Fin 3) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (((sChartBaseChange (R' := R') W j).toRingHom).comp
          ((chartCoordEquiv W j).symm.toRingHom))))
      (Spec.map (CommRingCat.ofHom (algebraMap R'
        (MvPolynomial {k : Fin 3 // k ≠ j} R' ⧸
          Ideal.span {MvPolynomial.dehomogenizeAux R' j
            (W.map (algebraMap R R')).toProjective.polynomial}))))
      ((modelChartCover W).openCover.f j ≫ projModelπ W)
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
```

[PROVED]
```lean
lemma baseChangeGradedHom_mk_X (W : WeierstrassCurve R) (j : Fin 3) :
    (baseChangeGradedHom (algebraMap R R') W)
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j)) =
      (quotientGradingHom (projIdeal (W.map (algebraMap R R'))))
        (MvPolynomial.X j) :=
```

-- The chart square of the base-change morphism of models is cartesian: `D₊`-preimages under `Proj.map` are the base-changed charts.
[PROVED]
```lean
lemma isPullback_projModelBaseChange_chart (W : WeierstrassCurve R) (j : Fin 3) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map
        (baseChangeGradedHom (algebraMap R R') W)
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j)))))
      (Proj.awayι (quotientGrading (projIdeal (W.map (algebraMap R R'))))
        ((baseChangeGradedHom (algebraMap R R') W)
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j)))
        ((baseChangeGradedHom (algebraMap R R') W).2
          (mk_X_mem_quotientGrading_one W j)) one_pos)
      (Proj.awayι (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j))
        (mk_X_mem_quotientGrading_one W j) one_pos)
      (projModelBaseChange (algebraMap R R') W) :=
```

-- The graded square of the base change: quotient map after coefficient map.
[PROVED]
```lean
lemma gradedSquare (W : WeierstrassCurve R) :
    (baseChangeGradedHom (algebraMap R R') W).comp
      (quotientGradingHom (projIdeal W)) =
    (quotientGradingHom (projIdeal (W.map (algebraMap R R')))).comp
      (mvMapGraded (algebraMap R R')) :=
```

-- The lift restricts over each cover piece to the base-changed chart.
[PROVED]
```lean
lemma isPullback_lift_piece (W : WeierstrassCurve R) (j : Fin 3) :
    IsPullback
      ((thetaIso (R' := R') W j).hom ≫
        Proj.awayι (quotientGrading (projIdeal (W.map (algebraMap R R'))))
          ((baseChangeGradedHom (algebraMap R R') W)
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j)))
          ((baseChangeGradedHom (algebraMap R R') W).2
            (mk_X_mem_quotientGrading_one W j)) one_pos)
      ((isPullback_piece (R' := R') W j).isoPullback.hom)
      (projModelBaseChangeLift (algebraMap R R') W)
      ((Scheme.Pullback.openCoverOfLeft ((modelChartCover W).openCover)
        (projModelπ W) (Spec.map (CommRingCat.ofHom (algebraMap R R')))).f j) :=
```

[PROVED]
```lean
theorem projModelBaseChangeLift_isIso (W : WeierstrassCurve R) :
    IsIso (projModelBaseChangeLift (algebraMap R R') W) :=
```

-- **(T-A5a, headline)** The projective model of `W.map f` is the base change of the projective model of `W` along `Spec f`.
[PROVED]
```lean
theorem isPullback_projModelBaseChange (W : WeierstrassCurve R) :
    IsPullback (projModelBaseChange (algebraMap R R') W)
      (projModelπ (W.map (algebraMap R R'))) (projModelπ W)
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
```

-- The section at infinity lands entirely in the `Y`-chart.
[PROVED]
```lean
lemma projModelZero_preimage_yChart (W : WeierstrassCurve R) :
    projModelZero W ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))) = ⊤ :=
```

-- The chart factorisation of the section at infinity through the `Y`-chart.
[DATA]
```lean
noncomputable def projModelZeroChart (W : WeierstrassCurve R) :
    Spec (.of R) ⟶ Spec (.of (Away (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)))) :=
```

[PROVED]
```lean
@[reassoc]
lemma projModelZeroChart_fac (W : WeierstrassCurve R) :
    projModelZeroChart W ≫ Proj.awayι (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
      (mk_X_mem_quotientGrading_one W 1) one_pos = projModelZero W :=
```

-- The chart factorisation of the zero section is a retraction of the chart's `R`-structuring.
[PROVED]
```lean
lemma projModelZeroChart_comp_χ (W : WeierstrassCurve R) :
    projModelZeroChart W ≫ Spec.map (CommRingCat.ofHom
      ((algebraMap (↥(quotientGrading (projIdeal W) 0))
        (Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)))).comp
      ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (projIdeal W) 0)))) =
    𝟙 (Spec (.of R)) :=
```

-- Evaluation of the `Y`-chart at the point at infinity `[0:1:0]`.
[DATA]
```lean
noncomputable def zeroChartHom (W : WeierstrassCurve R) :
    Away (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)) →+* R :=
```

[PROVED]
```lean
lemma zeroChartHom_mk (W : WeierstrassCurve R) {i : ℕ}
    (hs : (quotientGradingHom (projIdeal W)) (MvPolynomial.X 1) ∈
      quotientGrading (projIdeal W) i) (n : ℕ) (a : projCoordRing W)
    (ha : a ∈ quotientGrading (projIdeal W) (n • i)) :
    zeroChartHom W (HomogeneousLocalization.Away.mk _ hs n a ha) =
      projModelZeroEval W a :=
```

-- The `Spec` of the chart evaluation composed with the chart inclusion is the section at infinity (the glue step of the zero-leg).
[PROVED]
```lean
lemma spec_zeroChartHom_awayι (W : WeierstrassCurve R) :
    Spec.map (CommRingCat.ofHom (zeroChartHom W)) ≫
      Proj.awayι (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1))
        (mk_X_mem_quotientGrading_one W 1) one_pos = projModelZero W :=
```

-- The `Y`-chart factorisation of the zero section is `Spec` of the evaluation at the point at infinity.
[PROVED]
```lean
lemma projModelZeroChart_eq_spec (W : WeierstrassCurve R) :
    projModelZeroChart W = Spec.map (CommRingCat.ofHom (zeroChartHom W)) :=
```

-- The point-at-infinity evaluation is natural in the base ring.
[PROVED]
```lean
lemma projModelZeroEval_baseChangeGradedHom {R' : Type u} [CommRing R'] [Algebra R R']
    (W : WeierstrassCurve R) (x : projCoordRing W) :
    projModelZeroEval (W.map (algebraMap R R'))
      ((baseChangeGradedHom (algebraMap R R') W) x) =
      algebraMap R R' (projModelZeroEval W x) :=
```

-- Naturality of the section at infinity under base change (T-A5b zero-leg).
[PROVED]
```lean
lemma projModelZero_baseChange {R' : Type u} [CommRing R'] [Algebra R R']
    (W : WeierstrassCurve R) :
    projModelZero (W.map (algebraMap R R')) ≫
        projModelBaseChange (algebraMap R R') W =
      Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ projModelZero W :=
```

-- **(T-A2)** The constructed model satisfies its interface.
[PROVED]
```lean
theorem projModel_isWeierstrassModel (W : WeierstrassCurve R) :
    IsWeierstrassModel W (projModel W) (projModelπ W) (projModelZero W) :=
```

-- **(T-A4, uniqueness of the model — KM 2.2.5 scope)** For **elliptic** `W`, any two pointed **smooth** models satisfying `IsWeierstrassModel W` are isomorphic over `Spec R`, compatibly with the base points.
[SORRY]
```lean
theorem isWeierstrassModel_unique (W : WeierstrassCurve R) [W.IsElliptic]
    {X X' : Scheme.{u}}
    {f : X ⟶ Spec (.of R)} {x₀ : Spec (.of R) ⟶ X} {f' : X' ⟶ Spec (.of R)}
    {x₀' : Spec (.of R) ⟶ X'}
    (hs : SmoothOfRelativeDimension 1 f) (hs' : SmoothOfRelativeDimension 1 f')
    (h : IsWeierstrassModel W X f x₀)
    (h' : IsWeierstrassModel W X' f' x₀') :
    ∃ e : X ≅ X', e.hom ≫ f' = f ∧ x₀ ≫ e.hom = x₀' :=
```

Declarations: 81

---

## ModularCurves/GroupScheme/MuN.lean  (887 lines)

The group schemes `μ_N = Spec ℤ[T]/(Tᴺ − 1)` and the constant scheme `(ℤ/N)_S` over a base: points descriptions, group-object structures via representability, finite locally free of rank `N`, and étale iff `N` invertible.

Context: `open AlgebraicGeometry CategoryTheory Limits Polynomial`, `universe u`, **`noncomputable section`** (so `def`s below are noncomputable without the keyword), `namespace ModularCurves`.

-- The coordinate ring `ℤ[T]/(Tᴺ − 1)` of `μ_N`.
[DATA]
```lean
def muNRing (N : ℕ) : CommRingCat.{u} :=
  .of (ULift.{u} (Polynomial ℤ ⧸ Ideal.span {(X : Polynomial ℤ) ^ N - 1}))
```

-- The absolute scheme of `N`-th roots of unity, `μ_N = Spec ℤ[T]/(Tᴺ − 1)`.
[DATA]
```lean
def muNAbs (N : ℕ) : Scheme.{u} := Spec (muNRing N)
```

-- `μ_N` over an arbitrary base `S`: the base change of `muNAbs` to `S` (fibre product over the terminal scheme `Spec ℤ`).
[DATA]
```lean
def muN (S : Scheme.{u}) (N : ℕ) : Scheme.{u} :=
  pullback (terminal.from S) (terminal.from (muNAbs N))
```

-- The structure morphism of `μ_{N,S}`.
[DATA]
```lean
def muNπ (S : Scheme.{u}) (N : ℕ) : muN S N ⟶ S := pullback.fst _ _
```

-- The constant `S`-scheme on a finite type `A`: the disjoint union of copies of `S` indexed by `A`.
[DATA]
```lean
abbrev constScheme (S : Scheme.{u}) (A : Type) [Finite A] : Scheme.{u} :=
  ∐ fun _ : A ↦ S
```

-- The structure morphism of the constant scheme.
[DATA]
```lean
abbrev constSchemeπ (S : Scheme.{u}) (A : Type) [Finite A] : constScheme S A ⟶ S :=
  Sigma.desc fun _ ↦ 𝟙 S
```

-- **(DS3a, ticket T-B2)** The group structure on `μ_{N,S}` in `Over S`, with comultiplication `Spec` of `T ↦ T ⊗ T`.
[DATA]
```lean
noncomputable instance muNGrpObj (S : Scheme.{u}) (N : ℕ) [NeZero N] :
    GrpObj (Over.mk (muNπ S N)) :=
```

-- **(DS3b pin, ticket T-B2)** `S`-morphisms into the constant scheme `∐_A S` over `g : T ⟶ S` are the locally constant `A`-valued functions on `T`.
[DATA]
```lean
def constSchemePointsEquiv (S : Scheme.{u}) (A : Type) [Finite A] {T : Scheme.{u}}
    (g : T ⟶ S) :
    { h : T ⟶ constScheme S A // h ≫ constSchemeπ S A = g } ≃ LocallyConstant T A where
```

-- Naturality of the constant-scheme points description: restriction along `k : T' ⟶ T` is composition with `k` on locally constant functions.
[PROVED]
```lean
lemma constSchemePointsEquiv_natural (S : Scheme.{u}) (A : Type) [Finite A]
    {T T' : Scheme.{u}} (g : T ⟶ S) (k : T' ⟶ T)
    (h : { h : T ⟶ constScheme S A // h ≫ constSchemeπ S A = g }) :
    constSchemePointsEquiv S A (k ≫ g) ⟨k ≫ h.1, by rw [Category.assoc, h.2]⟩ =
      (constSchemePointsEquiv S A g h).comap k.base.hom :=
```

-- **(DS3b, ticket T-B2)** The group structure on the constant group scheme `(ℤ/N)_S`, induced by representability from the presheaf of locally constant `ℤ/N`-valued functions.
[DATA]
```lean
noncomputable instance constZModGrpObj (S : Scheme.{u}) (N : ℕ) [NeZero N] :
    GrpObj (Over.mk (constSchemeπ S (ZMod N))) :=
```

-- **(DS3c / T-B2a, specification of DS3a)** The canonical points description of `μ_{N,S}`: for `T ⟶ S`, the `T`-points of `μ_{N,S}` over `S` are the `N`-th roots of unity of `Γ(T, O_T)`.
[DATA]
```lean
noncomputable def muNPointsEquiv (S : Scheme.{u}) (N : ℕ) [NeZero N] {T : Scheme.{u}}
    (g : T ⟶ S) :
    { h : T ⟶ muN S N // h ≫ muNπ S N = g } ≃ { a : Γ(T, ⊤) // a ^ N = 1 } :=
```

-- **(T-B7)** `μ_{N,S} ⟶ S` is finite locally free of rank `N`, étale iff `N` is invertible on `S`. (Finiteness.)
[PROVED]
```lean
theorem muNπ_isFinite (S : Scheme.{u}) (N : ℕ) [NeZero N] : IsFinite (muNπ S N) :=
```

-- **(T-B7)** `μ_{N,S} ⟶ S` is flat, of constant rank `N`.
[PROVED]
```lean
theorem muNπ_flat (S : Scheme.{u}) (N : ℕ) [NeZero N] : Flat (muNπ S N) :=
```

[PROVED]
```lean
theorem muNπ_finrank (S : Scheme.{u}) (N : ℕ) [NeZero N] (s : S) :
    (muNπ S N).finrank s = N :=
```

[PROVED]
```lean
theorem muNπ_etale_iff (S : Scheme.{u}) (N : ℕ) [NeZero N] :
    Etale (muNπ S N) ↔ IsUnit (N : Γ(S, ⊤)) :=
```

-- **(T-B2, DS3 naturality spec — register rule (iii))** The points description of `μ_N` is natural: restriction along `k : T' ⟶ T` corresponds to applying `Γ`-map.
[PROVED]
```lean
theorem muNPointsEquiv_natural (S : Scheme.{u}) (N : ℕ) [NeZero N]
    {T T' : Scheme.{u}} (g : T ⟶ S) (k : T' ⟶ T)
    (h : { h : T ⟶ muN S N // h ≫ muNπ S N = g }) :
    (muNPointsEquiv S N (k ≫ g) ⟨k ≫ h.1, by rw [Category.assoc, h.2]⟩ : Γ(T', ⊤)) =
      (Scheme.Γ.map k.op).hom (muNPointsEquiv S N g h : Γ(T, ⊤)) :=
```

-- **(T-B2, DS3a group-law pin)** The points description of `μ_{N,S}` sends the unit of the group structure `muNGrpObj` to `1`.
[PROVED]
```lean
theorem muNPointsEquiv_one (S : Scheme.{u}) (N : ℕ) [NeZero N] {T : Scheme.{u}}
    (g : T ⟶ S) :
    letI : Monoid (Over.mk g ⟶ Over.mk (muNπ S N)) := Hom.monoid
    (muNPointsEquiv S N g ⟨(1 : Over.mk g ⟶ Over.mk (muNπ S N)).left, Over.w _⟩ :
      Γ(T, ⊤)) = 1 :=
```

-- **(T-B2, DS3a group-law pin — register rule (iii))** The points description of `μ_{N,S}` is multiplicative: the group structure `muNGrpObj` is, on `T`-points, multiplication of `N`-th roots of unity in `Γ(T, ⊤)`.
[PROVED]
```lean
theorem muNPointsEquiv_mul (S : Scheme.{u}) (N : ℕ) [NeZero N] {T : Scheme.{u}}
    (g : T ⟶ S) (f₁ f₂ : Over.mk g ⟶ Over.mk (muNπ S N)) :
    letI : Monoid (Over.mk g ⟶ Over.mk (muNπ S N)) := Hom.monoid
    (muNPointsEquiv S N g ⟨(f₁ * f₂).left, Over.w _⟩ : Γ(T, ⊤)) =
      (muNPointsEquiv S N g ⟨f₁.left, Over.w f₁⟩ : Γ(T, ⊤)) *
        (muNPointsEquiv S N g ⟨f₂.left, Over.w f₂⟩ : Γ(T, ⊤)) :=
```

Declarations: 18

---

## ModularCurves/WeilPairing/Basic.lean  (135 lines)

The Weil pairing over a base scheme (KM 2.8): `e_N : E[N] ×_S E[N] ⟶ μ_N` registered as canonical data (DS4, a data-sorry) together with its specification statements (bilinearity, alternating, fibrewise nondegeneracy, base-change naturality, divisibility, symplectic formula) — all sorried.

Context: `open AlgebraicGeometry CategoryTheory Limits`; local Over instances; `namespace ModularCurves`, `namespace EllipticCurve`, `variable {S : Scheme.{u}} (E : EllipticCurve S)`.

-- **(DS4, ticket chain T-C1)** The Weil pairing of `E[N]`, as an `S`-morphism `E[N] ×_S E[N] ⟶ μ_{N,S}`. DATA-SORRY (register entry DS4).
[DATA-SORRY]
```lean
noncomputable def weilPairing (N : ℕ) [NeZero N] :
    pullback (E.torsionπ N) (E.torsionπ N) ⟶ muN S N := sorry
```

-- **(T-C1a, specification of DS4)** The Weil pairing is a morphism over `S`.
[SORRY]
```lean
theorem weilPairing_over (N : ℕ) [NeZero N] :
    E.weilPairing N ≫ muNπ S N = pullback.fst _ _ ≫ E.torsionπ N :=
```

-- Pair two `T`-points of `E[N]` into a `T`-point of `E[N] ×_S E[N]`, and evaluate the Weil pairing, landing in the `N`-th roots of unity of `Γ(T, O_T)` via the points description of `μ_N`.
[DATA] (real construction; consumes the DS4 sorried data)
```lean
noncomputable def weilPairingEval {N : ℕ} [NeZero N] {T : Scheme.{u}} {g : T ⟶ S}
    (x y : E.Point g)
    (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero) (hy : y.1 ≫ E.mulByHom N = g ≫ E.zero) :
    { a : Γ(T, ⊤) // a ^ N = 1 } :=
```

-- **(T-C2 = KM 2.8, bilinearity)** `e_N(x + x', y) = e_N(x, y) · e_N(x', y)` on `T`-points.
[SORRY]
```lean
theorem weilPairingEval_add_left {N : ℕ} [NeZero N] {T : Scheme.{u}} {g : T ⟶ S}
    (x x' y : E.Point g) (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero)
    (hx' : x'.1 ≫ E.mulByHom N = g ≫ E.zero) (hy : y.1 ≫ E.mulByHom N = g ≫ E.zero)
    (hxx' : (x + x').1 ≫ E.mulByHom N = g ≫ E.zero) :
    (E.weilPairingEval (x + x') y hxx' hy : Γ(T, ⊤)) =
      E.weilPairingEval x y hx hy * E.weilPairingEval x' y hx' hy :=
```

-- **(T-C2′ = KM 2.8, alternating)** `e_N(x, x) = 1`.
[SORRY]
```lean
theorem weilPairingEval_self {N : ℕ} [NeZero N] {T : Scheme.{u}} {g : T ⟶ S}
    (x : E.Point g) (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero) :
    (E.weilPairingEval x x hx hx : Γ(T, ⊤)) = 1 :=
```

-- **(T-C3 = KM 2.8, fibrewise nondegeneracy)** On every geometric point of `S`, the pairing is nondegenerate: a torsion point pairing trivially with everything is zero.
[SORRY]
```lean
theorem weilPairingEval_nondegenerate {N : ℕ} [NeZero N]
    (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (.of k) ⟶ S)
    (x : E.Point t) (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero)
    (h : ∀ (y : E.Point t) (hy : y.1 ≫ E.mulByHom N = t ≫ E.zero),
      (E.weilPairingEval x y hx hy : Γ(Spec (.of k), ⊤)) = 1) :
    x = E.zeroPoint t :=
```

-- **(T-C2a, base-change naturality — required pinning spec per expert review Q4)** Restriction along `k : T' ⟶ T` commutes with the pairing.
[SORRY]
```lean
theorem weilPairingEval_restrict {N : ℕ} [NeZero N] {T T' : Scheme.{u}} {g : T ⟶ S}
    (k : T' ⟶ T) (x y : E.Point g)
    (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero) (hy : y.1 ≫ E.mulByHom N = g ≫ E.zero)
    (hx' : (Point.restrict E k x).1 ≫ E.mulByHom N = (k ≫ g) ≫ E.zero)
    (hy' : (Point.restrict E k y).1 ≫ E.mulByHom N = (k ≫ g) ≫ E.zero) :
    (E.weilPairingEval (Point.restrict E k x) (Point.restrict E k y) hx' hy' : Γ(T', ⊤))
      = (Scheme.Γ.map k.op).hom (E.weilPairingEval x y hx hy : Γ(T, ⊤)) :=
```

-- **(T-C2b, divisibility — expert review Q5)** For points killed by `N`, the `N·M`-pairing is the `M`-th power of the `N`-pairing.
[SORRY]
```lean
theorem weilPairingEval_mul {N M : ℕ} [NeZero N] [NeZero M] {T : Scheme.{u}}
    {g : T ⟶ S} (x y : E.Point g)
    (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero) (hy : y.1 ≫ E.mulByHom N = g ≫ E.zero)
    (hx' : x.1 ≫ E.mulByHom (N * M) = g ≫ E.zero)
    (hy' : y.1 ≫ E.mulByHom (N * M) = g ≫ E.zero) :
    (haveI : NeZero (N * M) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩;
      (E.weilPairingEval (N := N * M) x y hx' hy' : Γ(T, ⊤))) =
      (E.weilPairingEval (N := N) x y hx hy : Γ(T, ⊤)) ^ M :=
```

-- **(T-C2c, the symplectic-formula pin — expert review Q6, Silverman convention)** On a pair of torsion points, `e_N(aP + bQ, cP + dQ) = e_N(P,Q)^{ad − bc}` (exponent taken mod `N`).
[SORRY]
```lean
theorem weilPairingEval_symplectic {N : ℕ} [NeZero N] {T : Scheme.{u}} {g : T ⟶ S}
    (P Q : E.Point g) (a b c d : ℤ)
    (hP : P.1 ≫ E.mulByHom N = g ≫ E.zero) (hQ : Q.1 ≫ E.mulByHom N = g ≫ E.zero)
    (h₁ : (a • P + b • Q).1 ≫ E.mulByHom N = g ≫ E.zero)
    (h₂ : (c • P + d • Q).1 ≫ E.mulByHom N = g ≫ E.zero) :
    (E.weilPairingEval (a • P + b • Q) (c • P + d • Q) h₁ h₂ : Γ(T, ⊤)) =
      (E.weilPairingEval P Q hP hQ : Γ(T, ⊤)) ^ (((a * d - b * c) % (N : ℤ)).toNat) :=
```

Declarations: 9

---

## ModularCurves/WeilPairing/EtaleDescent.lean  (489 lines)

The char-0 étale-descent Weil pairing (T-C0): `E[N]` and `μ_N` over a field packaged as finite étale `k`-algebras with pinned fibre-functor values, the Galois-descent theorem turning a `Gal`-equivariant map of fibres into an algebra morphism, and the scheme-level field-base pairing statement (sorried).

Context: `open AlgebraicGeometry CategoryTheory Limits`, `open scoped TensorProduct`, `universe u`, `namespace ModularCurves` (with `namespace EllipticCurve` around the torsion-side declarations).

-- **(T-C0a)** The `N`-torsion of an elliptic curve over a field, as a finite étale `k`-algebra.
[DATA]
```lean
noncomputable def torsionAlgebra (k : Type u) [Field k]
    (E : EllipticCurve (Spec (CommRingCat.of k))) (N : ℕ) [NeZero N]
    (hk : (N : k) ≠ 0) : CommAlgCat.FiniteEtale.{u} k :=
```

-- **(T-C0b)** The `k̄`-points of the torsion algebra are the `N`-torsion of the geometric point group.
[PROVED]
```lean
theorem torsionAlgebraPointsEquiv (k : Type u) [Field k]
    (E : EllipticCurve (Spec (CommRingCat.of k))) (N : ℕ) [NeZero N]
    (hk : (N : k) ≠ 0) :
    Nonempty (((torsionAlgebra k E N hk).obj →ₐ[k] AlgebraicClosure k) ≃
      Submodule.torsionBy ℤ
        (E.Point (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))
        (N : ℤ)) :=
```

-- **(T-C0d-i, μ side)** `μ_N` over `Spec k` as a finite étale `k`-algebra, for `N` invertible in `k`.
[DATA]
```lean
noncomputable def muNAlgebra (k : Type u) [Field k] (N : ℕ) [NeZero N]
    (hk : (N : k) ≠ 0) : CommAlgCat.FiniteEtale.{u} k :=
```

-- The affine `Γ ⊣ Spec` fibre correspondence over `Spec k`: for an affine scheme `X` over `Spec k` whose global sections carry the induced `k`-algebra structure, `k`-algebra homomorphisms `Γ(X, ⊤) →ₐ[k] R` are exactly the `Spec R`-points of `X` over `Spec k`.
[DATA]
```lean
noncomputable def algHomEquivSpecOver {k : Type u} [Field k] (R : Type u) [CommRing R]
    [Algebra k R] {X : Scheme.{u}} [IsAffine X] (π : X ⟶ Spec (CommRingCat.of k))
    [Algebra k Γ(X, ⊤)]
    (halg : CommRingCat.ofHom (algebraMap k Γ(X, ⊤)) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ π.appTop) :
    (Γ(X, ⊤) →ₐ[k] R) ≃
      { h : Spec (CommRingCat.of R) ⟶ X //
        h ≫ π = Spec.map (CommRingCat.ofHom (algebraMap k R)) } :=
```

-- **(T-C0d-i, μ side, fibre pin)** The `k̄`-points of the `μ_N`-algebra are the `N`-th roots of unity of `k̄`.
[PROVED]
```lean
theorem muNAlgebraPointsEquiv (k : Type u) [Field k] (N : ℕ) [NeZero N]
    (hk : (N : k) ≠ 0) :
    Nonempty (((muNAlgebra k N hk).obj →ₐ[k] AlgebraicClosure k) ≃
      { a : AlgebraicClosure k // a ^ N = 1 }) :=
```

-- Splitting the fibre of a tensor product: `k`-algebra homomorphisms out of `A ⊗[k] B` into a commutative `k`-algebra are pairs of homomorphisms on the factors.
[DATA]
```lean
noncomputable def tensorAlgHomPairEquiv (k A B Ω : Type u) [CommRing k] [CommRing A]
    [CommRing B] [CommRing Ω] [Algebra k A] [Algebra k B] [Algebra k Ω] :
    ((A ⊗[k] B) →ₐ[k] Ω) ≃ (A →ₐ[k] Ω) × (B →ₐ[k] Ω) where
```

-- **(T-C0d-i, descent heart)** Fullness of the Galois correspondence, unbundled: a `Gal(k^sep/k)`-equivariant map between the fibre-functor values of two finite étale `k`-algebras descends to a morphism of algebras inducing it by precomposition.
[PROVED]
```lean
theorem exists_finiteEtaleHom_of_galoisEquivariant {k : Type u} [Field k]
    (A B : CommAlgCat.FiniteEtale.{u} k)
    (q : ((B : Type u) →ₐ[k] SeparableClosure k) →
      ((A : Type u) →ₐ[k] SeparableClosure k))
    (hq : ∀ (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k)
        (x : (B : Type u) →ₐ[k] SeparableClosure k),
      q (σ.toAlgHom.comp x) = σ.toAlgHom.comp (q x)) :
    ∃ w : A ⟶ B, ∀ x : (B : Type u) →ₐ[k] SeparableClosure k,
      q x = x.comp w.hom.hom :=
```

-- **(T-C0d-i, pair side)** `E[N] ×_{Spec k} E[N]` as a finite étale `k`-algebra: the tensor product `torsionAlgebra ⊗[k] torsionAlgebra`.
[DATA]
```lean
noncomputable def torsionPairAlgebra (k : Type u) [Field k]
    (E : EllipticCurve (Spec (CommRingCat.of k))) (N : ℕ) [NeZero N]
    (hk : (N : k) ≠ 0) : CommAlgCat.FiniteEtale.{u} k :=
```

-- **(T-C0d-i, pair side, fibre pin)** The fibre-functor value of the pair algebra splits as the product of two copies of the fibre of `torsionAlgebra`.
[DATA]
```lean
noncomputable def torsionPairAlgebraPointsEquiv (k : Type u) [Field k]
    (E : EllipticCurve (Spec (CommRingCat.of k))) (N : ℕ) [NeZero N]
    (hk : (N : k) ≠ 0) :
    ((torsionPairAlgebra k E N hk).obj →ₐ[k] AlgebraicClosure k) ≃
      ((torsionAlgebra k E N hk).obj →ₐ[k] AlgebraicClosure k) ×
        ((torsionAlgebra k E N hk).obj →ₐ[k] AlgebraicClosure k) :=
```

-- **(T-C0d-i, packaging)** The gate-free Galois-descent transport for the Weil pairing: any `Gal(k̄/k)`-equivariant map from pairs of `k̄`-points of `E[N]` to `k̄`-points of `μ_N` is induced by an actual morphism `muNAlgebra ⟶ torsionPairAlgebra` of finite étale `k`-algebras.
[PROVED]
```lean
theorem exists_pairingAlgebraHom_of_galoisEquivariant (k : Type u) [Field k]
    [CharZero k] (E : EllipticCurve (Spec (CommRingCat.of k))) (N : ℕ) [NeZero N]
    (hk : (N : k) ≠ 0)
    (p : ((torsionAlgebra k E N hk).obj →ₐ[k] AlgebraicClosure k) ×
          ((torsionAlgebra k E N hk).obj →ₐ[k] AlgebraicClosure k) →
        ((muNAlgebra k N hk).obj →ₐ[k] AlgebraicClosure k))
    (hp : ∀ (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
        (x : ((torsionAlgebra k E N hk).obj →ₐ[k] AlgebraicClosure k) ×
          ((torsionAlgebra k E N hk).obj →ₐ[k] AlgebraicClosure k)),
      p (σ.toAlgHom.comp x.1, σ.toAlgHom.comp x.2) = σ.toAlgHom.comp (p x)) :
    ∃ w : muNAlgebra k N hk ⟶ torsionPairAlgebra k E N hk,
      ∀ f : ((torsionPairAlgebra k E N hk).obj →ₐ[k] AlgebraicClosure k),
        f.comp w.hom.hom = p (torsionPairAlgebraPointsEquiv k E N hk f) :=
```

-- **(T-C0e)** The étale-descent Weil pairing over a characteristic-zero field base: the scheme-level pairing morphism with the same API as the DS4 register entry.
[SORRY]
```lean
theorem exists_weilPairingSpecField (k : Type u) [Field k] [CharZero k]
    (E : EllipticCurve (Spec (CommRingCat.of k))) (N : ℕ) [NeZero N] :
    ∃ w : pullback (E.torsionπ N) (E.torsionπ N) ⟶ muN (Spec (CommRingCat.of k)) N,
      w ≫ muNπ _ N = pullback.fst _ _ ≫ E.torsionπ N :=
```

Declarations: 11

---

## ModularCurves/WeilPairing/GaloisEquivariance.lean  (889 lines)

Galois equivariance of the HasseWeil field-level Weil pairing (T-C0c): for a curve-fixing base-field automorphism `σ`, `σ(e_ℓ(S,T)) = e_ℓ(σ•S, σ•T)`, built through the σ-induced function-field automorphism, the coordinatewise point action, translation conjugation, divisor Galois descent, and the constant-ratio core.

Context: `open WeierstrassCurve Polynomial IsDedekindDomain HasseWeil HasseWeil.Curves HasseWeil.WeilPairing`; `namespace ModularCurves`, `namespace WeilPairingGalois`; `set_option linter.unusedSectionVars false`, `set_option linter.style.longLine false`; `variable {F : Type*} [Field F] [DecidableEq F]`, `variable (W : WeierstrassCurve F) (σ : F ≃+* F)`. Section `Generators`/`Conjugation`/`DivisorDescent` additionally `variable [W.toAffine.IsElliptic]`; `DivisorDescent` (from `pointValuation_functionFieldEquiv` on) also `variable [IsAlgClosed F] [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing]`; section `Main` has all three.

-- **`CoordinateRing.map σ` is surjective** for a ring equivalence `σ` of the base field.
[PROVED]
```lean
theorem coordRingMap_surjective_of_ringEquiv :
    Function.Surjective
      (WeierstrassCurve.Affine.CoordinateRing.map W.toAffine σ.toRingHom) :=
```

-- **`CoordinateRing.map σ` is bijective** for a ring equivalence `σ` of the base field.
[PROVED]
```lean
theorem coordRingMap_bijective_of_ringEquiv :
    Function.Bijective
      (WeierstrassCurve.Affine.CoordinateRing.map W.toAffine σ.toRingHom) :=
```

-- The coordinate-ring automorphism `F[E] ≃+* F[E.map σ]` packaging the bijective `CoordinateRing.map σ`.
[DATA]
```lean
noncomputable def coordRingEquiv :
    W.toAffine.CoordinateRing ≃+* (W.map σ.toRingHom).toAffine.CoordinateRing :=
```

[PROVED]
```lean
@[simp] theorem coordRingEquiv_apply (z : W.toAffine.CoordinateRing) :
    coordRingEquiv W σ z =
      WeierstrassCurve.Affine.CoordinateRing.map W.toAffine σ.toRingHom z :=
```

-- The raw function-field equivalence `F(E) ≃+* F(E.map σ)`, lifting `coordRingEquiv` to fraction fields.
[DATA]
```lean
noncomputable def functionFieldEquivRaw :
    W.toAffine.FunctionField ≃+* (W.map σ.toRingHom).toAffine.FunctionField :=
```

-- The codomain cast `F(E.map σ) ≃+* F(E)` along the curve-fixing equation `hW`.
[DATA]
```lean
noncomputable def functionFieldCast (hW : W.map σ.toRingHom = W) :
    (W.map σ.toRingHom).toAffine.FunctionField ≃+* W.toAffine.FunctionField :=
```

-- **The function-field automorphism `σ_KE : F(E) ≃+* F(E)`** induced by a base-field automorphism `σ` fixing the curve.
[DATA]
```lean
noncomputable def functionFieldEquiv (hW : W.map σ.toRingHom = W) :
    W.toAffine.FunctionField ≃+* W.toAffine.FunctionField :=
```

-- `functionFieldEquivRaw` acts by `σ` on base constants (into the mapped curve's function field).
[PROVED]
```lean
theorem functionFieldEquivRaw_algebraMap (a : F) :
    functionFieldEquivRaw W σ (algebraMap F W.toAffine.FunctionField a) =
      algebraMap F (W.map σ.toRingHom).toAffine.FunctionField (σ a) :=
```

-- The codomain cast fixes base constants.
[PROVED]
```lean
theorem functionFieldCast_algebraMap (hW : W.map σ.toRingHom = W) (b : F) :
    functionFieldCast W σ hW
        (algebraMap F (W.map σ.toRingHom).toAffine.FunctionField b) =
      algebraMap F W.toAffine.FunctionField b :=
```

-- **`σ_KE` acts by `σ` on constants**: `σ_KE (algebraMap a) = algebraMap (σ a)`.
[PROVED]
```lean
theorem functionFieldEquiv_algebraMap (hW : W.map σ.toRingHom = W) (a : F) :
    functionFieldEquiv W σ hW (algebraMap F W.toAffine.FunctionField a) =
      algebraMap F W.toAffine.FunctionField (σ a) :=
```

-- `σ_KE` fixes the generator `x_gen` (the coordinate function `x` is defined over the prime field).
[PROVED]
```lean
theorem functionFieldEquiv_x_gen (hW : W.map σ.toRingHom = W) :
    functionFieldEquiv W σ hW (x_gen W) = x_gen W :=
```

-- `σ_KE` fixes the generator `y_gen`.
[PROVED]
```lean
theorem functionFieldEquiv_y_gen (hW : W.map σ.toRingHom = W) :
    functionFieldEquiv W σ hW (y_gen W) = y_gen W :=
```

-- Nonsingularity is preserved by a curve-fixing base automorphism: `(x, y)` nonsingular on `W` implies `(σ x, σ y)` nonsingular on `W`.
[PROVED]
```lean
theorem nonsingular_ringEquiv (hW : W.map σ.toRingHom = W) {x y : F}
    (h : W.toAffine.Nonsingular x y) : W.toAffine.Nonsingular (σ x) (σ y) :=
```

-- The cast of affine points along an equality of Weierstrass curves, as an `AddMonoidHom` (additivity is definitional after `subst`).
[DATA]
```lean
noncomputable def pointCastHom {V₁ V₂ : WeierstrassCurve F} (h : V₁ = V₂) :
    V₁.toAffine.Point →+ V₂.toAffine.Point where
```

-- `pointCastHom` on an affine point keeps the coordinates (the nonsingularity proof is transported by proof irrelevance).
[PROVED]
```lean
theorem pointCastHom_some {V₁ V₂ : WeierstrassCurve F} (h : V₁ = V₂) {x y : F}
    (hn : V₁.toAffine.Nonsingular x y) (hn' : V₂.toAffine.Nonsingular x y) :
    pointCastHom h (.some x y hn) = .some x y hn' :=
```

-- **The point action of a curve-fixing base automorphism**, as an `AddMonoidHom`: `σ • (x, y) = (σ x, σ y)` and `σ • O = O`.
[DATA]
```lean
noncomputable def pointHom (hW : W.map σ.toRingHom = W) :
    W.toAffine.Point →+ W.toAffine.Point :=
```

[PROVED]
```lean
@[simp] theorem pointHom_zero (hW : W.map σ.toRingHom = W) :
    pointHom W σ hW 0 = 0 :=
```

-- `pointHom` on an affine point: `σ • (x, y) = (σ x, σ y)`.
[PROVED]
```lean
theorem pointHom_some (hW : W.map σ.toRingHom = W) {x y : F}
    (h : W.toAffine.Nonsingular x y) (h' : W.toAffine.Nonsingular (σ x) (σ y)) :
    pointHom W σ hW (.some x y h) = .some (σ x) (σ y) h' :=
```

-- The point action transports `ℓ`-torsion: `ℓ • S = 0 → ℓ • (σ • S) = 0`.
[PROVED]
```lean
theorem pointHom_smul_eq_zero (hW : W.map σ.toRingHom = W) (ℓ : ℤ)
    {S : W.toAffine.Point} (hS : ℓ • S = 0) : ℓ • pointHom W σ hW S = 0 :=
```

-- The point action is injective.
[PROVED]
```lean
theorem pointHom_injective (hW : W.map σ.toRingHom = W) :
    Function.Injective (pointHom W σ hW) :=
```

-- The inverse automorphism also fixes the curve: `W.map σ.symm = W` from `W.map σ = W`.
[PROVED]
```lean
theorem map_symm_eq (hW : W.map σ.toRingHom = W) : W.map σ.symm.toRingHom = W :=
```

-- `σ_KE` fixes the base-changed curve `W_KE W = W.map (algebraMap F F(E))`.
[PROVED]
```lean
theorem mapKE_functionFieldEquiv_eq (hW : W.map σ.toRingHom = W) :
    (W_KE W).map (functionFieldEquiv W σ hW).toRingHom = W_KE W :=
```

-- **Generic σ-equivariance of the translation formulas** for a ring endomorphism `φ` of the function field that fixes the base-changed curve, fixes the generators, and acts by `σ` on base constants.
[PROVED]
```lean
theorem ringHom_translate_formulas
    (φ : W.toAffine.FunctionField →+* W.toAffine.FunctionField)
    (hφW : (W_KE W).map φ = W_KE W)
    (hφx : φ (x_gen W) = x_gen W) (hφy : φ (y_gen W) = y_gen W)
    (hφc : ∀ a : F, φ (algebraMap F W.toAffine.FunctionField a) =
      algebraMap F W.toAffine.FunctionField (σ a)) (xk yk : F) :
    φ (translateSlope_xy W xk yk) = translateSlope_xy W (σ xk) (σ yk) ∧
      φ (translateX_xy W xk yk) = translateX_xy W (σ xk) (σ yk) ∧
      φ (translateY_xy W xk yk) = translateY_xy W (σ xk) (σ yk) :=
```

-- `σ_KE` is equivariant on the translation formulas: `σ_KE (translate•_xy xk yk) = translate•_xy (σ xk) (σ yk)`.
[PROVED]
```lean
theorem functionFieldEquiv_translate_formulas (hW : W.map σ.toRingHom = W) (xk yk : F) :
    functionFieldEquiv W σ hW (translateSlope_xy W xk yk) =
        translateSlope_xy W (σ xk) (σ yk) ∧
      functionFieldEquiv W σ hW (translateX_xy W xk yk) =
        translateX_xy W (σ xk) (σ yk) ∧
      functionFieldEquiv W σ hW (translateY_xy W xk yk) =
        translateY_xy W (σ xk) (σ yk) :=
```

-- The `S = 0` case of the translation conjugation, for any `g`: since `τ_0` is the identity, both sides are `σ_KE g`.
[PROVED]
```lean
theorem conj_gen_zero (hW : W.map σ.toRingHom = W) (g : W.toAffine.FunctionField) :
    functionFieldEquiv W σ hW (translateAlgEquivOfPoint W Affine.Point.zero g) =
      translateAlgEquivOfPoint W (pointHom W σ hW Affine.Point.zero)
        (functionFieldEquiv W σ hW g) :=
```

-- The translation conjugation on the generator `x_gen`: `σ_KE (τ_S (x_gen)) = τ_{σ•S} (σ_KE (x_gen))`.
[PROVED]
```lean
theorem conj_x_gen (hW : W.map σ.toRingHom = W) (S : W.toAffine.Point) :
    functionFieldEquiv W σ hW (translateAlgEquivOfPoint W S (x_gen W)) =
      translateAlgEquivOfPoint W (pointHom W σ hW S)
        (functionFieldEquiv W σ hW (x_gen W)) :=
```

-- The translation conjugation on the generator `y_gen`: `σ_KE (τ_S (y_gen)) = τ_{σ•S} (σ_KE (y_gen))`.
[PROVED]
```lean
theorem conj_y_gen (hW : W.map σ.toRingHom = W) (S : W.toAffine.Point) :
    functionFieldEquiv W σ hW (translateAlgEquivOfPoint W S (y_gen W)) =
      translateAlgEquivOfPoint W (pointHom W σ hW S)
        (functionFieldEquiv W σ hW (y_gen W)) :=
```

-- The application form of `(σ_KE.toRingHom.comp τ_S.toRingHom) g`.
[PROVED]
```lean
theorem equiv_comp_translate_apply (hW : W.map σ.toRingHom = W)
    (S : W.toAffine.Point) (g : W.toAffine.FunctionField) :
    ((functionFieldEquiv W σ hW).toRingHom.comp
        (translateAlgEquivOfPoint W S).toRingEquiv.toRingHom) g =
      functionFieldEquiv W σ hW (translateAlgEquivOfPoint W S g) :=
```

-- The application form of `(τ_{σ•S}.toRingHom.comp σ_KE.toRingHom) g`.
[PROVED]
```lean
theorem translate_comp_equiv_apply (hW : W.map σ.toRingHom = W)
    (S : W.toAffine.Point) (g : W.toAffine.FunctionField) :
    ((translateAlgEquivOfPoint W (pointHom W σ hW S)).toRingEquiv.toRingHom.comp
        (functionFieldEquiv W σ hW).toRingHom) g =
      translateAlgEquivOfPoint W (pointHom W σ hW S)
        (functionFieldEquiv W σ hW g) :=
```

-- The translation conjugation as a ring-hom composition equality, via extensionality on the base and the generators.
[PROVED]
```lean
theorem functionFieldEquiv_comp_translate_eq (hW : W.map σ.toRingHom = W)
    (S : W.toAffine.Point) :
    (functionFieldEquiv W σ hW).toRingHom.comp
        (translateAlgEquivOfPoint W S).toRingEquiv.toRingHom =
      (translateAlgEquivOfPoint W (pointHom W σ hW S)).toRingEquiv.toRingHom.comp
        (functionFieldEquiv W σ hW).toRingHom :=
```

-- **The translation conjugation, pointwise**: `σ_KE (τ_S g) = τ_{σ•S} (σ_KE g)`.
[PROVED]
```lean
theorem functionFieldEquiv_conj (hW : W.map σ.toRingHom = W)
    (S : W.toAffine.Point) (g : W.toAffine.FunctionField) :
    functionFieldEquiv W σ hW (translateAlgEquivOfPoint W S g) =
      translateAlgEquivOfPoint W (pointHom W σ hW S)
        (functionFieldEquiv W σ hW g) :=
```

-- `coordRingEquiv` sends `maximalIdealAt P` to `maximalIdealAt Q` on the mapped curve, where `Q` has coordinates `(σ P.x, σ P.y)`.
[PROVED]
```lean
theorem map_maximalIdealAt_coordRingEquiv
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint)
    (Q : (⟨(W.map σ.toRingHom).toAffine⟩ : SmoothPlaneCurve F).SmoothPoint)
    (hQx : Q.x = σ P.x) (hQy : Q.y = σ P.y) :
    Ideal.map (coordRingEquiv W σ).toRingHom
        ((⟨W.toAffine⟩ : SmoothPlaneCurve F).maximalIdealAt P) =
      (⟨(W.map σ.toRingHom).toAffine⟩ : SmoothPlaneCurve F).maximalIdealAt Q :=
```

-- The smooth point of the mapped curve `W.map σ` with the same coordinates as `P` (the nonsingularity transported along `hW`).
[DATA]
```lean
noncomputable def pointOnMapped (hW : W.map σ.toRingHom = W)
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) :
    (⟨(W.map σ.toRingHom).toAffine⟩ : SmoothPlaneCurve F).SmoothPoint where
```

[PROVED]
```lean
@[simp] theorem pointOnMapped_x (hW : W.map σ.toRingHom = W)
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) :
    (pointOnMapped W σ hW P).x = P.x :=
```

[PROVED]
```lean
@[simp] theorem pointOnMapped_y (hW : W.map σ.toRingHom = W)
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) :
    (pointOnMapped W σ hW P).y = P.y :=
```

-- **Affine order transport for `σ_KE`**: for smooth points `P, Q` with `P = σ • Q` coordinatewise, `ord_P (σ_KE g) = ord_Q g` (as `pointValuation`s).
[PROVED]
```lean
theorem pointValuation_functionFieldEquiv (hW : W.map σ.toRingHom = W)
    (P Q : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint)
    (hPx : P.x = σ Q.x) (hPy : P.y = σ Q.y) (g : W.toAffine.FunctionField) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P
        (functionFieldEquiv W σ hW g) =
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation Q g :=
```

-- `coordRingEquiv` on the `F[X]`-basis decomposition `p • 1 + q • y`: it maps the coefficients through `Polynomial.map σ` and fixes the basis `{1, y}`.
[PROVED]
```lean
theorem coordRingEquiv_smul_basis (p q : Polynomial F) :
    coordRingEquiv W σ (p • (1 : W.toAffine.CoordinateRing) +
        q • WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine Polynomial.X) =
      (p.map σ.toRingHom) •
          (1 : (W.map σ.toRingHom).toAffine.CoordinateRing) +
        (q.map σ.toRingHom) •
          WeierstrassCurve.Affine.CoordinateRing.mk (W.map σ.toRingHom).toAffine
            Polynomial.X :=
```

-- **Norm transport for `coordRingEquiv`**: `N(coordRingEquiv u) = (N u).map σ`.
[PROVED]
```lean
theorem norm_coordRingEquiv (u : W.toAffine.CoordinateRing) :
    Algebra.norm (Polynomial F) (coordRingEquiv W σ u) =
      (Algebra.norm (Polynomial F) u).map σ.toRingHom :=
```

-- `ord_∞` of an integral element transports under `coordRingEquiv`.
[PROVED]
```lean
theorem ordAtInfty_algebraMap_coordRingEquiv (u : W.toAffine.CoordinateRing) :
    (⟨(W.map σ.toRingHom).toAffine⟩ : SmoothPlaneCurve F).ordAtInfty
        (algebraMap _ _ (coordRingEquiv W σ u)) =
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).ordAtInfty (algebraMap _ _ u) :=
```

-- The `ord_∞` transport for the raw lift `functionFieldEquivRaw`.
[PROVED]
```lean
theorem ordAtInfty_functionFieldEquivRaw (z : W.toAffine.FunctionField) :
    (⟨(W.map σ.toRingHom).toAffine⟩ : SmoothPlaneCurve F).ordAtInfty
        (functionFieldEquivRaw W σ z) =
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).ordAtInfty z :=
```

-- **`σ_KE` fixes the place at infinity**: `ord_∞ (σ_KE g) = ord_∞ g`.
[PROVED]
```lean
theorem ordAtInfty_functionFieldEquiv (hW : W.map σ.toRingHom = W)
    (g : W.toAffine.FunctionField) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).ordAtInfty (functionFieldEquiv W σ hW g) =
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).ordAtInfty g :=
```

-- The inverse-σ smooth point: coordinates `(σ⁻¹ P.x, σ⁻¹ P.y)` (so `σ • (this) = P`).
[DATA]
```lean
noncomputable def smoothPointInv (hW : W.map σ.toRingHom = W)
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint where
```

[PROVED]
```lean
@[simp] theorem smoothPointInv_x (hW : W.map σ.toRingHom = W)
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) :
    (smoothPointInv W σ hW P).x = σ.symm P.x :=
```

[PROVED]
```lean
@[simp] theorem smoothPointInv_y (hW : W.map σ.toRingHom = W)
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) :
    (smoothPointInv W σ hW P).y = σ.symm P.y :=
```

-- `σ • (smoothPointInv P) = P` at the affine-point level.
[PROVED]
```lean
theorem pointHom_smoothPointInv (hW : W.map σ.toRingHom = W)
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) :
    pointHom W σ hW
        (HasseWeil.Curves.SmoothPlaneCurve.SmoothPoint.toAffinePoint
          (smoothPointInv W σ hW P)) =
      HasseWeil.Curves.SmoothPlaneCurve.SmoothPoint.toAffinePoint P :=
```

-- `ord_P` transport restated via the inverse-σ point: `ord_P (σ_KE g) = ord_{σ⁻¹•P} g`.
[PROVED]
```lean
theorem ord_P_functionFieldEquiv (hW : W.map σ.toRingHom = W)
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint)
    (g : W.toAffine.FunctionField) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).ord_P P (functionFieldEquiv W σ hW g) =
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).ord_P (smoothPointInv W σ hW P) g :=
```

-- **Fibre-divisor place comparison** at an affine place: the coefficient of `[ℓ]^*(σ•T)` at `P` equals the coefficient of `[ℓ]^*(T)` at `σ⁻¹•P`.
[PROVED]
```lean
theorem pullbackDiv_smoothPointInv_eq (hW : W.map σ.toRingHom = W)
    (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (T : W.toAffine.Point)
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) :
    pullbackDiv (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom
        (mulByInt_ker_finite W ℓ hℓ) (pointHom W σ hW T)
        (ProjectiveSmoothPoint.affine P) =
      pullbackDiv (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom
        (mulByInt_ker_finite W ℓ hℓ) T
        (ProjectiveSmoothPoint.affine (smoothPointInv W σ hW P)) :=
```

-- **Fibre-divisor place comparison at infinity**: `[ℓ]^*(σ•T) ∞ = [ℓ]^*(T) ∞` (`0 = σ•T ⟺ 0 = T`).
[PROVED]
```lean
theorem pullbackDiv_pointHom_infinity (hW : W.map σ.toRingHom = W)
    (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (T : W.toAffine.Point) :
    pullbackDiv (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom
        (mulByInt_ker_finite W ℓ hℓ) (pointHom W σ hW T)
        ProjectiveSmoothPoint.infinity =
      pullbackDiv (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom
        (mulByInt_ker_finite W ℓ hℓ) T ProjectiveSmoothPoint.infinity :=
```

-- **Divisor Galois descent for the Weil function**: `div(σ_KE g_T) = div(g_{σ•T})`, compared place-by-place.
[PROVED]
```lean
theorem projectiveDivisorOf_functionFieldEquiv_weilFunction
    (hW : W.map σ.toRingHom = W) (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (T : W.toAffine.Point) (hT : ℓ • T = 0)
    (hσT : ℓ • pointHom W σ hW T = 0) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf
        (functionFieldEquiv W σ hW (weilFunction W ℓ hℓ T hT)) =
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf
        (weilFunction W ℓ hℓ (pointHom W σ hW T) hσT) :=
```

-- **σ-naturality of the Weil function**: `σ_KE (g_T) = c · g_{σ•T}` for a nonzero `c : F` (equal divisors, so the ratio is a nonzero constant).
[PROVED]
```lean
theorem functionFieldEquiv_weilFunction_eq_smul (hW : W.map σ.toRingHom = W)
    (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (T : W.toAffine.Point) (hT : ℓ • T = 0)
    (hσT : ℓ • pointHom W σ hW T = 0) :
    ∃ c : F, c ≠ 0 ∧
      functionFieldEquiv W σ hW (weilFunction W ℓ hℓ T hT) =
        algebraMap F W.toAffine.FunctionField c *
          weilFunction W ℓ hℓ (pointHom W σ hW T) hσT :=
```

-- **The σ-action constant-ratio core** (the σ-variant of `weilPairing_galois_core`): the pairing transforms by `e_ℓ(S', T') = σ (e_ℓ(S, T))`.
[PROVED]
```lean
theorem weilPairing_ringEquiv_core (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (σKE : W.toAffine.FunctionField ≃+* W.toAffine.FunctionField)
    (S T S' T' : W.toAffine.Point)
    (hS : ℓ • S = 0) (hT : ℓ • T = 0) (hS' : ℓ • S' = 0) (hT' : ℓ • T' = 0)
    (hconj : σKE (translateAlgEquivOfPoint W S (weilFunction W ℓ hℓ T hT)) =
      translateAlgEquivOfPoint W S' (σKE (weilFunction W ℓ hℓ T hT)))
    {c : F} (hc : c ≠ 0)
    (hnat : σKE (weilFunction W ℓ hℓ T hT) =
      algebraMap F W.toAffine.FunctionField c * weilFunction W ℓ hℓ T' hT')
    (hact : ∀ a : F, σKE (algebraMap F W.toAffine.FunctionField a) =
      algebraMap F W.toAffine.FunctionField (σ a)) :
    weilPairing W ℓ hℓ S' T' hS' hT' = σ (weilPairing W ℓ hℓ S T hS hT) :=
```

-- **Galois equivariance of the field-level Weil pairing (T-C0c)**: for a ring automorphism `σ : F ≃+* F` fixing the curve, `σ (e_ℓ(S, T)) = e_ℓ(σ • S, σ • T)`.
[PROVED]
```lean
theorem weilPairing_galois_equivariant (hW : W.map σ.toRingHom = W)
    (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (S T : W.toAffine.Point)
    (hS : ℓ • S = 0) (hT : ℓ • T = 0) :
    σ (weilPairing W ℓ hℓ S T hS hT) =
      weilPairing W ℓ hℓ (pointHom W σ hW S) (pointHom W σ hW T)
        (pointHom_smul_eq_zero W σ hW ℓ hS) (pointHom_smul_eq_zero W σ hW ℓ hT) :=
```

Declarations: 52

---

## ModularCurves/LevelStructure/Basic.lean  (201 lines)

Level structures Γ(N), Γ₁(N), Γ₀(N) (KM Ch. 3), in Drinfeld form (definitions of record over arbitrary base) and naive form (`N` invertible), with the KM 1.4.4 / 3.7 equivalence theorems.

Context: `open AlgebraicGeometry CategoryTheory Limits`; local Over instances; `namespace ModularCurves`, `namespace EllipticCurve`, `variable {S : Scheme.{u}} (E : EllipticCurve S)`.

-- **Naive full level-`N` structure** (Loeffler Fact 3.8.1, for `N` invertible on `S`): a pair of points `P, Q ∈ E(S)`, killed by `N`, generating `E[N]` on every geometric fibre.
[DATA]
```lean
def IsNaiveFullLevel (N : ℕ) [NeZero N] (P Q : E.Section) : Prop :=
  ((N : ℤ) • P = 0 ∧ (N : ℤ) • Q = 0) ∧
    ∀ (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (.of k) ⟶ S),
      ∀ x : E.Point t, (N : ℤ) • x = 0 →
        x ∈ AddSubgroup.closure {Point.pull E t P, Point.pull E t Q}
```

-- **Naive Γ₁(N)-structure**: a point killed by `N`, of fibrewise exact order `N` (the right-hand side of KM 1.4.4, *with its standing hypothesis*).
[DATA]
```lean
def IsNaiveGammaOne (N : ℕ) [NeZero N] (P : E.Section) : Prop :=
  ((N : ℤ) • P = 0) ∧
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (.of k) ⟶ S),
    (N : ℤ) • Point.pull E t P = 0 ∧
    ∀ a : ℕ, 0 < a → a < N → (a : ℤ) • Point.pull E t P ≠ 0
```

-- **Drinfeld Γ₁(N)-structure** (KM 3.2): a point of exact order `N` in the sense of KM 1.4.1.
[DATA]
```lean
def IsGammaOne (N : ℕ) [NeZero N] (P : E.Section) : Prop :=
  P.HasExactOrder E N
```

-- The ideal sheaf of `E[N]` as a closed subscheme of `E`: the kernel ideal of the inclusion `E[N] ⟶ E` (mathlib `Scheme.Hom.ker`).
[DATA]
```lean
noncomputable def torsionIdeal (N : ℕ) : Scheme.IdealSheafData E.E :=
  (E.torsionι N).ker
```

-- **(T-B3a, pinning spec)** The closed subscheme cut out by `torsionIdeal N` is `E[N]` itself, compatibly with the inclusions.
[PROVED]
```lean
theorem torsionIdeal_subscheme (N : ℕ) :
    ∃ e : (E.torsionIdeal N).subscheme ≅ E.torsion N,
      e.hom ≫ E.torsionι N = (E.torsionIdeal N).subschemeι :=
```

-- **Drinfeld Γ(N)-structure** (KM 3.1): a pair `P, Q` of points killed by `N` such that the divisor `Σ_{(a,b) ∈ (ℤ/N)²} [aP + bQ]` equals `E[N]` as a closed subscheme.
[DATA]
```lean
def IsFullLevel (N : ℕ) [NeZero N] (P Q : E.Section) : Prop :=
  ((N : ℤ) • P = 0 ∧ (N : ℤ) • Q = 0) ∧
    (RelEffCartierDiv.sectionsDivisor E.π
        (fun i : Fin (N ^ 2) =>
          (((((i : ℕ) % N : ℕ) : ℤ) • P + ((((i : ℕ) / N : ℕ) : ℤ) • Q) :
            E.Point (𝟙 S))))).ideal =
      (E.torsionIdeal N)
```

-- **Register box `T-D8-bridge` (KM 3.7 / 1.4.4 for Γ(N))**: for `N` invertible and `P, Q` killed by `N`, the divisor `Σ_{(a,b)} [aP + bQ]` equals `E[N]` iff on every geometric point the pulled-back `P, Q` generate the `N`-torsion.
[SORRY]
```lean
theorem fullLevel_divisor_iff_naive_gen (N : ℕ) [NeZero N] (hN : NIsInvertible S N)
    (P Q : E.Section) (hP : (N : ℤ) • P = 0) (hQ : (N : ℤ) • Q = 0) :
    (RelEffCartierDiv.sectionsDivisor E.π
        (fun i : Fin (N ^ 2) =>
          (((((i : ℕ) % N : ℕ) : ℤ) • P + ((((i : ℕ) / N : ℕ) : ℤ) • Q) :
            E.Point (𝟙 S))))).ideal =
      (E.torsionIdeal N) ↔
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (.of k) ⟶ S),
        ∀ x : E.Point t, (N : ℤ) • x = 0 →
          x ∈ AddSubgroup.closure {Point.pull E t P, Point.pull E t Q} :=
```

-- **(T-D8 = KM 3.7 / KM 1.4.4 upgraded to Γ(N))** For `N` invertible on `S`, Drinfeld full-level structures and naive full-level structures coincide.
[PROVED]
```lean
theorem isFullLevel_iff_naive (N : ℕ) [NeZero N] (hN : NIsInvertible S N)
    (P Q : E.Section) :
    E.IsFullLevel N P Q ↔ E.IsNaiveFullLevel N P Q :=
```

-- **(T-D9 = KM 1.4.4 (1) ⇔ (3), restated)** For `N` invertible, Drinfeld Γ₁(N) equals naive Γ₁(N).
[PROVED]
```lean
theorem isGammaOne_iff_naive (N : ℕ) [NeZero N] (hN : NIsInvertible S N) (P : E.Section) :
    E.IsGammaOne N P ↔ E.IsNaiveGammaOne N P :=
```

-- **Γ₀(N)-structure** (KM 3.4): a relative effective Cartier divisor `G ⊆ E` of degree `N` which is a subgroup (KM 1.3.6) and is *cyclic* (KM 1.4.1), the generator condition stated in its geometric-fibre Drinfeld form.
[DATA] (Prop-valued structure)
```lean
structure IsGammaZero (N : ℕ) [NeZero N] (G : RelEffCartierDiv E.π) : Prop where
  isSubgroup : G.IsSubgroup E
  degree_eq : ∀ s : S, G.degree s = N
  /-- Geometric Drinfeld cyclicity: over every geometric point `t` there is a section
  `P₀` of the base-changed curve with `Σ_{a=1}^{N} [a·P₀] = G_t` as divisors. -/
  geometricallyCyclic :
    ∀ (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (.of k) ⟶ S),
      ∃ P₀ : (E.baseChange t).Section,
        (P₀.orderDivisor (E.baseChange t) N).ideal = (G.baseChange t).ideal
```

-- **(T-D10, literal fppf-local form — KM 1.4.1 / 3.7.1)** A rank-`N` subgroup divisor `G ⊆ E` is Γ₀(N)-cyclic in KM's definitional sense: *fppf-locally on `S` it admits a generating section of exact order `N`*.
[DATA]
```lean
def IsGammaZeroFppf (N : ℕ) [NeZero N] (G : RelEffCartierDiv E.π) : Prop :=
  G.IsSubgroup E ∧ (∀ s : S, G.degree s = N) ∧
    ∃ (T : Scheme.{u}) (h : T ⟶ S),
      Function.Surjective h.base ∧ Flat h ∧ LocallyOfFinitePresentation h ∧
      ∃ P₀ : (E.baseChange h).Section,
        haveI : NeZero N := ‹_›
        P₀.HasExactOrder (E.baseChange h) N ∧
        (P₀.orderDivisor (E.baseChange h) N).ideal = (G.baseChange h).ideal
```

-- **(T-D10 — KM 3.7.1)** The geometric-fibre Drinfeld cyclicity of record (`IsGammaZero`) agrees with KM's literal fppf-local cyclicity (`IsGammaZeroFppf`).
[SORRY]
```lean
theorem isGammaZero_iff_fppf (N : ℕ) [NeZero N] (G : RelEffCartierDiv E.π) :
    E.IsGammaZero N G ↔ E.IsGammaZeroFppf N G :=
```

Declarations: 12

---

## ModularCurves/LevelStructure/CartierDivisor.lean  (1940 lines)

Relative effective Cartier divisors and full sets of sections (KM Ch. 1): the working definition (closed subscheme finite locally free over the base), single-section divisors, the T-D22 local-principality theorem, the fully-proved T-D3 register boxes (`Σᵢ [Pᵢ]` finite locally free of rank `n`), base change and flat pullback of divisors, and the affine full-set-of-sections theory (norm and charpoly forms).

Context: `open AlgebraicGeometry CategoryTheory Limits`, `universe u`, `namespace ModularCurves`, `variable {C S : Scheme.{u}}`. Inside `namespace RelEffCartierDiv`: `variable {π : C ⟶ S}`. Section `FullSections`: `variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]`.

-- A relative effective Cartier divisor in `C/S`, in the working form for relative curves (KM 1.2.3): a closed subscheme of `C` (given by its ideal sheaf) which is finite, flat and of finite presentation (= finite locally free) over `S`.
[DATA] (structure)
```lean
structure RelEffCartierDiv (π : C ⟶ S) where
  /-- The ideal sheaf of the divisor. -/
  ideal : C.IdealSheafData
  finite : IsFinite (ideal.subschemeι ≫ π)
  flat : Flat (ideal.subschemeι ≫ π)
  lfp : LocallyOfFinitePresentation (ideal.subschemeι ≫ π)
```

-- The degree of a relative effective Cartier divisor at `s : S` — the rank of the finite locally free morphism `D ⟶ S` (KM 1.2; locally constant in `s`).
[DATA]
```lean
noncomputable def degree (D : RelEffCartierDiv π) (s : S) : ℕ :=
```

-- The base-change square of a section is cartesian: `T` is the fibre product of `C ×_S T ⟶ C` against the section `z`.
[PROVED]
```lean
theorem isPullback_sectionBaseChange {π : C ⟶ S} (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    {T : Scheme.{u}} (t : T ⟶ S) :
    IsPullback
      (Limits.pullback.lift (t ≫ z) (𝟙 T)
        (by rw [Category.assoc, hz, Category.comp_id, Category.id_comp]))
      t (Limits.pullback.fst π t) z :=
```

-- The kernel of a base-changed section is the scheme-theoretic preimage of the kernel of the section.
[PROVED]
```lean
theorem ker_sectionBaseChange {π : C ⟶ S} [IsSeparated π] (z : S ⟶ C)
    (hz : z ≫ π = 𝟙 S) {T : Scheme.{u}} (t : T ⟶ S) :
    (Limits.pullback.lift (t ≫ z) (𝟙 T)
        (by rw [Category.assoc, hz, Category.comp_id, Category.id_comp]) :
      T ⟶ Limits.pullback π t).ker =
      (Scheme.Hom.ker z).comap (Limits.pullback.fst π t) :=
```

-- **(T-D3, single-section case — KM 1.2.2)** The divisor `[P]` of a single section of a separated morphism: the closed subscheme cut out by the kernel ideal of the section.
[DATA]
```lean
noncomputable def sectionDivisor (π : C ⟶ S) [IsSeparated π] (z : S ⟶ C)
    (hz : z ≫ π = 𝟙 S) : RelEffCartierDiv π :=
```

-- **(T-D3, single-section degree)** The divisor of a single section has degree `1`.
[PROVED]
```lean
theorem sectionDivisor_degree (π : C ⟶ S) [IsSeparated π] (z : S ⟶ C)
    (hz : z ≫ π = 𝟙 S) (s : S) : (sectionDivisor π z hz).degree s = 1 :=
```

-- **(T-D22 = HB-REGIMM, KM 1.2.2 / GME §2.1.4)** The kernel ideal of a section of a smooth relative curve is, affine-locally on the total space, principal on a nonzerodivisor.
[PROVED]
```lean
theorem exists_affineOpen_ker_principal_nonZeroDivisor (π : C ⟶ S) [IsSeparated π]
    (hsm : SmoothOfRelativeDimension 1 π) (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (c : C) :
    ∃ V : C.affineOpens, c ∈ V.1 ∧ ∃ f : Γ(C, V.1),
      (Scheme.Hom.ker z).ideal V = Ideal.span {f} ∧
      f ∈ nonZeroDivisors Γ(C, V.1) :=
```

-- **Register box (T-D3/T-D1, finiteness; KM 1.2.2 + 1.2.3)**: over a separated smooth relative curve the product of the section ideals cuts out a subscheme finite over the base.
[PROVED]
```lean
theorem sectionsIdeal_isFinite (π : C ⟶ S) [IsSeparated π]
    (hsm : SmoothOfRelativeDimension 1 π) {n : ℕ}
    (P : Fin n → { z : S ⟶ C // z ≫ π = 𝟙 S }) :
    IsFinite ((∏ i, Scheme.Hom.ker (P i).1).subschemeι ≫ π) :=
```

-- **Register box (T-D3/T-D1, flatness; KM 1.2.2 + 1.2.3)** — see `sectionsIdeal_isFinite`.
[PROVED]
```lean
theorem sectionsIdeal_flat (π : C ⟶ S) [IsSeparated π]
    (hsm : SmoothOfRelativeDimension 1 π) {n : ℕ}
    (P : Fin n → { z : S ⟶ C // z ≫ π = 𝟙 S }) :
    Flat ((∏ i, Scheme.Hom.ker (P i).1).subschemeι ≫ π) :=
```

-- **Register box (T-D3/T-D1, finite presentation; KM 1.2.2 + 1.2.3)** — see `sectionsIdeal_isFinite`.
[PROVED]
```lean
theorem sectionsIdeal_lfp (π : C ⟶ S) [IsSeparated π]
    (hsm : SmoothOfRelativeDimension 1 π) {n : ℕ}
    (P : Fin n → { z : S ⟶ C // z ≫ π = 𝟙 S }) :
    LocallyOfFinitePresentation ((∏ i, Scheme.Hom.ker (P i).1).subschemeι ≫ π) :=
```

-- **Register box (T-D3, degree; KM 1.2.6)**: the divisor sum has rank `n`.
[PROVED]
```lean
theorem sectionsIdeal_finrank (π : C ⟶ S) [IsSeparated π]
    (hsm : SmoothOfRelativeDimension 1 π) {n : ℕ}
    (P : Fin n → { z : S ⟶ C // z ≫ π = 𝟙 S }) (s : S) :
    haveI := sectionsIdeal_isFinite π hsm P
    haveI := sectionsIdeal_flat π hsm P
    ((∏ i, Scheme.Hom.ker (P i).1).subschemeι ≫ π).finrank s = n :=
```

[DATA] (no docstring; the divisor `Σᵢ [Pᵢ]` attached to a family of sections, defined by cases on the KM 1.2.1 standing hypotheses)
```lean
open scoped Classical in
noncomputable def sectionsDivisor (π : C ⟶ S) {n : ℕ}
    (P : Fin n → { z : S ⟶ C // z ≫ π = 𝟙 S }) : RelEffCartierDiv π :=
```

-- **(T-D3a, specification of DS4a)** `Σᵢ [Pᵢ]` has degree `n`, under KM 1.2.1's standing hypotheses.
[PROVED]
```lean
theorem sectionsDivisor_degree (π : C ⟶ S) [IsSeparated π]
    (hsm : SmoothOfRelativeDimension 1 π) {n : ℕ}
    (P : Fin n → { z : S ⟶ C // z ≫ π = 𝟙 S }) (s : S) :
    (sectionsDivisor π P).degree s = n :=
```

-- Base change of a relative effective Cartier divisor along `t : T ⟶ S`: the ideal sheaf of the base-changed closed subscheme `D ×_S T ↪ C ×_S T` (kernel ideal of the pulled-back closed immersion), as a divisor in the base-changed curve. (Docstring sits on the private helper `baseChange_prop`; this is the public def.)
[DATA]
```lean
noncomputable def baseChange (D : RelEffCartierDiv π) {T : Scheme.{u}} (t : T ⟶ S) :
    RelEffCartierDiv (pullback.snd π t) where
```

-- The ideal sheaf of a base-changed divisor is the scheme-theoretic preimage of the original ideal along the first projection.
[PROVED]
```lean
theorem baseChange_ideal (D : RelEffCartierDiv π) {T : Scheme.{u}} (t : T ⟶ S) :
    (D.baseChange t).ideal = D.ideal.comap (Limits.pullback.fst π t) :=
```

-- Two relative effective Cartier divisors of `C/S` with the same ideal sheaf are equal.
[PROVED]
```lean
@[ext] theorem ext {D₁ D₂ : RelEffCartierDiv π} (h : D₁.ideal = D₂.ideal) : D₁ = D₂ :=
```

-- **Flat pullback of a relative effective Cartier divisor** (KM 1.1.4): the preimage `f⁻¹(D) = D ×_C C'` of `D` along an `S`-morphism `f : C' ⟶ C` which is finite, flat and of finite presentation.
[DATA]
```lean
noncomputable def flatPullback (D : RelEffCartierDiv π) {C' : Scheme.{u}} {π' : C' ⟶ S}
    (f : C' ⟶ C) (w : f ≫ π = π')
    [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] :
    RelEffCartierDiv π' where
```

-- The ideal sheaf of a flat pullback is the scheme-theoretic preimage of the original ideal (KM p. 6).
[PROVED]
```lean
theorem flatPullback_ideal (D : RelEffCartierDiv π) {C' : Scheme.{u}} {π' : C' ⟶ S}
    (f : C' ⟶ C) (w : f ≫ π = π')
    [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] :
    (D.flatPullback f w).ideal = D.ideal.comap f :=
```

-- Flat pullback along the identity is the identity.
[PROVED]
```lean
theorem flatPullback_id (D : RelEffCartierDiv π) :
    D.flatPullback (𝟙 C) (Category.id_comp π) = D :=
```

-- Flat pullbacks compose contravariantly.
[PROVED]
```lean
theorem flatPullback_flatPullback (D : RelEffCartierDiv π) {C' C'' : Scheme.{u}}
    {π' : C' ⟶ S} {π'' : C'' ⟶ S} (f : C' ⟶ C) (w : f ≫ π = π')
    (g : C'' ⟶ C') (w' : g ≫ π' = π'')
    [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]
    [IsFinite g] [Flat g] [LocallyOfFinitePresentation g] :
    (D.flatPullback f w).flatPullback g w' =
      D.flatPullback (g ≫ f) (by rw [Category.assoc, w, w']) :=
```

-- Iterated base change is base change along the composite, up to the canonical pullback isomorphism (ideal-sheaf form).
[PROVED]
```lean
theorem baseChange_baseChange_ideal (D : RelEffCartierDiv π) {T T' : Scheme.{u}}
    (t : T ⟶ S) (t' : T' ⟶ T) :
    ((D.baseChange t).baseChange t').ideal =
      (D.baseChange (t' ≫ t)).ideal.comap (pullbackLeftPullbackSndIso π t t').hom :=
```

-- The base change of a section `P : B →ₐ[R] R` to an `R`-algebra `A`, as a section `A ⊗[R] B →ₐ[A] A`.
[DATA]
```lean
noncomputable def AlgHom.sectionBaseChange (A : Type u) [CommRing A] [Algebra R A]
    (P : B →ₐ[R] R) : A ⊗[R] B →ₐ[A] A :=
```

-- **Full set of sections, affine case** (KM 1.8.2; universal-norm form of KM 1.9.1): sections `P₁, ⋯, Pₙ : B →ₐ[R] R` are a *full set of sections* of `Spec B / Spec R` if for every `R`-algebra `A` and every `f ∈ A ⊗_R B`: `Norm_{(A ⊗ B)/A}(f) = ∏ᵢ (Pᵢ)_A(f)`.
[DATA]
```lean
def IsFullSetOfSectionsAlg [Module.Free R B] [Module.Finite R B] {n : ℕ}
    (P : Fin n → (B →ₐ[R] R)) : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra R A],
    ∀ f : A ⊗[R] B,
      Algebra.norm A f = ∏ i, AlgHom.sectionBaseChange R B A (P i) f
```

-- In a reduced commutative ring, two elements are equal as soon as every ring homomorphism to a field identifies them.
[PROVED]
```lean
theorem eq_of_forall_field_hom_eq {A₀ : Type u} [CommRing A₀] [IsReduced A₀]
    {x y : A₀} (h : ∀ (K : Type u) [Field K] (χ : A₀ →+* K), χ x = χ y) : x = y :=
```

-- Sections base-change functorially: transporting `f` along `ψ : A →ₐ[R] A'` and evaluating the section agrees with evaluating over `A` and applying `ψ`.
[PROVED]
```lean
theorem sectionBaseChange_tensor_map {A A' : Type u} [CommRing A] [CommRing A']
    [Algebra R A] [Algebra R A'] (ψ : A →ₐ[R] A') (P : B →ₐ[R] R) (f : A ⊗[R] B) :
    AlgHom.sectionBaseChange R B A' P (Algebra.TensorProduct.map ψ (AlgHom.id R B) f) =
      ψ (AlgHom.sectionBaseChange R B A P f) :=
```

-- **(T-D2 = KM 1.9.2, verbatim source in hand with proof)** Over a *reduced* base, it suffices to check the norm equation after base change to every residue field.
[PROVED]
```lean
theorem isFullSetOfSectionsAlg_iff_fields [IsReduced R] [Module.Free R B]
    [Module.Finite R B] {n : ℕ} (P : Fin n → (B →ₐ[R] R)) :
    IsFullSetOfSectionsAlg R B P ↔
      ∀ (K : Type u) [Field K] [Algebra R K], ∀ f : TensorProduct R K B,
        Algebra.norm K f = ∏ i, AlgHom.sectionBaseChange R B K (P i) f :=
```

-- **Full set of sections, characteristic-polynomial form** (KM 1.8.2 form (1)): the characteristic polynomial of multiplication by `f` on the free `A`-module `A ⊗_R B` is `∏ᵢ (X − f(Pᵢ))`.
[DATA]
```lean
def IsFullSetOfSectionsCharpoly [Module.Free R B] [Module.Finite R B] {n : ℕ}
    (P : Fin n → (B →ₐ[R] R)) : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra R A],
    ∀ f : A ⊗[R] B,
      (Algebra.lmul A (A ⊗[R] B) f).charpoly =
        ∏ i, ((X : A[X]) - Polynomial.C (AlgHom.sectionBaseChange R B A (P i) f))
```

-- **KM 1.8.2**: the norm form and the characteristic-polynomial form of "full set of sections" agree.
[PROVED]
```lean
theorem isFullSetOfSectionsAlg_iff_charpoly [Module.Free R B] [Module.Finite R B]
    {n : ℕ} (P : Fin n → (B →ₐ[R] R)) :
    IsFullSetOfSectionsAlg R B P ↔ IsFullSetOfSectionsCharpoly R B P :=
```

Declarations: 28

---

## ModularCurves/LevelStructure/ExactOrder.lean  (250 lines)

Points of exact order N (Drinfeld / KM 1.4): `Section.orderDivisor` (the divisor `[P] + [2P] + ⋯ + [NP]`), `HasExactOrder` (the divisor is a subgroup), KM 1.4.2 (`N • P = 0`), and the KM 1.4.4 equivalences with the geometric-fibre and finite-étale characterisations (three register boxes sorried).

Context: `open AlgebraicGeometry CategoryTheory Limits`; local Over instances; `namespace ModularCurves`, `namespace EllipticCurve`, `variable {S : Scheme.{u}} (E : EllipticCurve S)`.

-- A section of `E/S`, i.e. a point `P ∈ E(S)`.
[DATA]
```lean
abbrev Section := E.Point (𝟙 S)
```

-- Pull a point back along `t : T ⟶ S` (restriction of a section to a `T`-point).
[DATA]
```lean
def Point.pull {T : Scheme.{u}} (t : T ⟶ S) (P : E.Section) : E.Point t :=
```

-- Pulling points back along `t : T ⟶ S` is compatible with integer scalars: both sides are `≫ [a]` by `point_smul_eq_comp_mulBy`.
[PROVED]
```lean
theorem Point.pull_zsmul {T : Scheme.{u}} (t : T ⟶ S) (a : ℤ) (P : E.Section) :
    Point.pull E t (a • P) = a • Point.pull E t P :=
```

-- Pulling points back along `t` is additive: `pull` is a group homomorphism.
[PROVED]
```lean
theorem Point.pull_add {T : Scheme.{u}} (t : T ⟶ S) (P Q : E.Section) :
    Point.pull E t (P + Q) = Point.pull E t P + Point.pull E t Q :=
```

-- Pulling back the zero point gives zero.
[PROVED]
```lean
theorem Point.pull_zero {T : Scheme.{u}} (t : T ⟶ S) :
    Point.pull E t (0 : E.Section) = 0 :=
```

-- **KM 1.3.6**: a relative effective Cartier divisor `D` in `E/S` *is a subgroup* if for every `T ⟶ S` the subset of `E(T)` consisting of points factoring through `D` is a subgroup of `E(T)`.
[DATA]
```lean
def _root_.ModularCurves.RelEffCartierDiv.IsSubgroup (D : RelEffCartierDiv E.π) : Prop :=
  ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ S),
    ∃ H : AddSubgroup (E.Point g),
      ∀ P : E.Point g, P ∈ H ↔ ∃ h : T ⟶ D.ideal.subscheme, h ≫ D.ideal.subschemeι = P.1
```

-- The divisor `[P] + [2P] + ⋯ + [NP]` of KM 1.4.1 (via DS4a).
[DATA]
```lean
noncomputable def Section.orderDivisor (P : E.Section) (N : ℕ) : RelEffCartierDiv E.π :=
  RelEffCartierDiv.sectionsDivisor E.π
    (fun a : Fin N => ((((a : ℕ) : ℤ) + 1) • P : E.Point (𝟙 S)))
```

-- **KM 1.4.1 — a point of exact order `N`** (Drinfeld): `P ∈ E(S)` has exact order `N` if the degree-`N` relative effective Cartier divisor `[P] + [2P] + ⋯ + [NP]` is a subgroup of `E/S`.
[DATA]
```lean
def Section.HasExactOrder (P : E.Section) (N : ℕ) [NeZero N] : Prop :=
  (P.orderDivisor E N).IsSubgroup E
```

-- **Register box `BB-DELIGNE` (KM 1.4.2, cite [Oort–Tate])**, in the project's subgroup-divisor encoding: a subgroup divisor of constant degree `N` is killed by `N`.
[SORRY]
```lean
theorem _root_.ModularCurves.RelEffCartierDiv.IsSubgroup.smul_eq_zero_of_factors
    {D : RelEffCartierDiv E.π} (hD : D.IsSubgroup E) {N : ℕ} [NeZero N]
    (hdeg : ∀ s : S, D.degree s = N) {T : Scheme.{u}} (g : T ⟶ S) (Q : E.Point g)
    (hQ : ∃ h : T ⟶ D.ideal.subscheme, h ≫ D.ideal.subschemeι = Q.1) :
    (N : ℤ) • Q = 0 :=
```

-- `IdealSheafData.ideal` as a monoid homomorphism (products of ideal sheaves are computed pointwise).
[DATA]
```lean
noncomputable def _root_.AlgebraicGeometry.Scheme.IdealSheafData.idealMonoidHom
    (X : Scheme.{u}) :
    X.IdealSheafData →* (∀ U : X.affineOpens, Ideal Γ(X, U.1)) where
```

-- **(T-D5 = KM 1.4.2)** Exact order `N` implies `N • P = 0`.
[PROVED]
```lean
theorem Section.HasExactOrder.smul_eq_zero {P : E.Section} {N : ℕ} [NeZero N]
    (h : P.HasExactOrder E N) : (N : ℤ) • P = 0 :=
```

-- **Register box `T-D6b` (KM 1.4.4, (2)⟹(3) at a geometric point)**: over an algebraically closed field the subgroup divisor of rank `N` is, for `N` invertible, finite étale, hence consists of `N` distinct points.
[SORRY]
```lean
theorem Section.HasExactOrder.pull_nsmul_ne_zero {P : E.Section} {N : ℕ} [NeZero N]
    (hN : NIsInvertible S N) (hkill : (N : ℤ) • P = 0) (h : P.HasExactOrder E N)
    (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (.of k) ⟶ S)
    {a : ℕ} (ha0 : 0 < a) (haN : a < N) :
    (a : ℤ) • Point.pull E t P ≠ 0 :=
```

-- **Register box `T-D6c` (KM 1.4.4, (3)⟹(1) via (4))**: if on every geometric point the multiples `aP`, `a = 1, …, N` are distinct, then the divisor `Σ [aP]` is finite étale over `S` and the subgroup property follows.
[SORRY]
```lean
theorem Section.hasExactOrder_of_geometric {P : E.Section} {N : ℕ} [NeZero N]
    (hN : NIsInvertible S N) (hkill : (N : ℤ) • P = 0)
    (h : ∀ (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (.of k) ⟶ S),
      ∀ a : ℕ, 0 < a → a < N → (a : ℤ) • Point.pull E t P ≠ 0) :
    P.HasExactOrder E N :=
```

-- **(T-D6 = KM 1.4.4, (1) ⇔ (3))** For a point `P` killed by `N` and `N` invertible on `S`: `P` has exact order `N` iff on every geometric point the induced point has exact order `N` in the usual sense.
[PROVED]
```lean
theorem Section.hasExactOrder_iff_geometric {P : E.Section} {N : ℕ} [NeZero N]
    (hN : NIsInvertible S N) (hkill : (N : ℤ) • P = 0) :
    P.HasExactOrder E N ↔
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (.of k) ⟶ S),
        (N : ℤ) • Point.pull E t P = 0 ∧
        ∀ a : ℕ, 0 < a → a < N → (a : ℤ) • Point.pull E t P ≠ 0 :=
```

-- **Register box `T-D7-bridge` (KM 1.4.4, (3)⟺(4))**: the divisor `Σ [aP]` is finite étale over `S` iff on every geometric point the multiples are distinct.
[SORRY]
```lean
theorem Section.orderDivisor_etale_iff_geometric {P : E.Section} {N : ℕ} [NeZero N]
    (hN : NIsInvertible S N) (hkill : (N : ℤ) • P = 0) :
    Etale ((P.orderDivisor E N).ideal.subschemeι ≫ E.π) ↔
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (.of k) ⟶ S),
        ∀ a : ℕ, 0 < a → a < N → (a : ℤ) • Point.pull E t P ≠ 0 :=
```

-- **(T-D7 = KM 1.4.4, (1) ⇔ (4))** For a point `P` killed by `N` and `N` invertible on `S`: `P` has exact order `N` iff the divisor `Σₐ [aP]` is finite étale over `S`.
[PROVED]
```lean
theorem Section.hasExactOrder_iff_etale {P : E.Section} {N : ℕ} [NeZero N]
    (hN : NIsInvertible S N) (hkill : (N : ℤ) • P = 0) :
    P.HasExactOrder E N ↔
      Etale ((P.orderDivisor E N).ideal.subschemeι ≫ E.π) :=
```

Declarations: 16

---

## ModularCurves/LevelStructure/Incidence.lean  (2599 lines)

The Cartier-incidence representability block (KM 1.3): vanishing ideals of sections/submodules of finite locally free modules, the `vanishingLocus` ideal sheaf with its universal property (KM 1.3.4 engine), the incidence loci for `D' ≤ D` and `D = D'`, the subgroup locus (KM 1.3.7), and the exact-order (T-D17) and full-level (T-D18) representability loci — all fully proved.

Context: `open AlgebraicGeometry CategoryTheory Limits`, `universe u`, `namespace ModularCurves`. Section `ZeroLocus`: `variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]`. Section `SubmoduleVanishing`: same but implicit (`{R} … {M} …`). Section `VanishingLocus`: `variable {W S : Scheme.{u}} (p : W ⟶ S) [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] (E : W.IdealSheafData)`. Section `Incidence`: `variable {C S : Scheme.{u}} {π : C ⟶ S}` (with `namespace RelEffCartierDiv` around the subdivisor material).

-- The vanishing ideal of an element `σ` of an `R`-module `M`: the ideal generated by the values of all linear functionals at `σ`.
[DATA]
```lean
def sectionVanishingIdeal (σ : M) : Ideal R :=
  Ideal.span (Set.range fun φ : Module.Dual R M => φ σ)
```

-- **(T-D13, basis form)** For a basis `b` of `M`, the vanishing ideal of `σ` is generated by the coordinates of `σ` alone.
[PROVED]
```lean
theorem sectionVanishingIdeal_eq_span_coord {ι : Type u} (b : Module.Basis ι R M) (σ : M) :
    sectionVanishingIdeal R M σ = Ideal.span (Set.range fun i => b.coord i σ) :=
```

-- **(T-D27, coordinate descent along a tower)** For `M` a `B`-module and `B` an `R`-algebra (compatibly), the `R`-vanishing ideal of `σ` is generated by the `R`-coordinates of the `B`-coordinates of `σ`.
[PROVED]
```lean
theorem sectionVanishingIdeal_eq_span_coord_coord {B : Type u} [CommRing B] [Algebra R B]
    [Module B M] [IsScalarTower R B M] {ι κ : Type u} (c : Module.Basis κ R B)
    (b : Module.Basis ι B M) (σ : M) : sectionVanishingIdeal R M σ =
      Ideal.span (Set.range fun p : κ × ι => c.coord p.1 (b.coord p.2 σ)) :=
```

-- **(T-D14c, base-change vanishing bridge)** Finitely many elements of a free `R`-algebra all die in the base change `A ⊗[R] B` iff the ideal of all their coordinates is killed by `R → A`.
[PROVED]
```lean
theorem forall_one_tmul_eq_zero_iff_span_coord_le_ker {A B : Type u} [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] {ι κ : Type u} (b : Module.Basis ι R B)
    (g : κ → B) :
    (∀ j, (1 : A) ⊗ₜ[R] g j = (0 : A ⊗[R] B)) ↔
      Ideal.span (Set.range fun p : κ × ι => b.coord p.2 (g p.1)) ≤
        RingHom.ker (algebraMap R A) :=
```

-- The vanishing ideal of a submodule: the ideal generated by all values of all linear functionals on all elements of the submodule.
[DATA]
```lean
def submoduleVanishingIdeal (J : Submodule R M) : Ideal R :=
  ⨆ g : J, sectionVanishingIdeal R M g
```

[PROVED]
```lean
theorem sectionVanishingIdeal_le_submoduleVanishingIdeal {J : Submodule R M} {g : M}
    (hg : g ∈ J) :
    sectionVanishingIdeal R M g ≤ submoduleVanishingIdeal R M J :=
```

[PROVED]
```lean
theorem apply_mem_submoduleVanishingIdeal {J : Submodule R M} {g : M} (hg : g ∈ J)
    (φ : Module.Dual R M) : φ g ∈ submoduleVanishingIdeal R M J :=
```

-- **(T-D14c-0, gluing keystone)** The vanishing ideal of a submodule commutes with localization when the ambient module is finitely presented.
[PROVED]
```lean
theorem submoduleVanishingIdeal_localized {Rₛ Nₛ : Type u} [CommRing Rₛ] [Algebra R Rₛ]
    [AddCommGroup Nₛ] [Module R Nₛ] [Module Rₛ Nₛ] [IsScalarTower R Rₛ Nₛ]
    (S : Submonoid R) [IsLocalization S Rₛ] (f : M →ₗ[R] Nₛ) [IsLocalizedModule S f]
    [Module.FinitePresentation R M] (J : Submodule R M) :
    (submoduleVanishingIdeal R M J).map (algebraMap R Rₛ) =
      submoduleVanishingIdeal Rₛ Nₛ (J.localized' Rₛ S f) :=
```

-- Localizing an ideal of an `R`-algebra `A` (viewed as an `R`-submodule) into the localization `Af` of `A` at the image monoid is the pushforward ideal, restricted.
[PROVED]
```lean
theorem localized'_restrictScalars_eq_restrictScalars_map
    {R Rf A Af : Type u} [CommRing R] [CommRing Rf] [CommRing A] [CommRing Af]
    [Algebra R Rf] [Algebra R A] [Algebra A Af] [Algebra R Af] [Algebra Rf Af]
    [IsScalarTower R A Af] [IsScalarTower R Rf Af]
    (S : Submonoid R) [IsLocalization S Rf]
    [IsLocalization (Algebra.algebraMapSubmonoid A S) Af]
    [IsLocalizedModule S (IsScalarTower.toAlgHom R A Af).toLinearMap]
    (J : Ideal A) :
    Submodule.localized' Rf S (IsScalarTower.toAlgHom R A Af).toLinearMap
        (J.restrictScalars R) =
      (J.map (algebraMap A Af)).restrictScalars Rf :=
```

-- The preimage of an affine open under a finite (hence affine) morphism, as an affine open.
[DATA]
```lean
def affinePreimage (U : S.affineOpens) : W.affineOpens :=
  ⟨p ⁻¹ᵁ U.1, U.2.preimage p⟩
```

-- **(T-D14c-1)** The vanishing locus on `S` of an ideal sheaf `E` on a scheme `W` finite locally free over `S`: over an affine `U ⊆ S` it is the vanishing ideal of the sections of `E` inside the finite locally free `Γ(S, U)`-module `Γ(W, p⁻¹U)`.
[DATA]
```lean
noncomputable def vanishingLocus : S.IdealSheafData where
```

-- **(T-D14c-i, free cover)** A finite flat finitely-presented morphism has free sections over an affine neighbourhood of every point of the base.
[PROVED]
```lean
theorem exists_affineOpen_mem_free (s : S) :
    ∃ U : S.affineOpens, s ∈ U.1 ∧
      (letI := ((p.app U.1).hom).toAlgebra
       Module.Free Γ(S, U.1) Γ(W, p ⁻¹ᵁ U.1)) :=
```

-- `≤ (ker f)` is a pointwise condition over all affine opens — no quasi-compactness needed.
[PROVED]
```lean
theorem le_ker_iff_forall {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) :
    I ≤ f.ker ↔ ∀ U : Y.affineOpens, I.ideal U ≤ RingHom.ker (f.app U.1).hom :=
```

-- **(T-D14c-2, universal property of the vanishing locus)** `T → S` kills the vanishing locus of `E` iff `E` pulls back to the zero ideal sheaf on the base change of `W`.
[PROVED]
```lean
theorem vanishingLocus_le_ker_iff {T : Scheme.{u}} (t : T ⟶ S) :
    vanishingLocus p E ≤ t.ker ↔ E.comap (pullback.snd t p) = ⊥ :=
```

-- `D' ≤ D` for effective divisors: the closed subscheme of `D'` factors through that of `D`.
[DATA]
```lean
def IsSubdivisor (D' D : RelEffCartierDiv π) : Prop :=
  ∃ j : D'.ideal.subscheme ⟶ D.ideal.subscheme,
    j ≫ D.ideal.subschemeι = D'.ideal.subschemeι
```

-- **(T-D14a)** The subscheme-factorization form of `D' ≤ D` is ideal-sheaf containment (KM 1.3.1's `I(D) ⊆ I(D')` dictionary).
[PROVED]
```lean
theorem isSubdivisor_iff_le (D' D : RelEffCartierDiv π) :
    IsSubdivisor D' D ↔ D.ideal ≤ D'.ideal :=
```

-- **(T-D14a′)** A morphism factors through the closed subscheme of an ideal sheaf iff the ideal is contained in its kernel.
[PROVED]
```lean
theorem _root_.ModularCurves.exists_factor_subschemeι_iff {T : Scheme.{u}}
    (Z : S.IdealSheafData) (t : T ⟶ S) :
    (∃ h : T ⟶ Z.subscheme, h ≫ Z.subschemeι = t) ↔ Z ≤ t.ker :=
```

-- **(T-D14 = KM 1.3.4, incidence `≤`)** For a smooth relative curve and effective divisors `D, D'` with `D'` proper (= finite) over `S`, there is a closed subscheme `Z ⊆ S` universal for `D' ≤ D`, cut out locally by `deg D'` equations, compatible with arbitrary base change.
[PROVED]
```lean
theorem exists_incidenceLocusLE [IsSeparated π] (hsm : SmoothOfRelativeDimension 1 π)
    (D D' : RelEffCartierDiv π) :
    ∃ Z : S.IdealSheafData, ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ S),
      (∃ h : T ⟶ Z.subscheme, h ≫ Z.subschemeι = t) ↔
        IsSubdivisor (D'.baseChange t) (D.baseChange t) :=
```

-- **(T-D15 = KM 1.3.5, incidence `=`, verbatim source in hand)** As above, universal for `D_T = D'_T`, cut out locally by `deg D` equations.
[PROVED]
```lean
theorem exists_incidenceLocusEQ [IsSeparated π] (hsm : SmoothOfRelativeDimension 1 π)
    (D D' : RelEffCartierDiv π) :
    ∃ Z : S.IdealSheafData, ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ S),
      (∃ h : T ⟶ Z.subscheme, h ≫ Z.subschemeι = t) ↔
        (IsSubdivisor (D'.baseChange t) (D.baseChange t) ∧
         IsSubdivisor (D.baseChange t) (D'.baseChange t)) :=
```

-- **(T-D16 = KM 1.3.7, the subgroup-divisor locus, verbatim source in hand with proof)** For an elliptic curve `E/S` and an effective divisor `D` in `E/S`, there is a closed subscheme `Z ⊆ S` universal for "`D` is a subgroup", cut out locally by `1 + deg D + (deg D)²` equations, compatible with arbitrary base change.
[PROVED]
```lean
theorem exists_subgroupLocus (E : EllipticCurve S) (D : RelEffCartierDiv E.π) :
    ∃ Z : S.IdealSheafData, ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ S),
      (∃ h : T ⟶ Z.subscheme, h ≫ Z.subschemeι = t) ↔
        (D.baseChange t).IsSubgroup (E.baseChange t) :=
```

-- **(T-D17 = KM 1.6 for `A = ℤ/N`; the exact-order locus)** There is a closed subscheme of `E[N]` universal for "the (torsion) point has exact order `N`".
[PROVED]
```lean
theorem exists_exactOrderLocus (E : EllipticCurve S) (N : ℕ) [NeZero N] :
    ∃ Z : (E.torsion N).IdealSheafData, ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ S)
      (P : E.Point t) (hP : P.1 ≫ E.mulByHom N = t ≫ E.zero),
      (∃ h : T ⟶ Z.subscheme, h ≫ Z.subschemeι = E.pointToTorsion P hP) ↔
        EllipticCurve.Section.HasExactOrder (E.baseChange t) (EllipticCurve.Point.asSection E t P) N :=
```

-- **(T-D18 = KM 1.5–1.6 for `A = (ℤ/N)²`; the full-level locus)** There is a closed subscheme of `E[N] ×_S E[N]` universal for "the pair is a Drinfeld full level-`N` structure".
[PROVED]
```lean
theorem exists_fullLevelLocus (E : EllipticCurve S) (N : ℕ) [NeZero N] :
    ∃ Z : (pullback (E.torsionπ N) (E.torsionπ N)).IdealSheafData,
      ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ S) (P Q : E.Point t)
        (hP : P.1 ≫ E.mulByHom N = t ≫ E.zero)
        (hQ : Q.1 ≫ E.mulByHom N = t ≫ E.zero),
      (∃ h : T ⟶ Z.subscheme,
          h ≫ Z.subschemeι = pullback.lift (E.pointToTorsion P hP)
            (E.pointToTorsion Q hQ) (by simp)) ↔
        (E.baseChange t).IsFullLevel N (EllipticCurve.Point.asSection E t P) (EllipticCurve.Point.asSection E t Q) :=
```

Declarations: 22

---

# Totals

| File | Lines | Public decls | SORRY/DATA-SORRY among them |
|---|---|---|---|
| ModularCurves.lean | 18 | 0 | 0 |
| Basic.lean | 33 | 0 | 0 |
| EllipticCurve/Basic.lean | 273 | 6 | 0 |
| EllipticCurve/GroupLaw.lean | 299 | 26 | 3 (`abelEnrichment_exists`, `abelEnrichment_unique`, `Point.asSection_zsmul`) |
| EllipticCurve/Torsion.lean | 254 | 23 | 4 (`mulByHom_locallyQuasiFinite`, `mulByHom_flat`, `mulByHom_finrank`, `mulByHom_formallyUnramified`) |
| EllipticCurve/TorsionFibre.lean | 400 | 10 | 0 |
| EllipticCurve/WeierstrassModel.lean | 2727 | 81 | 1 (`isWeierstrassModel_unique`) |
| GroupScheme/MuN.lean | 887 | 18 | 0 |
| WeilPairing/Basic.lean | 135 | 9 | 8 (all except `weilPairingEval`; incl. DATA-SORRY `weilPairing`) |
| WeilPairing/EtaleDescent.lean | 489 | 11 | 1 (`exists_weilPairingSpecField`) |
| WeilPairing/GaloisEquivariance.lean | 889 | 52 | 0 |
| LevelStructure/Basic.lean | 201 | 12 | 2 (`fullLevel_divisor_iff_naive_gen`, `isGammaZero_iff_fppf`) |
| LevelStructure/CartierDivisor.lean | 1940 | 28 | 0 |
| LevelStructure/ExactOrder.lean | 250 | 16 | 4 (`IsSubgroup.smul_eq_zero_of_factors`, `pull_nsmul_ne_zero`, `hasExactOrder_of_geometric`, `orderDivisor_etale_iff_geometric`) |
| LevelStructure/Incidence.lean | 2599 | 22 | 0 |
| **Total** | **11394** | **314** | **23** |
# ModularCurves signature inventory — batch B (`Moduli/` + `ModularCurve/`)

Extracted 2026-07-07 from `projects/ModularCurves/ModularCurves/{Moduli,ModularCurve}/`
(branch `dev/modular-curves`). Every public top-level `def`/`theorem`/`lemma`/`structure`/
`class`/`abbrev`/`instance` is listed. Conventions:

- Each declaration is verbatim from its keyword through `:=`/`where`; proof bodies/tactics
  are omitted. Short definitional **data** bodies (the mathematical content of `def`s) are
  kept; elided body parts are marked `-- … (omitted)`.
- `-- [context: …]` lines record enclosing namespace / in-scope section `variable`s that
  bind into the declaration (they are part of the signature but not textually adjacent).
- Status marks: `[PROVED]` no sorry in body; `[SORRY]` body is/contains sorry;
  `[DATA]` def whose body is real data; `[DATA-SORRY]` def whose body is/contains sorry.
- Structures are shown with all field names and types (field docstrings dropped).

---

## projects/ModularCurves/ModularCurves/Moduli/Coarse.lean  (124 lines)

Coarse moduli statements (the j-line, Y₀(N), and coarse Y_{P_H}; KM Ch. 8 ⧗): the scheme-level answer for the non-rigid levels — level 1, `N ≤ 2`, `Γ₀(N)` — where only a stack exists and the classical objects are *coarse* moduli schemes, stated via geometric points over algebraically closed fields.

```lean
-- [context: namespace ModularCurves.EllipticCurve; variable {S : Scheme.{u}}]
-- Transport of points along a pointed `S`-morphism of elliptic curves.
def HomOver.mapPoint {E E' : EllipticCurve S} (f : E.HomOver E') {T : Scheme.{u}}
    {g : T ⟶ S} (P : E.Point g) : E'.Point g :=
  ⟨P.1 ≫ f.hom, by rw [Category.assoc, f.over_w, P.2]⟩
```
[DATA]

```lean
-- [context: namespace ModularCurves, section Coarse]
-- Isomorphism classes of elliptic curves with an `H`-orbit of full level-`N`
-- structures, over a base — the point-set that a coarse `Y_{P_H}` must have at
-- algebraically closed points: the quotient by the join of the `H`-action and pointed
-- **isomorphism** (`(E, L) ∼ (E', L')` iff some pointed `S`-isomorphism carries `g • L`
-- to `L'` for some `g ∈ H`; `Quot` takes the generated equivalence).
open EllipticCurve in
def GammaHClasses (S : Scheme.{u}) (N : ℕ) [NeZero N]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N))) : Type (u + 1) :=
  Quot (fun (a b : Σ E : EllipticCurve S, E.FullLevelPt N) =>
    ∃ (f : a.1.HomOver b.1) (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)),
      IsIso f.hom ∧ g ∈ H ∧
      f.mapPoint (a.1.glSmul g a.2).1.1 = b.2.1.1 ∧
      f.mapPoint (a.1.glSmul g a.2).1.2 = b.2.1.2)
```
[DATA]

```lean
-- The class of a levelled curve in `GammaHClasses`.
def GammaHClasses.mk {S : Scheme.{u}} {N : ℕ} [NeZero N]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (E : EllipticCurve S) (L : E.FullLevelPt N) : GammaHClasses S N H :=
  Quot.mk _ ⟨E, L⟩
```
[DATA]

```lean
-- **(T-M1 = KM 8.2 ⧗ "The j-line as a coarse moduli scheme"; Silverman III.1.4(b))**
-- The j-line `Spec R[j]` is a coarse moduli scheme for elliptic curves (level 1): over
-- every algebraically closed field, isomorphism classes of elliptic curves biject with
-- points of the affine line, via the `j`-invariant of any Weierstrass model of the curve.
theorem jLine_coarse_points (k : Type u) [Field k] [IsAlgClosed k] :
    Nonempty (EllipticCurve.IsoClasses (Spec (.of k)) ≃ k) := by sorry
```
[SORRY]

```lean
-- **(T-M1a, j-compatibility of the bijection)** The bijection of
-- `jLine_coarse_points` can be chosen to send (the class of) an elliptic curve whose
-- fibre is the Weierstrass model of `W` to `W.j`.
theorem jLine_coarse_points_j (k : Type u) [Field k] [IsAlgClosed k] :
    ∃ β : EllipticCurve.IsoClasses (Spec (.of k)) ≃ k,
      ∀ (W : WeierstrassCurve k) (_ : W.IsElliptic) (E : EllipticCurve (Spec (.of k)))
        (e : E.E ≅ projModel W), e.hom ≫ projModelπ W = E.π →
        β ⟦E⟧ = W.j := by sorry
```
[SORRY]

```lean
-- [context: variable (R : CommRingCat.{u})]
-- **(T-M2 = Loeffler §3.6 / §3.8 Remark (1); KM Ch. 8 ⧗)** Coarse `Y_{P_H}` exists:
-- for every `H ≤ GL₂(ℤ/N)` (in particular the Borel — `Y₀(N)` — and `N ≤ 2` full level)
-- there is a scheme over `Spec R`, affine over the `j`-line, whose points over every
-- algebraically closed field biject with the classes `GammaHClasses` ("the maps
-- `P̃_H(S) → Y_{P_H}(S)` … are bijective if `S` is algebraically closed"),
-- **compatibly with `j`**.
theorem exists_coarse_gammaH (N : ℕ) [NeZero N]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (hinv : IsUnit (N : R)) :
    ∃ (Y : Scheme.{u}) (σ : Y ⟶ Spec R) (jY : Y ⟶ Spec (.of (Polynomial R))),
      jY ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial R))) = σ ∧
      IsAffineHom jY ∧
      ∀ (k : Type u) [Field k] [IsAlgClosed k] [Algebra R k],
        ∃ e : GammaHClasses (Spec (.of k)) N H ≃
            { h : Spec (.of k) ⟶ Y //
              h ≫ σ = Spec.map (CommRingCat.ofHom (algebraMap R k)) },
          ∀ (E : EllipticCurve (Spec (.of k))) (L : E.FullLevelPt N)
            (W : WeierstrassCurve k) (_ : W.IsElliptic)
            (i : E.E ≅ projModel W), i.hom ≫ projModelπ W = E.π →
            (e (GammaHClasses.mk H E L)).1 ≫ jY =
              Spec.map (CommRingCat.ofHom
                (Polynomial.eval₂RingHom (algebraMap R k) W.j)) := by sorry
```
[SORRY]

---

## projects/ModularCurves/ModularCurves/Moduli/EllCategory.lean  (182 lines)

The category `Ell/R` and moduli problems (KM Ch. 4; Loeffler §3.7): Katz–Mazur's stacks-without-saying-so formalism — objects `E → S`, morphisms are cartesian pointed squares, and moduli problems as contravariant functors, with representable / relatively representable / rigid.

```lean
-- [context: namespace ModularCurves]
-- An object of `Ell/R`: an `R`-scheme `S` together with an elliptic curve `E/S`.
structure EllObj (R : CommRingCat.{u}) where
  base : Scheme.{u}
  structMap : base ⟶ Spec R
  curve : EllipticCurve base
```
[DATA]

```lean
-- [context: variable {R : CommRingCat.{u}}]
-- A morphism of `Ell/R`: a cartesian square over a morphism of `R`-schemes,
-- compatible with the zero sections.
structure EllHom (X Y : EllObj R) where
  baseHom : X.base ⟶ Y.base
  base_w : baseHom ≫ Y.structMap = X.structMap
  top : X.curve.E ⟶ Y.curve.E
  isPullback : IsPullback top X.curve.π Y.curve.π baseHom
  zero_w : X.curve.zero ≫ top = baseHom ≫ Y.curve.zero
```
[DATA]  (also `attribute [ext] EllHom`)

```lean
instance : Category (EllObj R) where
  Hom := EllHom
  -- … (id, comp data and category laws omitted)
```
[DATA]

```lean
-- A **moduli problem** for elliptic curves over `R`: a contravariant functor
-- `Ell/R → Set`.
abbrev ModuliProblem (R : CommRingCat.{u}) := (EllObj R)ᵒᵖ ⥤ Type u
```
[DATA]

```lean
-- [context: namespace ModularCurves.ModuliProblem]
-- The base change of an `Ell/R` object along `g : T ⟶ S` (an `R`-scheme morphism over
-- the base of `X`).
noncomputable def _root_.ModularCurves.EllObj.pullbackAlong (X : EllObj R)
    {T : Scheme.{u}} (g : T ⟶ X.base) : EllObj R where
  base := T
  structMap := g ≫ X.structMap
  curve := X.curve.baseChange g
```
[DATA]

```lean
-- The canonical comparison morphism `X ×_S T' ⟶ X ×_S T` in `Ell/R` induced by
-- `k : T' ⟶ T` over `g : T ⟶ X.base` (base-change functoriality).
noncomputable def _root_.ModularCurves.EllObj.pullbackAlongMap (X : EllObj R)
    {T T' : Scheme.{u}} (g : T ⟶ X.base) (k : T' ⟶ T) :
    X.pullbackAlong (k ≫ g) ⟶ X.pullbackAlong g where
  baseHom := k
  base_w := by simp [EllObj.pullbackAlong]
  top := Limits.pullback.map _ _ _ _ (𝟙 _) k (𝟙 _) (by simp) (by simp)
  -- … (isPullback, zero_w proofs omitted)
```
[DATA]

```lean
-- `P` is **representable** if it is a representable presheaf on `Ell/R` — mathlib's
-- `Functor.IsRepresentable`, under the project's name (kept as an `abbrev` so the two
-- never diverge).
abbrev Representable (P : ModuliProblem R) : Prop :=
  P.IsRepresentable
```
[DATA]

```lean
-- `P` is **relatively representable**: for every `E/S` in `Ell/R`, the functor
-- `Sch/S → Set`, `T ↦ P(E ×_S T / T)` is representable — stated with its naturality
-- clause (the representing bijections commute with restriction along `T' ⟶ T`).
def RelativelyRepresentable (P : ModuliProblem R) : Prop :=
  ∀ X : EllObj R, ∃ (Z : Scheme.{u}) (f : Z ⟶ X.base),
    ∃ eqv : ∀ {T : Scheme.{u}} (g : T ⟶ X.base),
        { h : T ⟶ Z // h ≫ f = g } ≃ P.obj (Opposite.op (X.pullbackAlong g)),
      ∀ {T T' : Scheme.{u}} (g : T ⟶ X.base) (k : T' ⟶ T)
        (h : { h : T ⟶ Z // h ≫ f = g }),
        eqv (k ≫ g) ⟨k ≫ h.1, by rw [Category.assoc, h.2]⟩ =
          P.map (X.pullbackAlongMap g k).op (eqv g h)
```
[DATA]

```lean
-- `P` is **rigid**: for every `E/S`, `Aut(E/S)` (automorphisms over the identity of the
-- base) acts on `P(E/S)` without fixed points.
def Rigid (P : ModuliProblem R) : Prop :=
  ∀ (X : EllObj R) (e : X ≅ X), e.hom.baseHom = 𝟙 X.base → e ≠ Iso.refl X →
    ∀ a : P.obj (Opposite.op X), P.map e.hom.op a ≠ a
```
[DATA]

```lean
-- **(T-E5 = Loeffler Thm 3.7.4 = KM 4.7)** A moduli problem is representable iff it is
-- relatively representable and rigid.
theorem representable_iff (P : ModuliProblem R) :
    P.Representable ↔ P.RelativelyRepresentable ∧ P.Rigid := by sorry
```
[SORRY]

---

## projects/ModularCurves/ModularCurves/Moduli/Groupoid.lean  (92 lines)

Groupoid-valued moduli (expert-review addition Q7): the category of elliptic curves over a fixed base `S` with pointed `S`-morphisms (whose core is the groupoid of the moduli stack), iso-classes as its set-valued shadow, and the rigidification bridge for `N ≥ 3`.

```lean
-- [context: namespace ModularCurves.EllipticCurve; variable {S : Scheme.{u}}]
-- A morphism of elliptic curves over the *same* base: a morphism of total spaces
-- over `S` carrying zero to zero — a **pointed `S`-morphism**, NOT necessarily
-- invertible (`[2] : E ⟶ E` is one, of fibre degree 4, as is the zero morphism between
-- any two curves).
@[ext]
structure HomOver (E E' : EllipticCurve S) where
  hom : E.E ⟶ E'.E
  over_w : hom ≫ E'.π = E.π
  zero_w : E.zero ≫ hom = E'.zero
```
[DATA]

```lean
-- Elliptic curves over `S` with pointed `S`-morphisms form a category.
instance : Category (EllipticCurve S) where
  Hom := HomOver
  -- … (id, comp data and category laws omitted)
```
[DATA]

```lean
-- Isomorphism classes of elliptic curves over `S` — the set-valued shadow of the
-- groupoid.
def IsoClasses (S : Scheme.{u}) : Type (u + 1) :=
  Quotient (⟨fun E E' : EllipticCurve S => Nonempty (E ≅ E'),
    ⟨fun _ => ⟨Iso.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ => ⟨e ≪≫ e'⟩⟩⟩ :
      Setoid (EllipticCurve S))
```
[DATA]

```lean
-- **(T-G3 = rigidification bridge; GME 2.6.4 Aut-computation, p. 151)**
-- For `N ≥ 3` and `N` invertible, an **automorphism** of an elliptic curve over `S`
-- fixing a naive full level-`N` structure is the identity — the groupoid of `(E, P, Q)`
-- is equivalent to a set, and the set-valued problem `gammaFullNaiveProblem` is the
-- honest one.
theorem aut_trivial_of_fullLevel (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (hinv : NIsInvertible S N) (E : EllipticCurve S) (P Q : E.Section)
    (hPQ : E.IsNaiveFullLevel N P Q) (e : E ≅ E)
    (hP : P.1 ≫ e.hom.hom = P.1) (hQ : Q.1 ≫ e.hom.hom = Q.1) :
    e = Iso.refl E := by sorry
```
[SORRY]

---

## projects/ModularCurves/ModularCurves/Moduli/GammaH.lean  (910 lines)

General level structures `P_H` and full level `N` over an arbitrary base (Loeffler §3.8; KM Ch. 3–5, 7): the `GL₂(ℤ/N)`-action on full level structures, the moduli problems `P_H` with their relative-representability / rigidity / representability statements, the non-rigidity of full level `N ≤ 2` (the honest stack content), and the Drinfeld-form problems over ℤ.

```lean
-- [context: namespace ModularCurves.EllipticCurve; variable {S : Scheme.{u}}]
-- A (naive) full level-`N` point: a pair of sections forming a naive full level-`N`
-- structure.
def FullLevelPt (E : EllipticCurve S) (N : ℕ) [NeZero N] : Type u :=
  { PQ : E.Section × E.Section // E.IsNaiveFullLevel N PQ.1 PQ.2 }
```
[DATA]

```lean
-- On an element killed by `N`, an integer scalar depends only on its residue mod `N`:
-- if `a ≡ b (mod N)` in `ZMod N`, then `a • R = b • R`.
theorem zsmul_eq_of_intCast_eq {G : Type*} [AddCommGroup G] {N : ℕ} (R : G)
    (hR : (N : ℤ) • R = 0) {a b : ℤ} (h : (a : ZMod N) = (b : ZMod N)) :
    a • R = b • R := by
```
[PROVED]

```lean
-- [context: variable (E : EllipticCurve S)]
-- Reduction step for `GL₂`-recovery: a `ZMod N`-linear combination
-- `(a.val)•P' + (b.val)•Q'` of the transformed points `P' = m₀₀·pp + m₁₀·pq`,
-- `Q' = m₀₁·pp + m₁₁·pq` contracts, on `N`-torsion `pp, pq`, to the combination with
-- `ZMod N`-multiplied coefficients.
theorem recover_combo {N : ℕ} [NeZero N] {T : Scheme.{u}} (t : T ⟶ S)
    (pp pq P' Q' : E.Point t) (hpp : (N : ℤ) • pp = 0) (hpq : (N : ℤ) • pq = 0)
    (m00 m10 m01 m11 a b : ZMod N)
    (hP' : P' = (m00.val : ℤ) • pp + (m10.val : ℤ) • pq)
    (hQ' : Q' = (m01.val : ℤ) • pp + (m11.val : ℤ) • pq) :
    (a.val : ℤ) • P' + (b.val : ℤ) • Q'
      = ((a * m00 + b * m01).val : ℤ) • pp + ((a * m10 + b * m11).val : ℤ) • pq := by
```
[PROVED]

```lean
-- [context: variable (E : EllipticCurve S)]
-- The `GL₂(ℤ/N)`-action on full level structures, by precomposition of the
-- isomorphism `(ℤ/N)² ≅ E[N]`: in coordinates,
-- `g • (P, Q) = (g₁₁·P + g₂₁·Q, g₁₂·P + g₂₂·Q)` (entries lifted via `ZMod.val`;
-- well-defined because level points are killed by `N`).
noncomputable def glSmul {N : ℕ} [NeZero N]
    (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) (L : E.FullLevelPt N) :
    E.FullLevelPt N :=
  let m : Matrix (Fin 2) (Fin 2) (ZMod N) := g
  ⟨((((m 0 0).val : ℤ) • L.1.1 + ((m 1 0).val : ℤ) • L.1.2,
     ((m 0 1).val : ℤ) • L.1.1 + ((m 1 1).val : ℤ) • L.1.2)),
    by
      -- … (killing + generation membership proof omitted; no sorry)
```
[DATA]

```lean
-- If `N • P = 0` then `m • P = 0` whenever `N ∣ m` — so `m • P` depends only on
-- `m mod N`.
theorem smul_eq_zero_of_dvd {N : ℕ} (P : E.Section) (hP : (N : ℤ) • P = 0)
    {m : ℤ} (hm : (N : ℤ) ∣ m) : m • P = 0 := by
```
[PROVED]

```lean
-- `((x : ZMod N).val : ℤ) • P` is additive in `x` when `P` is killed by `N`.
theorem val_smul_add {N : ℕ} [NeZero N] (P : E.Section) (hP : (N : ℤ) • P = 0)
    (x y : ZMod N) :
    (((x + y).val : ℤ) • P) = ((x.val : ℤ) • P) + ((y.val : ℤ) • P) := by
```
[PROVED]

```lean
-- `((x*y : ZMod N).val : ℤ) • P = (x.val * y.val) • P` when `P` is killed by `N`.
theorem val_smul_mul {N : ℕ} [NeZero N] (P : E.Section) (hP : (N : ℤ) • P = 0)
    (x y : ZMod N) :
    (((x * y).val : ℤ) • P) = ((x.val : ℤ) * (y.val : ℤ)) • P := by
```
[PROVED]

```lean
-- The `GL₂`-action fixes level structures under the identity matrix (all `N`:
-- `ZMod.val_one` for `N ≥ 2`; for `N = 1`, level points are `0`).
theorem glSmul_one {N : ℕ} [NeZero N] (L : E.FullLevelPt N) :
    E.glSmul 1 L = L := by
```
[PROVED]

```lean
-- **(T-H2a)** The action law. `glSmul` is *precomposition* of the trivialisation
-- `(ℤ/N)² ≅ E[N]` with `g`, hence a **right** action: `(φ∘g)∘h = φ∘(g*h)` reads
-- `(g*h) • L = h • (g • L)`.
theorem glSmul_mul {N : ℕ} [NeZero N]
    (g h : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) (L : E.FullLevelPt N) :
    E.glSmul (g * h) L = E.glSmul h (E.glSmul g L) := by
```
[PROVED]

```lean
-- The `H`-orbit equivalence on full level structures, for `H ≤ GL₂(ℤ/N)`.
noncomputable def hOrbitSetoid {N : ℕ} [NeZero N]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N))) :
    Setoid (E.FullLevelPt N) :=
  ⟨fun L L' => ∃ g ∈ H, E.glSmul g L = L', by
    -- … (equivalence-relation proof omitted; no sorry)
```
[DATA]

```lean
-- Pull a full level point back along a base morphism `σ : T' ⟶ T`: the level of the
-- base-changed curve.
noncomputable def FullLevelPt.pullAlong {T T' : Scheme.{u}} {E : EllipticCurve T}
    {N : ℕ} [NeZero N] (σ : T' ⟶ T) (L : E.FullLevelPt N) :
    (E.baseChange σ).FullLevelPt N :=
  ⟨(EllipticCurve.Point.asSection E σ
      ⟨σ ≫ L.1.1.1, by rw [Category.assoc, L.1.1.2, Category.comp_id]⟩,
    EllipticCurve.Point.asSection E σ
      ⟨σ ≫ L.1.2.1, by rw [Category.assoc, L.1.2.2, Category.comp_id]⟩),
    by sorry⟩
```
[DATA-SORRY]

```lean
-- [context: namespace ModularCurves, section GammaH; variable (R : CommRingCat.{u})]
-- **The moduli problem `P_H`** for `H ≤ GL₂(ℤ/N)`: `E/S ↦ {H`-orbits of (naive) full
-- level-`N` structures on `E/S}`.
noncomputable def gammaHNaiveProblem (N : ℕ) [NeZero N]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N))) : ModuliProblem R where
  obj X := Quotient (X.unop.curve.hOrbitSetoid H)
  map f := ↾Quotient.map
    (fun L => ⟨⟨EllHom.pullSection R f.unop L.1.1, EllHom.pullSection R f.unop L.1.2⟩,
      by sorry⟩)
    (by sorry)
  -- … (map_id, map_comp proved)
```
[DATA-SORRY]

```lean
-- **(T-H1)** `P_⊥` is the naive full-level problem: the `H = ⊥` orbits are
-- singletons, recovering `gammaFullNaiveProblem`.
theorem gammaHNaive_bot (N : ℕ) [NeZero N] :
    Nonempty ((gammaHNaiveProblem R N ⊥) ≅ gammaFullNaiveProblem R N) :=
```
[PROVED]

```lean
-- **(T-H4 = Loeffler Prop 3.8.2, BOTH halves)** `P_H` is relatively representable
-- **and the representing objects are finite étale** over the base when `N` is invertible
-- (verbatim: "relatively representable and étale … finite étale") — the étale conjunct
-- was missing from the statement until 2026-07-06.
theorem gammaHNaive_relativelyRepresentable (N : ℕ) [NeZero N]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (hinv : IsUnit (N : R)) :
    (gammaHNaiveProblem R N H).RelativelyRepresentable ∧
      ∀ X : EllObj R, ∃ (Z : Scheme.{u}) (f : Z ⟶ X.base), IsFinite f ∧ Etale f ∧
        ∀ {T : Scheme.{u}} (g : T ⟶ X.base), Nonempty
          ({ h : T ⟶ Z // h ≫ f = g } ≃
            (gammaHNaiveProblem R N H).obj (Opposite.op (X.pullbackAlong g))) := by
  sorry
```
[SORRY]

```lean
-- **(T-H5 = Loeffler Prop 3.8.3, the rigidity criterion for arbitrary level)** Over
-- `R` with `6N` invertible: `P_H` is rigid iff the preimage of `H` in `SL₂(ℤ)` is
-- torsion-free ("contains no elements of finite order — i.e. has no elliptic points and
-- does not contain `−1`").
theorem gammaHNaive_rigid_iff (N : ℕ) [NeZero N] [Nontrivial R]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (hinv : IsUnit ((6 * N : ℕ) : R)) :
    (gammaHNaiveProblem R N H).Rigid ↔
      ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        (Matrix.SpecialLinearGroup.toGL
          (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ) ∈ H) →
        IsOfFinOrder γ → γ = 1 := by sorry
```
[SORRY]

```lean
-- **(T-H6, fine modular curves of arbitrary level)** For rigid `P_H` (and `N`
-- invertible), `P_H` is representable — "there is a scheme `Y = Y_{P_H}`, an elliptic
-- curve `ℰ/Y` and an `α ∈ P_H(ℰ/Y)` representing the functor" — and the base is smooth
-- and affine over `Spec R`.
theorem gammaHNaive_representable_of_rigid (N : ℕ) [NeZero N]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (hinv : IsUnit (N : R)) (hrig : (gammaHNaiveProblem R N H).Rigid) :
    (gammaHNaiveProblem R N H).Representable ∧
      ∀ X : EllObj R, Nonempty ((gammaHNaiveProblem R N H).RepresentableBy X) →
        (Smooth X.structMap ∧ IsAffineHom X.structMap) := by sorry
```
[SORRY]

```lean
-- [context: still section GammaH; variable {S : Scheme.{u}}]
-- **(T-H7a)** Multiplication morphisms compose multiplicatively:
-- `[m] ≫ [n] = [m·n]` (both are convolution powers of the identity).
theorem EllipticCurve.mulBy_comp_mulBy (E : EllipticCurve S) (m n : ℤ) :
    E.mulBy m ≫ E.mulBy n = E.mulBy (m * n) := by
```
[PROVED]

```lean
-- **(T-H7a)** `[1]` is the identity of `E.asOver`.
theorem EllipticCurve.mulBy_one (E : EllipticCurve S) : E.mulBy 1 = 𝟙 E.asOver := by
```
[PROVED]

```lean
-- **(T-H7a)** Scheme-level composition law for the multiplication morphisms.
theorem EllipticCurve.mulByHom_comp_mulByHom (E : EllipticCurve S) (m n : ℤ) :
    E.mulByHom m ≫ E.mulByHom n = E.mulByHom (m * n) := by
```
[PROVED]

```lean
-- **(T-H7a)** Scheme-level: `[1] = 𝟙`.
theorem EllipticCurve.mulByHom_one (E : EllipticCurve S) :
    E.mulByHom 1 = 𝟙 E.E := by
```
[PROVED]

```lean
-- **(T-H7a)** `[-1]` is a (self-inverse) involution.
theorem EllipticCurve.mulByHom_neg_one_involutive (E : EllipticCurve S) :
    E.mulByHom (-1) ≫ E.mulByHom (-1) = 𝟙 E.E := by
```
[PROVED]

```lean
-- **(T-H7a)** `[n]` is pointed: it carries the zero section to the zero section.
theorem EllipticCurve.zero_comp_mulByHom (E : EllipticCurve S) (n : ℤ) :
    E.zero ≫ E.mulByHom n = E.zero := by
```
[PROVED]

```lean
-- [context: variable (R : CommRingCat.{u})]
-- **(T-H7a)** Negation `[-1]` as an `Ell/R`-endomorphism over the identity of the
-- base: cartesian because `[-1]` is a self-inverse isomorphism.
noncomputable def EllObj.negHom (X : EllObj R) : X ⟶ X where
  baseHom := 𝟙 X.base
  base_w := Category.id_comp _
  top := X.curve.mulByHom (-1)
  -- … (isPullback, zero_w proofs omitted)
```
[DATA]

```lean
-- **(T-H7a)** `[-1]` is a self-inverse `Ell/R`-endomorphism.
theorem EllObj.negHom_comp_negHom (X : EllObj R) :
    EllObj.negHom R X ≫ EllObj.negHom R X = 𝟙 X := by
```
[PROVED]

```lean
-- **(T-H7a)** `[-1]` as an automorphism of `X` in `Ell/R` (self-inverse).
noncomputable def EllObj.negIso (X : EllObj R) : X ≅ X where
  hom := EllObj.negHom R X
  inv := EllObj.negHom R X
  hom_inv_id := EllObj.negHom_comp_negHom R X
  inv_hom_id := EllObj.negHom_comp_negHom R X
```
[DATA]

```lean
-- **(T-H7a, the fixity engine)** Pulling a section back along `[-1]` is negation.
theorem EllObj.pullSection_negHom (X : EllObj R) (P : X.curve.Section) :
    EllHom.pullSection R (EllObj.negHom R X) P = -P := by
```
[PROVED]

```lean
-- **(T-H7c)** Over a base with a geometric point, `[-1] ≠ 𝟙`: the geometric fibre
-- has a nonzero point of odd order `M ∈ {3,5}` (T-B6), while `[-1] = 𝟙` forces every
-- point to be `2`-torsion.
theorem EllipticCurve.mulByHom_neg_one_ne_id (E : EllipticCurve S) (k : Type u)
    [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S) :
    E.mulByHom (-1) ≠ 𝟙 E.E := by
```
[PROVED]

```lean
-- **(T-H7b-i)** Sections of an elliptic curve over `Spec k̄` are separated by their
-- value at the closed point (`AlgebraicGeometry.ext_of_apply_closedPoint_eq`: `E` is
-- locally of finite type over the algebraically closed base since it is proper).
theorem EllipticCurve.section_ext (k : Type u) [Field k] [IsAlgClosed k]
    (E : EllipticCurve (Spec (CommRingCat.of k))) {P Q : E.Section}
    (h : P.1 (IsLocalRing.closedPoint k) = Q.1 (IsLocalRing.closedPoint k)) : P = Q :=
```
[PROVED]

```lean
-- **(T-H7b-i)** Pulling sections back along any morphism of field-Specs is
-- injective: the base spaces are single points, so the closed-point values are
-- preserved, and `section_ext` separates.
theorem EllipticCurve.pull_injective (k k' : Type u) [Field k] [IsAlgClosed k]
    [Field k'] (E : EllipticCurve (Spec (CommRingCat.of k)))
    (t : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k)) :
    Function.Injective (EllipticCurve.Point.pull E t) := by
```
[PROVED]

```lean
-- **(T-H7b)** Naive full level-`N` structures exist over an algebraically closed
-- base when `N ≤ 2` and `N` is invertible: for `N = 1` the zero pair works (the killing
-- clause forces it); for `N = 2` a basis of `E[2]` from the geometric-fibre structure
-- (T-B6) does.
theorem EllipticCurve.exists_isNaiveFullLevel_of_le_two (k : Type u) [Field k]
    [IsAlgClosed k] (E : EllipticCurve (Spec (CommRingCat.of k))) (N : ℕ)
    [NeZero N] (hN : N ≤ 2) (hk : (N : k) ≠ 0) :
    ∃ P Q : E.Section, E.IsNaiveFullLevel N P Q := by
```
[PROVED]

```lean
-- **(T-H7d)** A nonempty `R`-scheme base has a geometric point in which every
-- `R`-invertible `N` stays invertible: take the algebraic closure of a residue field.
theorem EllObj.exists_geometricPoint (X : EllObj R) (hne : Nonempty X.base)
    (N : ℕ) (hinv : IsUnit ((N : ℕ) : R)) :
    ∃ (k : Type u) (_ : Field k) (_ : IsAlgClosed k)
      (t : Spec (CommRingCat.of k) ⟶ X.base), (N : k) ≠ 0 := by
```
[PROVED]

```lean
-- **(T-H7, the honest stack statement at small `N`)** For `N ≤ 2` the full-level
-- problem is NOT rigid — `[-1]` is a nontrivial automorphism acting trivially on all
-- level data (on `E[2]`, `−P = P`) — so no fine scheme exists and the object of record
-- is the levelled groupoid (design D6).
theorem gammaFullNaive_not_rigid_of_le_two (N : ℕ) [NeZero N] (hN : N ≤ 2)
    (hinv : IsUnit ((N : ℕ) : R)) (hR : ∃ X : EllObj R, Nonempty X.base) :
    ¬ (gammaFullNaiveProblem R N).Rigid := by
```
[PROVED]  (private helpers `neg_eq_self_of_zsmul_eq_zero_of_le_two`, `gammaFullNaiveProblem_map_negIso_of_le_two` omitted as private)

```lean
-- [context: namespace ModularCurves, section DrinfeldOverZ; variable (R : CommRingCat.{u})]
-- **Full level N over an arbitrary base — the Drinfeld form.** The moduli problem
-- `E/S ↦ {Drinfeld full level-N structures}` (KM 3.1: pairs with `Σ [aP+bQ] = E[N]` as
-- divisors), with NO invertibility hypothesis on `N`.
noncomputable def gammaFullDrinfeldProblem (N : ℕ) [NeZero N] : ModuliProblem R where
  obj X := { PQ : X.unop.curve.Section × X.unop.curve.Section //
    X.unop.curve.IsFullLevel N PQ.1 PQ.2 }
  map f := ↾fun PQ => ⟨⟨EllHom.pullSection R f.unop PQ.1.1,
    EllHom.pullSection R f.unop PQ.1.2⟩, by sorry⟩
  -- … (map_id, map_comp proved)
```
[DATA-SORRY]

```lean
-- The Drinfeld `Γ₁(N)` problem over an arbitrary base: points of exact order `N`
-- (KM 3.2 via KM 1.4.1 — fully sourced Ch. 1 machinery).
noncomputable def gammaOneDrinfeldProblem (N : ℕ) [NeZero N] : ModuliProblem R where
  obj X := { P : X.unop.curve.Section // X.unop.curve.IsGammaOne N P }
  map f := ↾fun P => ⟨EllHom.pullSection R f.unop P.1, by sorry⟩
  -- … (map_id, map_comp proved)
```
[DATA-SORRY]

```lean
-- **(T-H8 = GME Thm 2.6.8 scope; over-ℤ refinements = KM 4.7.2/5.1, ⧗KM)** For
-- `N ≥ 3` with `N` **invertible**, the Drinfeld full-level problem is rigid and
-- representable.
theorem gammaFullDrinfeld_representable (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (hinv : IsUnit (N : R)) :
    (gammaFullDrinfeldProblem R N).Rigid ∧
      (gammaFullDrinfeldProblem R N).Representable := by sorry
```
[SORRY]

```lean
-- **(T-H9, `Γ₁` analogue — over-ℤ refinement is KM 5.x, ⧗KM)** For `N ≥ 4` with `N`
-- **invertible**, the Drinfeld `Γ₁(N)` problem is rigid and representable.
theorem gammaOneDrinfeld_representable (N : ℕ) [NeZero N] (hN : 4 ≤ N)
    (hinv : IsUnit (N : R)) :
    (gammaOneDrinfeldProblem R N).Rigid ∧
      (gammaOneDrinfeldProblem R N).Representable := by sorry
```
[SORRY]

```lean
-- [context: namespace ModularCurves.EllipticCurve; variable {S : Scheme.{u}}]
-- The **levelled category**: elliptic curves over `S` with (naive) full level-`N`
-- structure; morphisms are pointed `S`-morphisms carrying one level structure to the
-- other.
@[ext]
structure LevelledHom {N : ℕ} [NeZero N]
    (X Y : Σ E : EllipticCurve S, E.FullLevelPt N) where
  hom : X.1 ⟶ Y.1
  level_w₁ : X.2.1.1.1 ≫ hom.hom = Y.2.1.1.1
  level_w₂ : X.2.1.2.1 ≫ hom.hom = Y.2.1.2.1
```
[DATA]

```lean
noncomputable instance levelledCategory (N : ℕ) [NeZero N] :
    Category (Σ E : EllipticCurve S, E.FullLevelPt N) where
  Hom := LevelledHom
  -- … (id, comp data and category laws omitted)
```
[DATA]

---

## projects/ModularCurves/ModularCurves/Moduli/QuotientProblem.lean  (779 lines)

The simultaneous moduli problem `(𝒫,δ)` and the Katz–Mazur 4.7 engine (T-Q6): every `Ell/R`-morphism is cartesian (comparison isos to the chosen pullback), KM 4.7 step (i) — representability of the simultaneous problem, the `Aut δ`-action through the second factor, freeness of the action from rigidity, and the axiomatized quotient engine `𝕸(𝒫,δ)/G`.

```lean
-- [context: namespace ModularCurves.EllObj; variable {R : CommRingCat.{u}}]
-- The tautological cartesian projection `X ×_{X.base} T ⟶ X` in `Ell/R`
-- lying over `g : T ⟶ X.base`.
noncomputable def pullbackAlongπ (X : EllObj R) {T : Scheme.{u}}
    (g : T ⟶ X.base) : X.pullbackAlong g ⟶ X where
  baseHom := g
  base_w := rfl
  top := pullback.fst X.curve.π g
  isPullback := IsPullback.of_hasPullback X.curve.π g
  zero_w := pullback.lift_fst _ _ _
```
[DATA]

```lean
@[simp]
theorem pullbackAlongπ_baseHom (X : EllObj R) {T : Scheme.{u}}
    (g : T ⟶ X.base) : (X.pullbackAlongπ g).baseHom = g := rfl
```
[PROVED]

```lean
-- The comparison morphism `Y ⟶ X.pullbackAlong u.baseHom` induced by an
-- `Ell/R`-morphism `u : Y ⟶ X` (the canonical map to the chosen pullback).
noncomputable def toPullbackAlong {Y X : EllObj R} (u : Y ⟶ X) :
    Y ⟶ X.pullbackAlong u.baseHom where
  baseHom := 𝟙 Y.base
  -- … (base_w, top := u.isPullback.isoPullback.hom, isPullback, zero_w omitted)
```
[DATA]

```lean
@[simp]
theorem toPullbackAlong_baseHom {Y X : EllObj R} (u : Y ⟶ X) :
    (toPullbackAlong u).baseHom = 𝟙 Y.base := rfl
```
[PROVED]

```lean
-- The comparison morphism composed with the tautological projection recovers the
-- original morphism: `toPullbackAlong u ≫ pullbackAlongπ = u`.
@[reassoc (attr := simp)]
theorem toPullbackAlong_pullbackAlongπ {Y X : EllObj R} (u : Y ⟶ X) :
    toPullbackAlong u ≫ X.pullbackAlongπ u.baseHom = u := by
```
[PROVED]

```lean
-- The morphism `Y ⟶ X.pullbackAlong g` assembled from `u : Y ⟶ X` and a base
-- factorization `h : Y.base ⟶ T` with `h ≫ g = u.baseHom` (the universal property
-- of the tautological cartesian square, map-in direction).
noncomputable def homToPullbackAlong {Y X : EllObj R} {T : Scheme.{u}}
    {g : T ⟶ X.base} (u : Y ⟶ X) (h : Y.base ⟶ T) (hh : h ≫ g = u.baseHom) :
    Y ⟶ X.pullbackAlong g where
  baseHom := h
  -- … (base_w, top := pullback.lift u.top (Y.curve.π ≫ h) _, isPullback, zero_w omitted)
```
[DATA]

```lean
@[simp]
theorem homToPullbackAlong_baseHom {Y X : EllObj R} {T : Scheme.{u}}
    {g : T ⟶ X.base} (u : Y ⟶ X) (h : Y.base ⟶ T) (hh : h ≫ g = u.baseHom) :
    (homToPullbackAlong u h hh).baseHom = h := rfl
```
[PROVED]

```lean
-- Projecting the assembled morphism back to `X` recovers `u`.
@[reassoc (attr := simp)]
theorem homToPullbackAlong_pullbackAlongπ {Y X : EllObj R} {T : Scheme.{u}}
    {g : T ⟶ X.base} (u : Y ⟶ X) (h : Y.base ⟶ T) (hh : h ≫ g = u.baseHom) :
    homToPullbackAlong u h hh ≫ X.pullbackAlongπ g = u := by
```
[PROVED]

```lean
-- **The universal property of the tautological cartesian square**: morphisms
-- `Y ⟶ X ×_{X.base} T` correspond to pairs `(u : Y ⟶ X, h : Y.base ⟶ T)` with
-- `h ≫ g = u.baseHom`.
noncomputable def homPullbackAlongEquiv (X : EllObj R) {T : Scheme.{u}}
    (g : T ⟶ X.base) (Y : EllObj R) :
    (Y ⟶ X.pullbackAlong g) ≃
      {p : (Y ⟶ X) × (Y.base ⟶ T) // p.2 ≫ g = p.1.baseHom} where
  toFun v := ⟨(v ≫ X.pullbackAlongπ g, v.baseHom), rfl⟩
  invFun p := homToPullbackAlong p.1.1 p.1.2 p.2
  -- … (left_inv, right_inv proofs omitted)
```
[DATA]

```lean
-- Decomposing a morphism into the tautological square over a composite base
-- map: `v : Y ⟶ X ×_{X.base} T` factors as the comparison of `v ≫ π` followed by
-- the base-change functoriality map.
theorem toPullbackAlong_pullbackAlongMap {Y X : EllObj R} {T : Scheme.{u}}
    {g : T ⟶ X.base} (v : Y ⟶ X.pullbackAlong g) :
    toPullbackAlong (v ≫ X.pullbackAlongπ g) ≫
      X.pullbackAlongMap g v.baseHom = v := by
```
[PROVED]

```lean
-- **Every `Ell/R`-morphism is cartesian**: the comparison isomorphism
-- `Y ≅ X.pullbackAlong u.baseHom` induced by `u : Y ⟶ X`.
noncomputable def isoPullbackAlong {Y X : EllObj R} (u : Y ⟶ X) :
    Y ≅ X.pullbackAlong u.baseHom where
  hom := toPullbackAlong u
  -- … (inv data, hom_inv_id, inv_hom_id omitted)
```
[DATA]

```lean
@[simp]
theorem isoPullbackAlong_hom {Y X : EllObj R} (u : Y ⟶ X) :
    (isoPullbackAlong u).hom = toPullbackAlong u := rfl
```
[PROVED]

```lean
-- **Two `Ell/R`-morphisms with equal base maps differ by an endomorphism over
-- the identity** (the connecting endomorphism; KM p. 113's `θ(g)`).
noncomputable def connectHom {V X : EllObj R} (v' v : V ⟶ X)
    (hb : v'.baseHom = v.baseHom) : V ⟶ V :=
  homToPullbackAlong v' (𝟙 V.base) (by rw [Category.id_comp, hb]) ≫
    (isoPullbackAlong v).inv
```
[DATA]

```lean
theorem connectHom_baseHom {V X : EllObj R} (v' v : V ⟶ X)
    (hb : v'.baseHom = v.baseHom) :
    (connectHom v' v hb).baseHom = 𝟙 V.base := by
```
[PROVED]

```lean
-- The defining property of the connecting endomorphism.
@[reassoc]
theorem connectHom_comp {V X : EllObj R} (v' v : V ⟶ X)
    (hb : v'.baseHom = v.baseHom) :
    connectHom v' v hb ≫ v = v' := by
```
[PROVED]

```lean
-- An endomorphism over the identity fixing one morphism is the identity
-- (cartesianness makes `v` "relatively mono" over its base map).
theorem eq_id_of_baseHom_of_comp {V X : EllObj R} (v : V ⟶ X) (ξ : V ⟶ V)
    (h1 : ξ.baseHom = 𝟙 V.base) (h2 : ξ ≫ v = v) : ξ = 𝟙 V := by
```
[PROVED]

```lean
-- [context: namespace ModularCurves.ModuliProblem]
-- **The simultaneous moduli problem** `(𝒫,δ)` (KM p. 112): the pointwise product
-- presheaf, whose value on `E/S` is `𝒫(E/S) × δ(E/S)`.
def simul (P Q : ModuliProblem R) : ModuliProblem R where
  obj X := P.obj X × Q.obj X
  map f := ↾fun a => (P.map f a.1, Q.map f a.2)
  -- … (map_id, map_comp proved)
```
[DATA]

```lean
@[simp]
theorem simul_obj (P Q : ModuliProblem R) (X : (EllObj R)ᵒᵖ) :
    (P.simul Q).obj X = (P.obj X × Q.obj X) := rfl
```
[PROVED]

```lean
@[simp]
theorem simul_map (P Q : ModuliProblem R) {X Y : (EllObj R)ᵒᵖ} (f : X ⟶ Y)
    (a : (P.simul Q).obj X) :
    (P.simul Q).map f a = (P.map f a.1, Q.map f a.2) := rfl
```
[PROVED]

```lean
-- [context: section SimulRepresentable;
--  variable (P : ModuliProblem R) {Xδ : EllObj R} {Z : Scheme.{u}} {f : Z ⟶ Xδ.base};
--  private theorem map_val_eq omitted as private]
-- **KM 4.7, step (i)** (KM p. 112: "Because `δ` is representable, and `𝒫` is
-- relatively representable, the simultaneous problem `(𝒫,δ)` is representable, by
-- `𝕸(𝒫,δ) = 𝒫_{E/𝕸(δ)}`"): the explicit `RepresentableBy` structure on the relative
-- representing object over the universal curve.
noncomputable def simulRepresentableBy (Q : ModuliProblem R)
    (rδ : Q.RepresentableBy Xδ)
    (eqv : ∀ {T : Scheme.{u}} (g : T ⟶ Xδ.base),
      { h : T ⟶ Z // h ≫ f = g } ≃ P.obj (Opposite.op (Xδ.pullbackAlong g)))
    (hnat : ∀ {T T' : Scheme.{u}} (g : T ⟶ Xδ.base) (k : T' ⟶ T)
      (h : { h : T ⟶ Z // h ≫ f = g }),
      eqv (k ≫ g) ⟨k ≫ h.1, by rw [Category.assoc, h.2]⟩ =
        P.map (Xδ.pullbackAlongMap g k).op (eqv g h)) :
    (P.simul Q).RepresentableBy (Xδ.pullbackAlong f) where
  -- … (homEquiv data and homEquiv_comp omitted)
```
[DATA]

```lean
-- **KM 4.7, step (i), existence form**: if `δ` is representable and `𝒫` is
-- relatively representable, the simultaneous problem `(𝒫,δ)` is representable.
theorem simul_representable (P Q : ModuliProblem R)
    (hQ : Q.Representable) (hP : P.RelativelyRepresentable) :
    (P.simul Q).Representable := by
```
[PROVED]

```lean
-- [context: section GroupAction; variable (P Q : ModuliProblem R)]
-- The natural transformation of simultaneous problems acting through the second
-- factor.
def simulMapSnd {Q Q' : ModuliProblem R} (η : Q ⟶ Q') :
    P.simul Q ⟶ P.simul Q' where
  app X := ↾fun a => (a.1, η.app X a.2)
  -- … (naturality proved)
```
[DATA]

```lean
@[simp]
theorem simulMapSnd_app {Q Q' : ModuliProblem R} (η : Q ⟶ Q')
    (X : (EllObj R)ᵒᵖ) (a : (P.simul Q).obj X) :
    (P.simulMapSnd η).app X a = (a.1, η.app X a.2) := rfl
```
[PROVED]

```lean
@[simp]
theorem simulMapSnd_id : P.simulMapSnd (𝟙 Q) = 𝟙 (P.simul Q) := by
```
[PROVED]

```lean
theorem simulMapSnd_comp {Q Q' Q'' : ModuliProblem R} (η : Q ⟶ Q')
    (θ : Q' ⟶ Q'') :
    P.simulMapSnd (η ≫ θ) = P.simulMapSnd η ≫ P.simulMapSnd θ := by
```
[PROVED]

```lean
-- **The action of `Aut δ` on the simultaneous problem `(𝒫,δ)` through the
-- second factor** (KM p. 112: `G` acts on `(𝒫,δ)` through its action on `δ`).
def simulAutSnd : Aut Q →* Aut (P.simul Q) where
  toFun e :=
    { hom := P.simulMapSnd e.hom
      inv := P.simulMapSnd e.inv
      -- … }
  -- … (map_one', map_mul' omitted)
```
[DATA]

```lean
@[simp]
theorem simulAutSnd_apply_hom (e : Aut Q) :
    ((P.simulAutSnd Q) e).hom = P.simulMapSnd e.hom := rfl
```
[PROVED]

```lean
-- [context: namespace ModularCurves.EllObj]
-- Base-scheme projection of `Ell/R`-automorphisms: an automorphism of an
-- `Ell/R`-object restricts to an automorphism of its base scheme.
def autBase (X : EllObj R) : Aut X →* Aut X.base where
  toFun e :=
    { hom := e.hom.baseHom
      inv := e.inv.baseHom
      -- … }
  map_one' := rfl
  map_mul' _ _ := rfl
```
[DATA]

```lean
@[simp]
theorem autBase_apply_hom (X : EllObj R) (e : Aut X) :
    (X.autBase e).hom = e.hom.baseHom := rfl
```
[PROVED]

```lean
-- [context: namespace ModularCurves.ModuliProblem]
-- **The KM 4.7 geometric action** (KM p. 112–113: "Let `G` operate upon
-- `𝕸(𝒫,δ)` through its action on `δ`", then "The action of `g ∈ G` on `𝕸(𝒫,δ)` is
-- defined as follows: the curve `E` with `(α_univ, g·β_univ)` is classified by a
-- unique morphism `g : 𝕸(𝒫,δ) → 𝕸(𝒫,δ)`"): the scheme action of `G` on the base of
-- any representing object of the simultaneous problem `(𝒫,δ)`, induced by an action
-- `φ : G →* Aut δ` on the auxiliary problem.
noncomputable def simulSchemeAction (P Q : ModuliProblem R) {G : Type*} [Group G]
    (φ : G →* Aut Q) {XM : EllObj R}
    (rM : (P.simul Q).RepresentableBy XM) :
    AlgebraicGeometry.SchemeAction G XM.base :=
  AlgebraicGeometry.SchemeAction.ofAut
    ((XM.autBase.comp rM.autMulHom).comp ((P.simulAutSnd Q).comp φ))
```
[DATA]

```lean
-- A **relative representation datum** for `Q` at `X : Ell/R` — the components
-- of one instance of `RelativelyRepresentable` (T-E3), bundled as data so the
-- KM 4.7 engine can consume them functionally.
structure RelRepData (Q : ModuliProblem R) (X : EllObj R) where
  Z : Scheme.{u}
  f : Z ⟶ X.base
  eqv : ∀ {T : Scheme.{u}} (g : T ⟶ X.base),
    { h : T ⟶ Z // h ≫ f = g } ≃ Q.obj (Opposite.op (X.pullbackAlong g))
  nat : ∀ {T T' : Scheme.{u}} (g : T ⟶ X.base) (k : T' ⟶ T)
    (h : { h : T ⟶ Z // h ≫ f = g }),
    eqv (k ≫ g) ⟨k ≫ h.1, by rw [Category.assoc, h.2]⟩ =
      Q.map (X.pullbackAlongMap g k).op (eqv g h)
```
[DATA]

```lean
-- The bundled and the `∃`-form of relative representability agree.
theorem relativelyRepresentable_iff_nonempty_relRepData (Q : ModuliProblem R) :
    Q.RelativelyRepresentable ↔ ∀ X : EllObj R, Nonempty (RelRepData Q X) := by
```
[PROVED]

```lean
-- **KM 4.7, axiom 2 vocabulary** (KM p. 112: "G operates upon δ, in such a way
-- that for every elliptic curve E/S […] the S-scheme `δ_{E/S}` is a finite etale
-- G-torsor"): a relative representation datum for the auxiliary problem carrying a
-- compatible `G`-action which makes it a finite étale `G`-torsor over the base.
structure TorsorData {Q : ModuliProblem R} {G : Type u} [Group G] [Finite G]
    (φ : G →* Aut Q) (X : EllObj R) extends RelRepData Q X where
  σZ : SchemeAction G Z
  over_base : ∀ γ : G, σZ.hom γ ≫ f = f
  equivariant : ∀ {T : Scheme.{u}} (g : T ⟶ X.base)
    (h : { h : T ⟶ Z // h ≫ f = g }) (γ : G),
    eqv g ⟨h.1 ≫ σZ.hom γ, by rw [Category.assoc, over_base, h.2]⟩ =
      (φ γ).hom.app (Opposite.op (X.pullbackAlong g)) (eqv g h)
  finite : IsFinite f
  etale : AlgebraicGeometry.Etale f
  surjective : Surjective f
  torsor : IsIso ((Limits.Sigma.desc fun γ : G =>
    Limits.pullback.lift (σZ.hom γ) (𝟙 Z)
      (by rw [Category.id_comp]; exact over_base γ)) :
    (∐ fun _ : G => Z) ⟶ Limits.pullback f f)
```
[DATA]

```lean
-- **Freeness of the KM action** (KM p. 113: "By axiom 2) and the rigidity of
-- `𝒫`, `G` operates freely on `𝕸(𝒫,δ)`"): if `𝒫` is rigid and the auxiliary
-- problem is a rigidifier, no `g ≠ 1` fixes a point of the representing object of
-- the simultaneous problem over a nonempty scheme.
theorem simulSchemeAction_free_of_rigid (P Q : ModuliProblem R)
    {G : Type u} [Group G] [Finite G] (φ : G →* Aut Q) {XM : EllObj R}
    (rM : (P.simul Q).RepresentableBy XM)
    (hrig : P.Rigid) (htors : ∀ X : EllObj R, Nonempty (TorsorData φ X))
    (γ : G) (hγ : γ ≠ 1) (T : Scheme.{u}) (t : T ⟶ XM.base)
    (hfix : t ≫ (P.simulSchemeAction Q φ rM).hom γ = t) :
    IsEmpty T := by
```
[PROVED]

```lean
-- **The Katz–Mazur 4.7 engine** (SCHOLIE 4.7.0, axiomatized claim, KM p. 112:
-- "We claim that over `ℤ[1/N]`, `𝒫` is represented by the affine `ℤ[1/N]`-scheme
-- `𝕸(𝒫,δ)/G`"): a rigid, relatively representable moduli problem that is affine
-- over `(Ell)` is representable, given an auxiliary problem `δ` that is
-- representable by an affine scheme and carries a `G`-action making its relative
-- representing schemes finite étale `G`-torsors.
theorem representable_of_rigid_of_torsor (P Q : ModuliProblem R)
    {G : Type u} [Group G] [Finite G] (φ : G →* Aut Q)
    (hQrep : Q.Representable)
    (hQaff : ∀ {XQ : EllObj R}, Q.RepresentableBy XQ → IsAffine XQ.base)
    (hPaff : ∀ X : EllObj R, ∃ d : RelRepData P X, IsAffineHom d.f)
    (htors : ∀ X : EllObj R, Nonempty (TorsorData φ X))
    (hrig : P.Rigid) :
    P.Representable := by
  sorry
```
[SORRY]

---

## projects/ModularCurves/ModularCurves/Moduli/QuotientStack.lean  (664 lines)

The quotient prestack `[X/G]` of a scheme by a finite group action (T-W3): the action groupoid `[X/G](S)`, the strict presheaf of groupoids `Schemeᵒᵖ ⥤ Cat`, the coarse comparison to the T-Q5 quotient, `G`-torsor pairs, and the trivialization functor with its faithfulness.

File-wide context: `namespace ModularCurves; variable {G : Type u} [Group G] {X : Scheme.{u}} (σ : SchemeAction G X)`.

```lean
-- The value of the quotient prestack `[X/G]` on `S`: the action groupoid of
-- `G` on the `S`-points of `X`.
def ActionGroupoid (_σ : SchemeAction G X) (S : Scheme.{u}) : Type u := S ⟶ X
```
[DATA]

```lean
-- [context: namespace ActionGroupoid; variable {σ} {S : Scheme.{u}}]
-- Interpret an `S`-point of `X` as an object of the action groupoid.
def mk (t : S ⟶ X) : ActionGroupoid σ S := t
```
[DATA]

```lean
-- The underlying `S`-point of an object of the action groupoid.
def pt (t : ActionGroupoid σ S) : S ⟶ X := t
```
[DATA]

```lean
@[simp] theorem pt_mk (t : S ⟶ X) : (mk (σ := σ) t).pt = t := rfl
```
[PROVED]

```lean
instance : Groupoid (ActionGroupoid σ S) where
  Hom t t' := { g : G // t.pt ≫ σ.hom g = t'.pt }
  -- … (id, comp, inv data and groupoid laws omitted)
```
[DATA]

```lean
@[simp]
theorem comp_val {a b c : ActionGroupoid σ S} (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g).1 = f.1 * g.1 := rfl
```
[PROVED]

```lean
@[simp]
theorem id_val (a : ActionGroupoid σ S) : (𝟙 a : a ⟶ a).1 = 1 := rfl
```
[PROVED]

```lean
theorem eqToHom_val {a b : ActionGroupoid σ S} (h : a = b) :
    (eqToHom h).1 = 1 := by
```
[PROVED]

```lean
-- Restriction of the action groupoid along `u : S' ⟶ S` (precomposition).
def restrict (σ : SchemeAction G X) {S S' : Scheme.{u}} (u : S' ⟶ S) :
    ActionGroupoid σ S ⥤ ActionGroupoid σ S' where
  obj t := mk (u ≫ t.pt)
  -- … (map data, map_id, map_comp omitted)
```
[DATA]

```lean
@[simp]
theorem restrict_obj_pt {S S' : Scheme.{u}} (u : S' ⟶ S)
    (t : ActionGroupoid σ S) : ((restrict σ u).obj t).pt = u ≫ t.pt := rfl
```
[PROVED]

```lean
@[simp]
theorem restrict_map_val {S S' : Scheme.{u}} (u : S' ⟶ S)
    {t t' : ActionGroupoid σ S} (f : t ⟶ t') :
    ((restrict σ u).map f).1 = f.1 := rfl
```
[PROVED]  (private theorem `functor_ext` omitted as private)

```lean
-- **The quotient prestack `[X/G]`** (T-W3): the strict presheaf of groupoids
-- sending `S` to the action groupoid of `G` on `X(S)`, with restriction by
-- precomposition.
open ActionGroupoid in
def QuotientStack (σ : SchemeAction G X) : Schemeᵒᵖ ⥤ Cat.{u, u} where
  obj S := Cat.of (ActionGroupoid σ S.unop)
  map u := (restrict σ u.unop).toCatHom
  -- … (map_id, map_comp proved)
```
[DATA]

```lean
@[simp]
theorem quotientStack_obj (σ : SchemeAction G X) (S : Schemeᵒᵖ) :
    (QuotientStack σ).obj S = Cat.of (ActionGroupoid σ S.unop) := rfl
```
[PROVED]

```lean
-- [context: section Coarse; variable [Finite G]
--  [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
--  (V : ↥X → X.Opens) (hVs : ∀ x : ↥X, σ.IsStableOpen (V x))
--  (hVa : ∀ x : ↥X, IsAffineOpen (V x)) (hVmem : ∀ x : ↥X, x ∈ V x)]
-- **The coarse comparison** `[X/G](S) ⟶ (X/G)(S)`: composing an `S`-point with
-- the T-Q5 quotient projection collapses the groupoid (every morphism goes to an
-- identity, by the invariance `hom_quotientπ`).
noncomputable def ActionGroupoid.toQuotient (S : Scheme.{u}) :
    ActionGroupoid σ S ⥤ Discrete (S ⟶ σ.quotient V hVs hVa) where
  obj t := ⟨t.pt ≫ σ.quotientπ V hVs hVa hVmem⟩
  -- … (map data, map_id, map_comp omitted)
```
[DATA]

```lean
-- [context: section TorsorPair; variable [Finite G]]
-- **A `G`-torsor pair over `S`** (T-W3b vocabulary): a finite étale `G`-torsor
-- `p : P ⟶ S` (in the `∐`-comparison sense of record — `TorsorData`/Stack.lean
-- shape) together with a `G`-equivariant map to `X`.
structure TorsorPair (σ : SchemeAction G X) (S : Scheme.{u}) where
  P : Scheme.{u}
  p : P ⟶ S
  τ : SchemeAction G P
  over_base : ∀ g : G, τ.hom g ≫ p = p
  finite : IsFinite p
  etale : AlgebraicGeometry.Etale p
  surjective : Surjective p
  torsor : IsIso ((Limits.Sigma.desc fun g : G =>
    Limits.pullback.lift (τ.hom g) (𝟙 P)
      (by rw [Category.id_comp]; exact over_base g)) :
    (∐ fun _ : G => P) ⟶ Limits.pullback p p)
  u : P ⟶ X
  equivariant : ∀ g : G, τ.hom g ≫ u = u ≫ σ.hom g
```
[DATA]

```lean
-- [context: namespace TorsorPair; variable {σ} {S : Scheme.{u}}]
-- Morphisms of `G`-torsor pairs: equivariant maps over `S` compatible with the
-- maps to `X`.
@[ext]
structure Hom (A B : TorsorPair σ S) where
  hom : A.P ⟶ B.P
  over : hom ≫ B.p = A.p
  equiv : ∀ g : G, A.τ.hom g ≫ hom = hom ≫ B.τ.hom g
  compat : hom ≫ B.u = A.u
```
[DATA]

```lean
instance : Category (TorsorPair σ S) where
  Hom A B := Hom A B
  -- … (id, comp data and category laws omitted)
```
[DATA]

```lean
omit [Finite G] in
@[simp]
theorem comp_hom {A B C : TorsorPair σ S} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl
```
[PROVED]

```lean
omit [Finite G] in
@[simp]
theorem id_hom (A : TorsorPair σ S) : (𝟙 A : A ⟶ A).hom = 𝟙 A.P := rfl
```
[PROVED]

The following declarations (through `trivialize_faithful`) live in `namespace ModularCurves` inside `section TorsorPair` (after `end TorsorPair` closes the inner namespace).

```lean
-- The translation action of `G` on `∐_G S`: `g` maps the `h`-summand
-- identically onto the `h * g`-summand.
variable (G) in
noncomputable def trivialTorsorAction (S : Scheme.{u}) :
    SchemeAction G (∐ fun _ : G => S) where
  hom g := Limits.Sigma.desc fun h => Limits.Sigma.ι (fun _ : G => S) (h * g)
  -- … (hom_one, hom_mul proved)
```
[DATA]

```lean
omit [Finite G] in
@[reassoc (attr := simp)]
theorem ι_trivialTorsorAction_hom (S : Scheme.{u}) (g h : G) :
    Limits.Sigma.ι (fun _ : G => S) h ≫ (trivialTorsorAction G S).hom g =
      Limits.Sigma.ι (fun _ : G => S) (h * g) :=
```
[PROVED]

```lean
-- The projection of the trivial torsor.
noncomputable def trivialTorsorπ (S : Scheme.{u}) :
    (∐ fun _ : G => S) ⟶ S :=
  Limits.Sigma.desc fun _ => 𝟙 S
```
[DATA]

```lean
omit [Group G] [Finite G] in
@[reassoc (attr := simp)]
theorem ι_trivialTorsorπ (S : Scheme.{u}) (h : G) :
    Limits.Sigma.ι (fun _ : G => S) h ≫ trivialTorsorπ S = 𝟙 S :=
```
[PROVED]

```lean
omit [Finite G] in
theorem trivialTorsorAction_over_base (S : Scheme.{u}) (g : G) :
    (trivialTorsorAction G S).hom g ≫ trivialTorsorπ S = trivialTorsorπ S := by
```
[PROVED]

```lean
-- The equivariant map of the trivial torsor pair attached to an `S`-point
-- `t : S ⟶ X`: on the `g`-summand it is `t` translated by `g`.
noncomputable def trivialTorsorMap (S : Scheme.{u}) (t : S ⟶ X) :
    (∐ fun _ : G => S) ⟶ X :=
  Limits.Sigma.desc fun g => t ≫ σ.hom g
```
[DATA]

```lean
omit [Finite G] in
@[reassoc (attr := simp)]
theorem ι_trivialTorsorMap (S : Scheme.{u}) (t : S ⟶ X) (h : G) :
    Limits.Sigma.ι (fun _ : G => S) h ≫ trivialTorsorMap σ S t =
      t ≫ σ.hom h :=
```
[PROVED]

```lean
omit [Finite G] in
theorem trivialTorsorMap_equivariant (S : Scheme.{u}) (t : S ⟶ X) (g : G) :
    (trivialTorsorAction G S).hom g ≫ trivialTorsorMap σ S t =
      trivialTorsorMap σ S t ≫ σ.hom g := by
```
[PROVED]

```lean
-- Left translation on the trivial torsor: the `h`-summand maps identically to
-- the `g * h`-summand.
variable (G) in
noncomputable def trivialTorsorLeft (S : Scheme.{u}) (g : G) :
    (∐ fun _ : G => S) ⟶ (∐ fun _ : G => S) :=
  Limits.Sigma.desc fun h => Limits.Sigma.ι (fun _ : G => S) (g * h)
```
[DATA]

```lean
omit [Finite G] in
@[reassoc (attr := simp)]
theorem ι_trivialTorsorLeft (S : Scheme.{u}) (g h : G) :
    Limits.Sigma.ι (fun _ : G => S) h ≫ trivialTorsorLeft G S g =
      Limits.Sigma.ι (fun _ : G => S) (g * h) :=
```
[PROVED]

```lean
-- Left translations commute with the (right-translation) torsor action.
omit [Finite G] in
theorem trivialTorsorLeft_equivariant (S : Scheme.{u}) (g γ : G) :
    (trivialTorsorAction G S).hom γ ≫ trivialTorsorLeft G S g =
      trivialTorsorLeft G S g ≫ (trivialTorsorAction G S).hom γ := by
```
[PROVED]

```lean
-- Left translations lie over the base.
omit [Finite G] in
theorem trivialTorsorLeft_over_base (S : Scheme.{u}) (g : G) :
    trivialTorsorLeft G S g ≫ trivialTorsorπ S = trivialTorsorπ S := by
```
[PROVED]

```lean
-- The compatibility of left translation with the equivariant maps: if
-- `t ≫ σ.hom g = t'`, left translation by `g⁻¹` carries the trivial pair of `t'`
-- to that of `t`.
omit [Finite G] in
theorem trivialTorsorLeft_map (S : Scheme.{u}) {t t' : S ⟶ X} {g : G}
    (hg : t ≫ σ.hom g = t') :
    trivialTorsorLeft G S g⁻¹ ≫ trivialTorsorMap σ S t' =
      trivialTorsorMap σ S t := by
```
[PROVED]

```lean
omit [Finite G] in
@[simp]
theorem trivialTorsorLeft_one (S : Scheme.{u}) :
    trivialTorsorLeft G S (1 : G) = 𝟙 _ := by
```
[PROVED]

```lean
-- The trivial-torsor projection is étale (a coproduct of identities;
-- `Etale` is Zariski-local at the source).
omit [Group G] [Finite G] in
theorem trivialTorsorπ_etale (S : Scheme.{u}) :
    AlgebraicGeometry.Etale (trivialTorsorπ (G := G) S) :=
```
[PROVED]

```lean
-- The trivial-torsor projection is surjective (any single summand already
-- covers).
omit [Finite G] in
theorem trivialTorsorπ_surjective (S : Scheme.{u}) :
    Surjective (trivialTorsorπ (G := G) S) := by
```
[PROVED]

```lean
-- **The fold of a finite coproduct of copies of an affine scheme is finite**
-- (T-W3b-i, model case): conjugating by `sigmaSpec`, the fold is `Spec` of the
-- diagonal `R →+* Π_ι R`, which is module-finite for finite `ι`.
theorem isFinite_sigmaDesc_id_spec {ι : Type u} [Finite ι]
    (R : CommRingCat.{u}) :
    AlgebraicGeometry.IsFinite
      (Limits.Sigma.desc fun _ : ι => 𝟙 (Spec R)) := by
```
[PROVED]

```lean
-- **The fold of a finite coproduct of copies of any scheme is a finite
-- morphism** (T-W3b-i): it is the base change of the affine model
-- (`isFinite_sigmaDesc_id_spec` over `Spec ℤ`) along `S ⟶ Spec ℤ`, via the
-- extensivity of `Scheme` (pullbacks distribute over finite coproducts).
theorem isFinite_sigmaDesc_id {ι : Type u} [Finite ι] (S : Scheme.{u}) :
    AlgebraicGeometry.IsFinite (Limits.Sigma.desc fun _ : ι => 𝟙 S) := by
```
[PROVED]

```lean
-- The trivial-torsor projection is a finite morphism.
omit [Group G] [Finite G] in
theorem trivialTorsorπ_finite [Finite G] (S : Scheme.{u}) :
    AlgebraicGeometry.IsFinite (trivialTorsorπ (G := G) S) :=
```
[PROVED]

```lean
-- [context: section TorsorComparison; variable (S : Scheme.{u});
--  private decls trivialTorsor_distrib / trivialTorsorReindex / trivialTorsorReindexInv /
--  trivialTorsor_comparison_eq and a private IsIso instance omitted as private]
-- **The trivial torsor satisfies the torsor condition** (the last property
-- field of the trivial `TorsorPair`): `(γ, x) ↦ (γ·x, x)` identifies
-- `∐_G (∐_G S)` with `(∐_G S) ×_S (∐_G S)`.
theorem trivialTorsor_torsor :
    IsIso ((Limits.Sigma.desc fun γ : G =>
      Limits.pullback.lift ((trivialTorsorAction G S).hom γ)
        (𝟙 (∐ fun _ : G => S))
        (by rw [Category.id_comp]; exact trivialTorsorAction_over_base S γ)) :
      (∐ fun _ : G => (∐ fun _ : G => S)) ⟶
        Limits.pullback (trivialTorsorπ S) (trivialTorsorπ S)) := by
```
[PROVED]

```lean
omit [Finite G] in
theorem trivialTorsorLeft_mul (S : Scheme.{u}) (g g' : G) :
    trivialTorsorLeft G S (g * g') =
      trivialTorsorLeft G S g' ≫ trivialTorsorLeft G S g := by
```
[PROVED]

```lean
-- [context: section Trivialize]
-- **The trivial torsor pair** attached to an `S`-point `t : S ⟶ X`: the
-- split torsor `∐_G S → S` with the translation action and the equivariant map
-- `(g, s) ↦ σ(g)(t(s))`.
noncomputable def trivialTorsorPair (S : Scheme.{u}) (t : S ⟶ X) :
    TorsorPair σ S where
  P := ∐ fun _ : G => S
  p := trivialTorsorπ S
  τ := trivialTorsorAction G S
  over_base := trivialTorsorAction_over_base S
  finite := trivialTorsorπ_finite S
  etale := trivialTorsorπ_etale S
  surjective := trivialTorsorπ_surjective S
  torsor := trivialTorsor_torsor S
  u := trivialTorsorMap σ S t
  equivariant := trivialTorsorMap_equivariant σ S t
```
[DATA]

```lean
-- **The trivialization functor** (T-W3b): the prestack `[X/G](S)` maps to the
-- groupoid of `G`-torsor pairs by sending an `S`-point to its trivial torsor pair
-- and a group element `f : t ⟶ t'` to left translation by `f⁻¹`.
noncomputable def trivialize (S : Scheme.{u}) :
    ActionGroupoid σ S ⥤ TorsorPair σ S where
  obj t := trivialTorsorPair σ S t.pt
  map {t t'} f :=
    { hom := trivialTorsorLeft G S f.1⁻¹
      over := trivialTorsorLeft_over_base S f.1⁻¹
      equiv := fun g => trivialTorsorLeft_equivariant S f.1⁻¹ g
      compat := trivialTorsorLeft_map σ S f.2 }
  -- … (map_id, map_comp proved)
```
[DATA]

```lean
-- The range of a coproduct component is clopen: open as an open immersion,
-- closed because the complement is the (open) union of the other components.
theorem isClopen_range_sigmaι {σ' : Type u} (g : σ' → Scheme.{u}) (i : σ') :
    IsClopen (Set.range (Limits.Sigma.ι g i).base) := by
```
[PROVED]

```lean
-- **The trivialization functor is faithful over a nonempty base** (the
-- `S = ∅` counterexample in the attack log is the only obstruction; fullness
-- additionally needs `S` connected).
theorem trivialize_faithful (S : Scheme.{u}) [Nonempty S] :
    (trivialize σ S).Faithful where
```
[PROVED]

---

## projects/ModularCurves/ModularCurves/Moduli/Representability.lean  (273 lines)

Representability: Tate normal form, Y₁(N), Y(N) (Loeffler §§3.3–3.4, 3.8; KM Ch. 3–5) — the elementary ring-level spine (Tate normal form and the universal Tate curve) plus section pullback in `Ell/R` and the naive Γ₁(N) / Γ(N) moduli problems with their representability statements.

```lean
-- [context: namespace ModularCurves, section TateNormalForm;
--  variable {R : Type u} [CommRing R]]
-- Tate normal form: `Y² + αXY + βY = X³ + βX²`, i.e. `a₂ = a₃ ( = β)`, `a₄ = a₆ = 0`.
def _root_.WeierstrassCurve.IsTateNormal (W : WeierstrassCurve R) : Prop :=
  W.a₂ = W.a₃ ∧ W.a₄ = 0 ∧ W.a₆ = 0
```
[DATA]

```lean
-- The point `(x, y)` on `W` is *nowhere of order 1, 2 or 3*: the product
-- `ψ₂(x,y) · ψ₃(x,y)` of division-polynomial values is a unit of `R` (equivalently: in no
-- residue field does `P` become `0`, 2-torsion, or 3-torsion; the affine point is nowhere
-- `0` automatically).
def NowhereOrderLEThree (W : WeierstrassCurve R) (x y : R) : Prop :=
  IsUnit ((W.Ψ 2).evalEval x y * (W.Ψ 3).evalEval x y)
```
[DATA]

```lean
-- **(T-E1 = Loeffler Prop 3.3.4, ring level — PROVABLE-NOW target)** If `W/R` is
-- elliptic and `(x, y)` is a rational point nowhere of order `≤ 3`, there exist unique
-- `(α, β)` and a unique change of variables `vc` with `vc • W` in Tate normal form and
-- `(x, y) ↦ (0, 0)` (i.e. `vc.r = x`, `vc.t = y`).
open WeierstrassCurve.Affine in
theorem exists_unique_variableChange_isTateNormal (W : WeierstrassCurve R) [W.IsElliptic]
    (x y : R) (h : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y) :
    ∃! vc : WeierstrassCurve.VariableChange R,
      (vc • W).IsTateNormal ∧ vc.r = x ∧ vc.t = y := by
```
[PROVED]

```lean
-- The universal Tate-normal Weierstrass curve `E(A, B) : Y² + AXY + BY = X³ + BX²` over
-- `ℤ[A, B]`.
noncomputable def tateCurve : WeierstrassCurve (MvPolynomial (Fin 2) ℤ) :=
  { a₁ := MvPolynomial.X 0
    a₂ := MvPolynomial.X 1
    a₃ := MvPolynomial.X 1
    a₄ := 0
    a₆ := 0 }
```
[DATA]

```lean
-- The universal Tate curve is in Tate normal form (sanity pin).
theorem tateCurve_isTateNormal : tateCurve.IsTateNormal := ⟨rfl, rfl, rfl⟩
```
[PROVED]

```lean
-- The coordinate ring `ℤ[A, B][Δ(A,B)⁻¹]` of the universal Tate curve — the affine ring
-- of (the coarse ring-level avatar of) the universal elliptic curve with a point of nowhere
-- order ≤ 3.
noncomputable abbrev tateRing : Type :=
  Localization.Away tateCurve.Δ
```
[DATA]  (private lemma `tateRing_eval₂Hom_comp` omitted as private)

```lean
-- **(T-E2 = Loeffler Cor 3.3.5, ring level — PROVABLE-NOW target)** For every ring `A`,
-- ring homomorphisms `tateRing →+* A` correspond exactly to pairs `(α, β) ∈ A²` with
-- `Δ(α, β)` a unit — i.e. to Tate-normal elliptic curves over `A` marked at `(0, 0)`.
theorem tateRing_homEquiv (A : Type u) [CommRing A] :
    ∃ e : (tateRing →+* A) ≃
        { c : A × A //
          IsUnit ((tateCurve.map (MvPolynomial.eval₂Hom (Int.castRingHom A)
            (fun i => if i = 0 then c.1 else c.2))).Δ) },
      ∀ φ : tateRing →+* A,
        ((e φ).1 : A × A) =
          (φ (algebraMap (MvPolynomial (Fin 2) ℤ) tateRing (MvPolynomial.X 0)),
           φ (algebraMap (MvPolynomial (Fin 2) ℤ) tateRing (MvPolynomial.X 1))) := by
```
[PROVED]

```lean
-- [context: section LevelModuli; variable (R : CommRingCat.{u})]
-- Sections pull back along `Ell/R` morphisms (contravariantly): given
-- `f : X ⟶ Y` in `Ell/R` and a section of `Y.curve`, the cartesian square produces a
-- section of `X.curve`.
noncomputable def EllHom.pullSection {X Y : EllObj R} (f : X ⟶ Y)
    (P : Y.curve.Section) : X.curve.Section :=
  ⟨f.isPullback.lift (f.baseHom ≫ P.1) (𝟙 X.base)
      (by rw [Category.assoc, P.2, Category.comp_id, Category.id_comp]),
    f.isPullback.lift_snd _ _ _⟩
```
[DATA]

```lean
-- Pulling a section back along the identity gives the section back.
theorem EllHom.pullSection_id {X : EllObj R} (P : X.curve.Section) :
    EllHom.pullSection R (𝟙 X) P = P := by
```
[PROVED]

```lean
-- Pulling sections back is compatible with composition.
theorem EllHom.pullSection_comp {X Y Z : EllObj R} (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : Z.curve.Section) :
    EllHom.pullSection R (f ≫ g) P =
      EllHom.pullSection R f (EllHom.pullSection R g P) := by
```
[PROVED]

```lean
-- **(T-E4a, additivity of section-pullback — surfaced by the adversarial pass
-- 2026-07-06)** `pullSection` is a group homomorphism.
theorem EllHom.pullSection_add {X Y : EllObj R} (f : X ⟶ Y)
    (P Q : Y.curve.Section) :
    EllHom.pullSection R f (P + Q) =
      EllHom.pullSection R f P + EllHom.pullSection R f Q := by sorry
```
[SORRY]

```lean
-- The naive `Γ₁(N)` moduli problem over `R`: `E/S ↦ {P ∈ E(S) : P` has naive exact
-- order `N}` (fibrewise; the right notion for `N` invertible, KM 1.4.4).
noncomputable def gammaOneNaiveProblem (N : ℕ) [NeZero N] : ModuliProblem R where
  obj X := { P : X.unop.curve.Section // X.unop.curve.IsNaiveGammaOne N P }
  map f := ↾fun P => ⟨EllHom.pullSection R f.unop P.1, by sorry⟩
  -- … (map_id, map_comp proved)
```
[DATA-SORRY]

```lean
-- The naive full-level-`N` (`Γ(N)`) moduli problem over `R`:
-- `E/S ↦ {(P, Q) generating E[N] in every fibre}`.
noncomputable def gammaFullNaiveProblem (N : ℕ) [NeZero N] : ModuliProblem R where
  obj X := { PQ : X.unop.curve.Section × X.unop.curve.Section //
    X.unop.curve.IsNaiveFullLevel N PQ.1 PQ.2 }
  map f := ↾fun PQ => ⟨⟨EllHom.pullSection R f.unop PQ.1.1,
    EllHom.pullSection R f.unop PQ.1.2⟩, by sorry⟩
  -- … (map_id, map_comp proved)
```
[DATA-SORRY]

```lean
-- **(T-E7 = Loeffler Thm 3.4.4 + Def 3.3.6; KM 5.x for the Drinfeld upgrade)** For
-- `N ≥ 4` and `N` invertible in `R`, the naive `Γ₁(N)` problem is representable, and the
-- representing base scheme is smooth and affine over `Spec R`.
theorem gammaOneNaive_representable (N : ℕ) [NeZero N] (hN : 4 ≤ N)
    (hinv : IsUnit (N : R)) :
    (gammaOneNaiveProblem R N).Representable ∧
      ∀ X : EllObj R, Nonempty ((gammaOneNaiveProblem R N).RepresentableBy X) →
        (Smooth X.structMap ∧ IsAffineHom X.structMap) := by sorry
```
[SORRY]

```lean
-- **(T-E9 = Loeffler Prop 3.8.2–3.8.3; KM 3.1/4.7/5.1)** For `N ≥ 3` and `N` invertible
-- in `R`, the naive full-level problem `[Γ(N)]` is rigid and representable; the representing
-- scheme `Y(N)` is smooth and affine over `Spec R`.
theorem gammaFullNaive_representable (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (hinv : IsUnit (N : R)) :
    ((gammaFullNaiveProblem R N).Rigid ∧ (gammaFullNaiveProblem R N).Representable) ∧
      ∀ X : EllObj R, Nonempty ((gammaFullNaiveProblem R N).RepresentableBy X) →
        (Smooth X.structMap ∧ IsAffineHom X.structMap) := by
  sorry
```
[SORRY]

---

## projects/ModularCurves/ModularCurves/Moduli/Stack.lean  (128 lines)

The stack of elliptic curves: descent statements (the "stack bridge") — torsor descent for rigidified (levelled) curves in the form GME Lemma 2.6.7 uses, and the fppf-separatedness half of "the moduli problems are fppf sheaves"; the pseudofunctor packaging (`T-E8`) is deferred.

```lean
-- [context: namespace ModularCurves]
-- **(T-E10 v2, descent of rigidified curves along a finite-group torsor — the form
-- GME Lemma 2.6.7 actually uses; ADVERSARIAL FIX 2026-07-05, DEF-2)**
-- Let `f : T' ⟶ T`, let `G` be a finite group acting on `T'` over `T` (via `σ`), with
-- the torsor condition …; if for every `g ∈ G` the `g`-twist of `(E', L')` is isomorphic
-- to `(E', L')` in the levelled groupoid, then `(E', L')` descends.
theorem levelledCurve_descent_of_torsor {T T' : Scheme.{u}} (f : T' ⟶ T)
    [Flat f] [LocallyOfFinitePresentation f] [Surjective f]
    (G : Type u) [Group G] [Finite G] (σ : G →* Aut (Over.mk f))
    (htorsor : IsIso ((Limits.Sigma.desc (fun g : G =>
      Limits.pullback.lift (f := f) (g := f) ((σ g).hom.left) (𝟙 T')
        (by rw [Category.id_comp]; exact Over.w (σ g).hom))) :
      (∐ fun _ : G => T') ⟶ Limits.pullback f f))
    (N : ℕ) [NeZero N] (hN : 3 ≤ N) (hinv : IsUnit (N : Γ(T', ⊤)))
    (E' : EllipticCurve T') (L' : E'.FullLevelPt N)
    (hdesc : ∀ g : G, Nonempty
      ((⟨E'.baseChange ((σ g).hom.left), EllipticCurve.FullLevelPt.pullAlong
          ((σ g).hom.left) L'⟩ : Σ E : EllipticCurve T', E.FullLevelPt N) ≅
        ⟨E', L'⟩)) :
    ∃ (E : EllipticCurve T) (L : E.FullLevelPt N), Nonempty
      ((⟨E.baseChange f, EllipticCurve.FullLevelPt.pullAlong f L⟩ :
          Σ E₀ : EllipticCurve T', E₀.FullLevelPt N) ≅ ⟨E', L'⟩) := by sorry
```
[SORRY]

```lean
-- **(T-E11, separatedness half of "the moduli problems are fppf sheaves")** For a
-- relatively representable moduli problem `P`, sections of `P` are determined fppf-locally:
-- restriction along an fppf cover `f : T' ⟶ T` is injective on `P`-values.
theorem moduliProblem_fppf_separated (R : CommRingCat.{u}) (P : ModuliProblem R)
    (hP : P.RelativelyRepresentable) :
    ∀ {T T' : Scheme.{u}} (f : T' ⟶ T), Flat f → LocallyOfFinitePresentation f →
      Surjective f → ∀ (X : EllObj R) (g : T ⟶ X.base)
      (a b : P.obj (Opposite.op (X.pullbackAlong g))),
      P.map (X.pullbackAlongMap g f).op a = P.map (X.pullbackAlongMap g f).op b →
      a = b := by
```
[PROVED]

---

## projects/ModularCurves/ModularCurves/Moduli/WeierstrassAtlas.lean  (130 lines)

The universal Weierstrass atlas `U := Spec ℤ[a₁,a₂,a₃,a₄,a₆][Δ⁻¹]` and the universal Weierstrass curve `E_U := projModel W_univ` over it (T-W5) — the atlas of the quotient-stack presentation `M_ell^W = [U/G]`.

```lean
-- [context: namespace ModularCurves]
-- The **universal Weierstrass curve** over the polynomial ring in its five coefficients:
-- `a_i = X_i`.
noncomputable def universalWeierstrass : WeierstrassCurve (MvPolynomial (Fin 5) ℤ) where
  a₁ := MvPolynomial.X 0
  a₂ := MvPolynomial.X 1
  a₃ := MvPolynomial.X 2
  a₄ := MvPolynomial.X 3
  a₆ := MvPolynomial.X 4
```
[DATA]

```lean
-- The **Weierstrass-atlas coefficient ring** `ℤ[a₁,…,a₆][Δ⁻¹]`: the coefficient polynomial
-- ring with the discriminant inverted.
abbrev WeierstrassAtlasRing : Type := Localization.Away universalWeierstrass.Δ
```
[DATA]

```lean
-- The universal Weierstrass curve pushed to the atlas ring (discriminant inverted).
noncomputable def universalWeierstrassLoc : WeierstrassCurve WeierstrassAtlasRing :=
  universalWeierstrass.map (algebraMap _ _)
```
[DATA]

```lean
-- Over the atlas ring the discriminant is a unit, so the universal curve is elliptic.
instance : universalWeierstrassLoc.IsElliptic :=
```
[PROVED]

```lean
-- The **Weierstrass atlas** `U = Spec ℤ[a₁,…,a₆][Δ⁻¹]`.
noncomputable def weierstrassAtlas : Scheme.{0} := Spec (.of WeierstrassAtlasRing)
```
[DATA]

```lean
instance : IsAffine weierstrassAtlas := isAffine_Spec _
```
[PROVED]

```lean
-- The **universal Weierstrass elliptic curve** `E_U`, the total space over the atlas.
noncomputable def universalCurve : Scheme.{0} := projModel universalWeierstrassLoc
```
[DATA]

```lean
-- The structure morphism `E_U → U` of the universal Weierstrass curve.
noncomputable def universalCurveπ : universalCurve ⟶ weierstrassAtlas :=
  projModelπ universalWeierstrassLoc
```
[DATA]

```lean
-- The universal Weierstrass curve is **proper** over the atlas.
instance : IsProper universalCurveπ := projModelπ_isProper _
```
[PROVED]

```lean
-- The universal Weierstrass curve is **smooth of relative dimension one** over the atlas.
theorem universalCurve_smooth : SmoothOfRelativeDimension 1 universalCurveπ :=
  projModel_smooth _
```
[PROVED]

```lean
-- The **zero section** `U → E_U` of the universal Weierstrass curve.
noncomputable def universalCurveZero : weierstrassAtlas ⟶ universalCurve :=
  projModelZero universalWeierstrassLoc
```
[DATA]

```lean
@[simp]
theorem universalCurveZero_π : universalCurveZero ≫ universalCurveπ = 𝟙 weierstrassAtlas :=
  projModelZero_projModelπ universalWeierstrassLoc
```
[PROVED]

```lean
-- The crux affine identity: the top affine chart's `isoSpec.hom` composed with the scheme's
-- `isoSpec.inv` is the top inclusion.
theorem crux_test (h : IsAffineOpen (⊤ : (weierstrassAtlas).Opens)) :
    h.isoSpec.hom ≫ weierstrassAtlas.isoSpec.inv = (⊤ : (weierstrassAtlas).Opens).ι := by
```
[PROVED]

```lean
-- The universal Weierstrass curve is locally Weierstrass (it *is* a global Weierstrass
-- model over the affine atlas — the whole space `⊤` witnesses it).
open Limits in
theorem universalCurve_localModel :
    LocallyWeierstrass universalCurveπ universalCurveZero universalCurveZero_π := by
  -- … (chart compatibility c1 proved; `case c2 => sorry` — T-W5a remainder)
```
[SORRY]

---

## projects/ModularCurves/ModularCurves/ModularCurve/VRhoGroup.lean  (204 lines)

The group structure on `V_ρ` (T-F1c): the `ρ`-twisted `(ℤ/N)²` is a group in continuous Galois sets — this file constructs the addition/zero/negation morphisms on the `ContAction` side and transports the addition through the Galois correspondence to `V_ρ`.

File-wide context: `namespace ModularCurves; open ModularCurves.FiniteEtaleGalois; variable {N : ℕ} [NeZero N]`.

```lean
-- The square of the `ρ`-twisted fiber: carrier `(ℤ/N)² × (ℤ/N)²` with the diagonal
-- Galois action.
noncomputable abbrev rhoSqAction (D : GaloisRepData N) :
    Action FintypeCat.{0} (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) where
  V := FintypeCat.of ((Fin 2 → ZMod N) × (Fin 2 → ZMod N))
  ρ :=
    { toFun := fun σ => FintypeCat.homMk
        (fun vw => (D.ρ (galSepMulEquivGalQ σ) • vw.1, D.ρ (galSepMulEquivGalQ σ) • vw.2))
      -- … (map_one', map_mul' proved) }
```
[DATA]

```lean
-- The diagonal action on the square is continuous: the kernel of `ρ` acts trivially.
open scoped Pointwise in
lemma rhoSqAction_isContinuous (D : GaloisRepData N) :
    (rhoSqAction D).IsContinuous := by
```
[PROVED]

```lean
-- The square as a continuous Galois set.
noncomputable abbrev rhoSqContAction (D : GaloisRepData N) :
    ContAction FintypeCat.{0} (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
  ⟨rhoSqAction D, rhoSqAction_isContinuous D⟩
```
[DATA]

```lean
-- Coordinatewise addition is Galois-equivariant (`ρ σ` is linear), giving the
-- addition morphism of continuous Galois sets.
noncomputable def rhoAddMor (D : GaloisRepData N) :
    rhoSqContAction D ⟶ rhoContAction D :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk (fun vw => vw.1 + vw.2)
      -- … (comm proved) }
```
[DATA]

```lean
-- The one-point Galois set.
noncomputable abbrev pointAction :
    Action FintypeCat.{0} (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) where
  V := FintypeCat.of PUnit
  ρ := { toFun := fun _ => FintypeCat.homMk id
         map_one' := rfl
         map_mul' := fun _ _ => rfl }
```
[DATA]

```lean
lemma pointAction_isContinuous : pointAction.IsContinuous := by
```
[PROVED]

```lean
-- The zero section: the one-point continuous Galois set.
noncomputable abbrev rhoPointContAction :
    ContAction FintypeCat.{0} (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
  ⟨pointAction, pointAction_isContinuous⟩
```
[DATA]

```lean
-- The zero morphism of continuous Galois sets.
noncomputable def rhoZeroMor (D : GaloisRepData N) :
    rhoPointContAction ⟶ rhoContAction D :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk (fun _ => 0)
      -- … (comm proved) }
```
[DATA]

```lean
-- Negation is Galois-equivariant, giving the inverse morphism.
noncomputable def rhoNegMor (D : GaloisRepData N) :
    rhoContAction D ⟶ rhoContAction D :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk (fun v => -v)
      -- … (comm proved) }
```
[DATA]

```lean
-- First projection of the square.
noncomputable def rhoSqFst (D : GaloisRepData N) :
    rhoSqContAction D ⟶ rhoContAction D :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk Prod.fst
      comm := fun σ => FintypeCat.hom_ext _ _ fun vw => rfl }
```
[DATA]

```lean
-- Second projection of the square.
noncomputable def rhoSqSnd (D : GaloisRepData N) :
    rhoSqContAction D ⟶ rhoContAction D :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk Prod.snd
      comm := fun σ => FintypeCat.hom_ext _ _ fun vw => rfl }
```
[DATA]

```lean
-- The square with its projections is the categorical binary product in the category
-- of continuous Galois sets (leaf F1c-2).
noncomputable def rhoSqIsProduct (D : GaloisRepData N) :
    IsLimit (BinaryFan.mk (rhoSqFst D) (rhoSqSnd D)) := by
```
[DATA]

```lean
-- Transport of the square through the Galois correspondence: the algebra of the
-- `ρ`-square is the tensor square of `vRhoAlgebra` (leaf F1c-3).
noncomputable def vRhoSqAlgebraIso (D : GaloisRepData N) :
    (finiteEtaleEquivContAction ℚ).inverse.obj (rhoSqContAction D) ≅
      Opposite.op (FiniteEtaleGalois.tensorObj (vRhoAlgebra D) (vRhoAlgebra D)) := by
```
[DATA]

```lean
-- The comultiplication: the finite étale algebra map corresponding to the addition
-- of the `ρ`-twisted Galois module (leaf F1c-4).
noncomputable def vRhoComulHom (D : GaloisRepData N) :
    vRhoAlgebra D ⟶ FiniteEtaleGalois.tensorObj (vRhoAlgebra D) (vRhoAlgebra D) :=
  ((vRhoSqAlgebraIso D).inv ≫
    (finiteEtaleEquivContAction ℚ).inverse.map (rhoAddMor D)).unop
```
[DATA]

```lean
-- **(T-F1c)** The addition morphism of `V_ρ`: `V_ρ ×_ℚ V_ρ ⟶ V_ρ`, `Spec` of the
-- comultiplication through the tensor identification of the fibre product.
noncomputable def vRhoAdd (D : GaloisRepData N) :
    pullback (vRhoπ D) (vRhoπ D) ⟶ vRho D :=
  (AlgebraicGeometry.pullbackSpecIso ℚ (vRhoAlgebra D : Type 0)
    (vRhoAlgebra D : Type 0)).hom ≫
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (vRhoComulHom D).hom.hom.toRingHom)
```
[DATA]

---

## projects/ModularCurves/ModularCurves/ModularCurve/YRho.lean  (473 lines)

The twisted modular curve `Y(ρ̄_N)` (Buzzard, *Formalizing Fermat* Lecture 8, p. 33): Galois representation data with cyclotomic determinant and pairing normalisation, the finite étale scheme `V_ρ` via the Grothendieck–Galois correspondence with its points description, ρ-level structures on elliptic curves, and the representability / geometric-irreducibility statements.

```lean
-- [context: namespace ModularCurves]
-- The absolute Galois group of `ℚ` (with its Krull topology, from mathlib): stated as
-- the automorphism group of the algebraic closure, definitionally
-- `Field.absoluteGaloisGroup ℚ` (kept as an `abbrev` of the unfolded form so the group and
-- Krull-topology instances apply).
abbrev GalQ : Type := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ
```
[DATA]

```lean
-- **(T-F0)** `ℚ̄` contains exactly `N` `N`-th roots of unity (char. 0, algebraically
-- closed).
theorem card_rootsOfUnity_algClosureQ (N : ℕ) [NeZero N] :
    Fintype.card { x // x ∈ rootsOfUnity N (AlgebraicClosure ℚ) } = N := by
```
[PROVED]

```lean
-- A mod-`N` Galois representation datum for the twisted modular curve: a continuous
-- action of `Gal(ℚ̄/ℚ)` on `(ℤ/N)²` with cyclotomic determinant, together with the pairing
-- normalisation `p`.
structure GaloisRepData (N : ℕ) [NeZero N] where
  ρ : GalQ →* Matrix.GeneralLinearGroup (Fin 2) (ZMod N)
  ker_open : IsOpen (X := GalQ) (MonoidHom.ker ρ : Set GalQ)
  det_cyclo : ∀ σ : GalQ,
    Matrix.GeneralLinearGroup.det (ρ σ) =
      modularCyclotomicCharacter (AlgebraicClosure ℚ) (card_rootsOfUnity_algClosureQ N) σ.toRingEquiv
  p : Multiplicative (ZMod N) ≃* rootsOfUnity N (AlgebraicClosure ℚ)
  p_equivariant : ∀ (σ : GalQ) (x : Multiplicative (ZMod N)),
    σ ((p x : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
      ((p (x ^ ((modularCyclotomicCharacter (AlgebraicClosure ℚ)
        (card_rootsOfUnity_algClosureQ N) σ.toRingEquiv : (ZMod N)ˣ) : ZMod N).val) :
          (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
```
[DATA]

```lean
-- [context: section GaloisSepBridge]
-- Concrete-field instance registration (see the AG-GG-3 protocol note): mathlib's
-- `separableClosure` instances do not unify against the `SeparableClosure` abbreviation at
-- concrete fields.
open ModularCurves.FiniteEtaleGalois in
instance : CompactSpace (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
  compactSpace_galSepClosure ℚ
```
[PROVED]

```lean
open ModularCurves.FiniteEtaleGalois in
noncomputable instance : PreGaloisCategory.IsFundamentalGroup
    (CommAlgCat.FiniteEtale.fiber ℚ (SeparableClosure ℚ) :
      (CommAlgCat.FiniteEtale.{0} ℚ)ᵒᵖ ⥤ FintypeCat.{0})
    (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
  isFundamentalGroup_galSepClosure (k := ℚ)
```
[PROVED]

```lean
-- In characteristic zero the separable closure is the algebraic closure.
noncomputable def sepClosureQAlgEquiv : SeparableClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ :=
```
[DATA]

```lean
-- The multiplicative comparison between the two absolute Galois groups.
noncomputable def galSepMulEquivGalQ :
    (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) ≃* GalQ :=
  AlgEquiv.autCongr sepClosureQAlgEquiv
```
[DATA]

```lean
lemma continuous_galSepMulEquivGalQ : Continuous galSepMulEquivGalQ := by
```
[PROVED]

```lean
-- The homeomorphic multiplicative comparison between the Galois groups of the
-- separable and the algebraic closure of `ℚ`.
noncomputable def galSepContinuousMulEquivGalQ :
    (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) ≃ₜ* GalQ :=
  { galSepMulEquivGalQ with
    continuous_toFun := continuous_galSepMulEquivGalQ
    -- … (continuous_invFun proved) }
```
[DATA]

```lean
-- [context: section RhoAction; open ModularCurves.FiniteEtaleGalois;
--  open scoped FintypeCatDiscrete; variable {N : ℕ} [NeZero N]]
-- The `(ℤ/N)²`-fiber as a `Gal(ℚ^sep/ℚ)`-set via `ρ`.
noncomputable abbrev rhoAction (D : GaloisRepData N) :
    Action FintypeCat.{0} (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) where
  V := FintypeCat.of (Fin 2 → ZMod N)
  ρ :=
    { toFun := fun σ => FintypeCat.homMk (fun v => D.ρ (galSepMulEquivGalQ σ) • v)
      -- … (map_one', map_mul' proved) }
```
[DATA]

```lean
-- The kernel of the `ρ`-action on the separable-closure side is open.
lemma rhoAction_ker_open (D : GaloisRepData N) :
    IsOpen {σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ |
      D.ρ (galSepMulEquivGalQ σ) = 1} := by
```
[PROVED]

```lean
-- The `ρ`-action is continuous (the fiber is discrete and the kernel is open).
open scoped Pointwise in
lemma rhoAction_isContinuous (D : GaloisRepData N) :
    (rhoAction D).IsContinuous := by
```
[PROVED]

```lean
-- The `ρ`-twisted `(ℤ/N)²` as a continuous Galois set.
noncomputable abbrev rhoContAction (D : GaloisRepData N) :
    ContAction FintypeCat.{0} (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
  ⟨rhoAction D, rhoAction_isContinuous D⟩
```
[DATA]

```lean
-- The finite étale `ℚ`-algebra corresponding to the `ρ`-twisted `(ℤ/N)²` under the
-- Galois correspondence.
noncomputable def vRhoAlgebra (D : GaloisRepData N) : CommAlgCat.FiniteEtale.{0} ℚ :=
  ((finiteEtaleEquivContAction ℚ).inverse.obj (rhoContAction D)).unop
```
[DATA]

```lean
-- **(T-F1, was DS5)** The finite étale scheme `V_ρ` over `ℚ` attached to the Galois
-- module `(ℤ/N)²` via `ρ`: the spectrum of the finite étale algebra corresponding to the
-- `ρ`-twisted `(ℤ/N)²` under the Grothendieck–Galois correspondence
-- `(FiniteEtale ℚ)ᵒᵖ ≌ ContAction FintypeCat Gal(ℚ^sep/ℚ)`.
noncomputable def vRho {N : ℕ} [NeZero N] (D : GaloisRepData N) : Scheme.{0} :=
  Spec (.of (vRhoAlgebra D : Type 0))
```
[DATA]

```lean
-- **(T-F1)** The structure morphism of `V_ρ`.
noncomputable def vRhoπ {N : ℕ} [NeZero N] (D : GaloisRepData N) :
    vRho D ⟶ Spec (.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ (vRhoAlgebra D : Type 0)))
```
[DATA]

```lean
-- **(T-F1a, specification of DS5)** `V_ρ ⟶ Spec ℚ` is finite étale.
theorem vRhoπ_finite_etale {N : ℕ} [NeZero N] (D : GaloisRepData N) :
    IsFinite (vRhoπ D) ∧ Etale (vRhoπ D) := by
```
[PROVED]

```lean
-- **(DS5c / T-F1b, specification of DS5)** The canonical `ℚ̄`-points description of
-- `V_ρ`: points over `ℚ̄` biject with `(ℤ/N)²`.
noncomputable def vRhoPointsEquiv {N : ℕ} [NeZero N] (D : GaloisRepData N) :
    { h : Spec (.of (AlgebraicClosure ℚ)) ⟶ vRho D //
        h ≫ vRhoπ D = Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) }
      ≃ (Fin 2 → ZMod N) :=
  ((specPointsEquivAlgHom ℚ (vRhoAlgebra D : Type 0) (AlgebraicClosure ℚ)).trans
    (AlgEquiv.arrowCongr AlgEquiv.refl sepClosureQAlgEquiv.symm)).trans
    (FiniteEtaleGalois.pointsEquivOfContAction ℚ (rhoContAction D))
```
[DATA]

```lean
-- **(T-F1b, companion specification)** The points bijection is Galois-equivariant:
-- translating a `ℚ̄`-point of `V_ρ` by `σ : Gal(ℚ̄/ℚ)` corresponds to acting by `ρ σ`
-- on `(ℤ/N)²`.
theorem vRhoPointsEquiv_equivariant {N : ℕ} [NeZero N] (D : GaloisRepData N) (σ : GalQ)
    (h : { h : Spec (.of (AlgebraicClosure ℚ)) ⟶ vRho D //
        h ≫ vRhoπ D = Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) }) :
    vRhoPointsEquiv D ⟨Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ h.1, by
        rw [Category.assoc, h.2, ← Spec.map_comp]
        congr 1
        ext r
        exact σ.commutes r⟩ =
      D.ρ σ • vRhoPointsEquiv D h := by
```
[PROVED]

```lean
-- The `(ℤ/N)²`-coordinate of a `ℚ̄`-valued raw `N`-torsion point of `E`, read through a
-- `ρ`-level isomorphism and the canonical points description of `V_ρ`.
noncomputable def coord {N : ℕ} [NeZero N] (D : GaloisRepData N) {T : Scheme.{0}}
    (sT : T ⟶ Spec (.of ℚ)) {E : EllipticCurve T}
    (torsionIso : E.torsion N ≅ pullback (vRhoπ D) sT)
    (hOver : torsionIso.hom ≫ pullback.snd (vRhoπ D) sT = E.torsionπ N)
    (t : Spec (.of (AlgebraicClosure ℚ)) ⟶ T)
    (ht : t ≫ sT = Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))
    (x : E.Point t) (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero) : Fin 2 → ZMod N :=
  vRhoPointsEquiv D
    ⟨E.pointToTorsion x hx ≫ torsionIso.hom ≫ pullback.fst _ _, by
      rw [Category.assoc, Category.assoc, pullback.condition,
        ← Category.assoc torsionIso.hom, hOver, ← Category.assoc,
        E.pointToTorsion_torsionπ, ht]⟩
```
[DATA]

```lean
-- The pairing-compatibility relation at a geometric point: `e_N(x,y) = p(a₁b₂ − a₂b₁)`
-- where `(a₁,a₂), (b₁,b₂)` are the coordinates of `x, y`.
def PairingCompatAt {N : ℕ} [NeZero N] (D : GaloisRepData N) {T : Scheme.{0}}
    (sT : T ⟶ Spec (.of ℚ)) {E : EllipticCurve T}
    (torsionIso : E.torsion N ≅ pullback (vRhoπ D) sT)
    (hOver : torsionIso.hom ≫ pullback.snd (vRhoπ D) sT = E.torsionπ N)
    (t : Spec (.of (AlgebraicClosure ℚ)) ⟶ T)
    (ht : t ≫ sT = Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))
    (x y : E.Point t)
    (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero)
    (hy : y.1 ≫ E.mulByHom N = t ≫ E.zero) : Prop := sorry
```
[DATA-SORRY]  (the `Prop` itself is `sorry`-defined; discharged by ticket T-F3, register DS5d)

```lean
-- A **ρ-level structure** on an elliptic curve `E` over a `ℚ`-scheme `T`: an
-- isomorphism of group schemes over `T` between `E[N]` and the pullback of `V_ρ`, carrying
-- the Weil pairing `e_N` to the pairing `p` of the datum.
structure RhoLevelStructure {N : ℕ} [NeZero N] (D : GaloisRepData N)
    {T : Scheme.{0}} (sT : T ⟶ Spec (.of ℚ)) (E : EllipticCurve T) where
  torsionIso : E.torsion N ≅ pullback (vRhoπ D) sT
  over_T : torsionIso.hom ≫ pullback.snd _ _ = E.torsionπ N
  coords_additive : ∀ (t : Spec (.of (AlgebraicClosure ℚ)) ⟶ T)
    (ht : t ≫ sT = Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))
    (x y : E.Point t)
    (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero) (hy : y.1 ≫ E.mulByHom N = t ≫ E.zero)
    (hxy : (x + y).1 ≫ E.mulByHom N = t ≫ E.zero),
    coord D sT torsionIso over_T t ht (x + y) hxy =
      coord D sT torsionIso over_T t ht x hx + coord D sT torsionIso over_T t ht y hy
  pairing_compat : ∀ (t : Spec (.of (AlgebraicClosure ℚ)) ⟶ T)
    (ht : t ≫ sT = Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))
    (x y : E.Point t)
    (hx : x.1 ≫ E.mulByHom N = t ≫ E.zero) (hy : y.1 ≫ E.mulByHom N = t ≫ E.zero),
    PairingCompatAt D sT torsionIso over_T t ht x y hx hy
```
[DATA]

```lean
-- **(T-F6 = expert review Q9: the symplectic Isom-scheme route)** Relative
-- representability of the ρ-level problem: for every elliptic curve `E` over a
-- `ℚ`-scheme `T`, the functor `T' ↦ {ρ-level structures on E ×_T T'}` is representable
-- by a finite étale `T`-scheme — the symplectic isomorphism scheme
-- `Isom^symp(E[N], V_ρ̄)`.
theorem rhoLevel_relativelyRepresentable {N : ℕ} [NeZero N] (hN : 3 ≤ N)
    (D : GaloisRepData N) {T : Scheme.{0}} (sT : T ⟶ Spec (.of ℚ))
    (E : EllipticCurve T) :
    ∃ (I : Scheme.{0}) (f : I ⟶ T), IsFinite f ∧ Etale f ∧
      ∀ {T' : Scheme.{0}} (k : T' ⟶ T),
        Nonempty ({ h : T' ⟶ I // h ≫ f = k } ≃
          RhoLevelStructure D (k ≫ sT) (E.baseChange k)) := by sorry
```
[SORRY]

```lean
-- The representing property for the twisted modular curve: `(Y, sY)` is a smooth
-- affine `ℚ`-curve whose `T`-points over `ℚ` are naturally the isomorphism classes of
-- pairs `(E, α)` — the quotient by pointed over-`T` isomorphisms carrying coordinates to
-- coordinates (DEF-4).
def RepresentsYRho {N : ℕ} [NeZero N] (D : GaloisRepData N) (Y : Scheme.{0})
    (sY : Y ⟶ Spec (.of ℚ)) : Prop :=
  SmoothOfRelativeDimension 1 sY ∧ IsAffineHom sY ∧
    ∀ (T : Scheme.{0}) (sT : T ⟶ Spec (.of ℚ)),
      Nonempty ({ h : T ⟶ Y // h ≫ sY = sT } ≃
        Quot (fun (a b : Σ E : EllipticCurve T, RhoLevelStructure D sT E) =>
          ∃ f : a.1 ≅ b.1,
            ∀ (t : Spec (.of (AlgebraicClosure ℚ)) ⟶ T)
              (ht : t ≫ sT =
                Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))
              (x : a.1.Point t)
              (hx : x.1 ≫ a.1.mulByHom N = t ≫ a.1.zero)
              (hx' : (f.hom.mapPoint x).1 ≫ b.1.mulByHom N = t ≫ b.1.zero),
              coord D sT b.2.torsionIso b.2.over_T t ht (f.hom.mapPoint x) hx' =
                coord D sT a.2.torsionIso a.2.over_T t ht x hx))
```
[DATA]

```lean
-- **(T-F4 = Buzzard p. 33, the main statement)** The twisted modular curve exists:
-- some `(Y, sY)` represents the ρ-level moduli problem in the sense of
-- `RepresentsYRho`.
theorem yRho_representable {N : ℕ} [NeZero N] (hN : 3 ≤ N) (D : GaloisRepData N) :
    ∃ (Y : Scheme.{0}) (sY : Y ⟶ Spec (.of ℚ)), RepresentsYRho D Y sY := by sorry
```
[SORRY]

```lean
-- **(T-F5, stream IRR)** Any curve representing the ρ-level problem is
-- geometrically irreducible over `ℚ`: its base change to `ℚ̄` is irreducible.
theorem yRho_geometricallyIrreducible {N : ℕ} [NeZero N] (hN : 3 ≤ N)
    (D : GaloisRepData N) (Y : Scheme.{0}) (sY : Y ⟶ Spec (.of ℚ))
    (hY : RepresentsYRho D Y sY) :
    IrreducibleSpace ↥(pullback sY
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))) := by sorry
```
[SORRY]

---

## Totals

| File | Public decls |
|---|---|
| Moduli/Coarse.lean | 6 |
| Moduli/EllCategory.lean | 10 |
| Moduli/GammaH.lean | 38 |
| Moduli/Groupoid.lean | 4 |
| Moduli/QuotientProblem.lean | 35 |
| Moduli/QuotientStack.lean | 44 |
| Moduli/Representability.lean | 15 |
| Moduli/Stack.lean | 2 |
| Moduli/WeierstrassAtlas.lean | 14 |
| ModularCurve/VRhoGroup.lean | 15 |
| ModularCurve/YRho.lean | 26 |
| **Total** | **209** |

Status breakdown: 92 [PROVED] · 19 [SORRY] · 91 [DATA] · 7 [DATA-SORRY].
# Inventory C — verbatim signature inventory of `projects/ModularCurves/ModularCurves/ForMathlib/` (28 files)

Convention: each public top-level declaration is listed verbatim from the `theorem`/`def`/... keyword through (but not including) `:=` / `where` / the proof body. Attribute lines, `variable (…) in`, `omit … in`, `open … in`, and `set_option … in` prefixes attached to a declaration are reproduced verbatim. `variable` lines giving the ambient binder context are reproduced at the top of each section. Marker legend: `[PROVED]` no sorry in body; `[SORRY]` body is/contains sorry; `[DATA]` a def/abbrev/structure/class/instance whose body is real data; `[DATA-SORRY]` a def whose body is sorry. The docstring's first sentence (when present) precedes each declaration as a `--` comment after the marker.

## ModularCurves/ForMathlib/AffinePointVariableChange.lean  (415 lines)
General coordinate change on affine points of a Weierstrass curve: `(x, y) ↦ (u⁻²(x−r), u⁻³(y−s(x−r)−t))` carries `Equation`/`Nonsingular` from `W` to `C • W` and induces a group isomorphism `W.Point ≃+ (C • W).Point`, with descent cocycle and base-ring naturality.

```lean
namespace WeierstrassCurve.VariableChange
variable {R : Type*} [CommRing R] (C : VariableChange R)

-- [DATA] The `x`-coordinate of `(x, y)` after the coordinate change `C = (u, r, s, t)`: `u⁻²(x - r)`.
def vcX (x : R) : R

-- [DATA] The `y`-coordinate of `(x, y)` after the coordinate change `C = (u, r, s, t)`: `u⁻³(y - s(x - r) - t)`.
def vcY (x y : R) : R

variable (W : WeierstrassCurve R)

-- [PROVED] The general coordinate change `C` carries a solution of the Weierstrass equation of `W` to a solution of the equation of `C • W`: the equation polynomial scales by `u⁻⁶`.
lemma equation_smul {x y : R} (h : W.toAffine.Equation x y) :
    (C • W).toAffine.Equation (C.vcX x) (C.vcY x y)

-- [PROVED] The general coordinate change `C` preserves nonsingularity: the gradient of the Weierstrass polynomial transforms by an invertible Jacobian (`∂/∂Y ↦ u⁻³·∂/∂Y`, `∂/∂X ↦ u⁻⁴(∂/∂X + s·∂/∂Y)`), so a smooth point of `W` maps to a smooth point of `C • W`.
lemma nonsingular_smul {x y : R} (h : W.toAffine.Nonsingular x y) :
    (C • W).toAffine.Nonsingular (C.vcX x) (C.vcY x y)

-- [PROVED] Equation-preservation is an iff: since `u⁻⁶` is a unit, the coordinate change reflects the Weierstrass equation as well as preserving it.
lemma equation_smul_iff {x y : R} :
    (C • W).toAffine.Equation (C.vcX x) (C.vcY x y) ↔ W.toAffine.Equation x y

-- [PROVED] Nonsingularity is likewise reflected by the coordinate change (the Jacobian is invertible), so a smooth point of `C • W` pulls back to a smooth point of `W`.
lemma nonsingular_smul' {x y : R} (h : (C • W).toAffine.Nonsingular (C.vcX x) (C.vcY x y)) :
    W.toAffine.Nonsingular x y

-- [PROVED] Nonsingularity is both preserved and reflected by the coordinate change.
lemma nonsingular_smul_iff {x y : R} :
    (C • W).toAffine.Nonsingular (C.vcX x) (C.vcY x y) ↔ W.toAffine.Nonsingular x y

-- [DATA] The `x`-coordinate map inverse to `vcX`: `x = u²X + r`.
def ivcX (X : R) : R

-- [DATA] The `y`-coordinate map inverse to `vcY`: `y = u³Y + s·u²X + t`.
def ivcY (X Y : R) : R

-- [PROVED]
@[simp] lemma vcX_ivcX (X : R) : C.vcX (C.ivcX X) = X

-- [PROVED]
@[simp] lemma vcY_ivcX_ivcY (X Y : R) : C.vcY (C.ivcX X) (C.ivcY X Y) = Y

-- [PROVED] Descent cocycle for the `x`-coordinate: applying `C'` then `C` is the change `C * C'`.
lemma vcX_comp (C C' : VariableChange R) (x : R) : (C * C').vcX x = C.vcX (C'.vcX x)

-- [PROVED] Descent cocycle for the `y`-coordinate.
lemma vcY_comp (C C' : VariableChange R) (x y : R) :
    (C * C').vcY x y = C.vcY (C'.vcX x) (C'.vcY x y)

variable {A : Type*} [CommRing A]

-- [PROVED] Naturality of `vcX` in the base ring: the coordinate change commutes with a ring map `φ`.
lemma vcX_map (φ : R →+* A) (C : VariableChange R) (x : R) :
    (C.map φ).vcX (φ x) = φ (C.vcX x)

-- [PROVED] Naturality of `vcY` in the base ring.
lemma vcY_map (φ : R →+* A) (C : VariableChange R) (x y : R) :
    (C.map φ).vcY (φ x) (φ y) = φ (C.vcY x y)

-- [DATA] The map on affine points induced by the coordinate change `C`, sending a point `(x, y)` on `W` to `(u⁻²(x - r), u⁻³(y - s(x - r) - t))` on `C • W` (and the point at infinity to itself).
def pointMap : W.toAffine.Point → (C • W).toAffine.Point

-- [PROVED]
@[simp] lemma pointMap_zero : C.pointMap W .zero = .zero

-- [PROVED]
@[simp] lemma pointMap_some {x y : R} (h : W.toAffine.Nonsingular x y) :
    C.pointMap W (.some x y h) = .some (C.vcX x) (C.vcY x y) (nonsingular_smul C W h)

-- [PROVED] Point-level descent cocycle: transporting `(C * C').pointMap` along `mul_smul` equals `C.pointMap ∘ C'.pointMap`.
lemma pointMap_mul (C C' : VariableChange R) (P : W.toAffine.Point) :
    mul_smul C C' W ▸ (C * C').pointMap W P = C.pointMap (C' • W) (C'.pointMap W P)

-- [PROVED] Unit condition of the descent cocycle: the identity coordinate change induces the identity on points (transported along `one_smul`).
lemma pointMap_one (P : W.toAffine.Point) :
    one_smul (M := VariableChange R) W ▸ (1 : VariableChange R).pointMap W P = P

-- [PROVED] The coordinate change commutes with the `y`-negation `negY`: transforming then negating equals negating then transforming.
lemma negY_smul (x y : R) :
    (C • W).toAffine.negY (C.vcX x) (C.vcY x y) = C.vcY x (W.toAffine.negY x y)

-- [PROVED] The coordinate change transforms the `x`-coordinate of a sum: for the transformed slope `u⁻¹(ℓ - s)`, the `addX` of `C • W` is `vcX` of the `addX` of `W`.
lemma addX_smul (x₁ x₂ ℓ : R) :
    (C • W).toAffine.addX (C.vcX x₁) (C.vcX x₂) (↑C.u⁻¹ * (ℓ - C.s))
      = C.vcX (W.toAffine.addX x₁ x₂ ℓ)

-- [PROVED] The coordinate change transforms the pre-negation `y`-coordinate of a sum.
lemma negAddY_smul (x₁ x₂ y₁ ℓ : R) :
    (C • W).toAffine.negAddY (C.vcX x₁) (C.vcX x₂) (C.vcY x₁ y₁) (↑C.u⁻¹ * (ℓ - C.s))
      = C.vcY (W.toAffine.addX x₁ x₂ ℓ) (W.toAffine.negAddY x₁ x₂ y₁ ℓ)

-- [PROVED] The coordinate change transforms the `y`-coordinate of a sum.
lemma addY_smul (x₁ x₂ y₁ ℓ : R) :
    (C • W).toAffine.addY (C.vcX x₁) (C.vcX x₂) (C.vcY x₁ y₁) (↑C.u⁻¹ * (ℓ - C.s))
      = C.vcY (W.toAffine.addX x₁ x₂ ℓ) (W.toAffine.addY x₁ x₂ y₁ ℓ)

-- [PROVED] The induced point map is a group anti/homomorphism for negation: `pointMap (-P) = -pointMap P`.
lemma pointMap_neg (P : W.toAffine.Point) : C.pointMap W (-P) = -(C.pointMap W P)

-- section Field
variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} (C : VariableChange F)

-- [PROVED] The coordinate change scales the addition `slope` (secant case): the secant of `C • W` through the transformed points is `u⁻¹` times the `s`-shifted secant of `W`.
lemma slope_smul_of_X_ne {x₁ x₂ y₁ y₂ : F} (hx : x₁ ≠ x₂) :
    (C • W).toAffine.slope (C.vcX x₁) (C.vcX x₂) (C.vcY x₁ y₁) (C.vcY x₂ y₂)
      = ↑C.u⁻¹ * (W.toAffine.slope x₁ x₂ y₁ y₂ - C.s)

-- [PROVED] The coordinate change scales the addition `slope` (tangent case): the tangent slope of `C • W` at the transformed point is `u⁻¹` times the `s`-shifted tangent slope of `W`.
lemma slope_smul_of_Y_ne {x₁ x₂ y₁ y₂ : F} (hx : x₁ = x₂) (hy : y₁ ≠ W.toAffine.negY x₂ y₂)
    (hne : y₁ ≠ W.toAffine.negY x₁ y₁) :
    (C • W).toAffine.slope (C.vcX x₁) (C.vcX x₂) (C.vcY x₁ y₁) (C.vcY x₂ y₂)
      = ↑C.u⁻¹ * (W.toAffine.slope x₁ x₂ y₁ y₂ - C.s)

-- [PROVED] The coordinate change scales the addition `slope` by `u⁻¹` (with the `s`-shift), in either the secant or tangent branch of the group law (i.e. whenever the sum is not the point at infinity).
lemma slope_smul {x₁ x₂ y₁ y₂ : F} (hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂))
    (hne : x₁ = x₂ → y₁ ≠ W.toAffine.negY x₁ y₁) :
    (C • W).toAffine.slope (C.vcX x₁) (C.vcX x₂) (C.vcY x₁ y₁) (C.vcY x₂ y₂)
      = ↑C.u⁻¹ * (W.toAffine.slope x₁ x₂ y₁ y₂ - C.s)

-- [PROVED] `vcX` is injective (the coordinate change scales by the unit `u⁻²`).
omit [DecidableEq F] in
lemma vcX_ne {x₁ x₂ : F} (hx : x₁ ≠ x₂) : C.vcX x₁ ≠ C.vcX x₂

-- [PROVED] The induced point map is additive: `pointMap (P + Q) = pointMap P + pointMap Q`.
lemma pointMap_add (P Q : W.toAffine.Point) :
    C.pointMap W (P + Q) = C.pointMap W P + C.pointMap W Q

-- [PROVED] The induced point map is injective (the coordinate change is a monomorphism on points).
lemma pointMap_injective : Function.Injective (C.pointMap W)

-- [DATA] The coordinate change `C` as a group homomorphism on affine points, `W.Point →+ (C • W).Point`. (`where` fields: toFun := C.pointMap W, map_zero', map_add'.)
def pointHom : W.toAffine.Point →+ (C • W).toAffine.Point where

-- [PROVED]
@[simp] lemma pointHom_apply (P : W.toAffine.Point) : C.pointHom P = C.pointMap W P

-- [PROVED]
lemma pointHom_injective : Function.Injective (C.pointHom (W := W))

-- [PROVED] The induced point map is surjective: every point of `C • W` is the image of its preimage under the inverse coordinate maps `ivcX`/`ivcY`.
omit [DecidableEq F] in
lemma pointMap_surjective : Function.Surjective (C.pointMap W)

-- [DATA] The coordinate change `C` as a group **isomorphism** on affine points, `W.Point ≃+ (C • W).Point`: the elliptic-curve group law is invariant under a change of Weierstrass coordinates (ticket T-W7).
noncomputable def pointEquiv : W.toAffine.Point ≃+ (C • W).toAffine.Point

-- [PROVED]
@[simp] lemma pointEquiv_apply (P : W.toAffine.Point) : C.pointEquiv P = C.pointMap W P

-- [PROVED] The group iso is compatible with multiplication-by-`n`, so it carries `n`-torsion to `n`-torsion — the invariance a level structure needs under a coordinate change (ticket T-W8).
lemma pointEquiv_zsmul (n : ℤ) (P : W.toAffine.Point) :
    C.pointEquiv (n • P) = n • C.pointEquiv P
```
(38 public declarations)

## ModularCurves/ForMathlib/AffineQuotient.lean  (916 lines)
The invariants morphism `invariantsπ : Spec B ⟶ Spec Bᴳ` for a finite group action is the categorical quotient of `Spec B` by `G` in the category of schemes: uniqueness and existence of descent, the universal property, plus stable-open separation, quotient-map topology, and the `j`-relative descent keystone.

```lean
namespace AlgebraicGeometry
variable {G : Type*} [Group G]
variable {B : Type u} [CommRing B] [MulSemiringAction G B]
variable (R : Type v) [CommRing R] [Algebra R B] [SMulCommClass G R B]
-- section Algebra: variable [Finite G]

-- [PROVED] **Factorization through the localized invariants** (the algebra engine of the affine quotient): a ring hom `φ : C →+* B_a`, `a` an invariant, whose image is fixed by the localized `G`-action factors uniquely through the localized inclusion `(Bᴳ)_a →+* B_a`.
theorem existsUnique_factor_fixedPoints_away {C : Type u} [CommRing C]
    (a : FixedPoints.subalgebra R B G)
    (φ : C →+* Localization.Away ((a : B)))
    (hφ : ∀ (g : G) (c : C), MulSemiringAction.awayHom (fun g => a.2 g) g (φ c) = φ c) :
    ∃! ψ : C →+* Localization.Away a,
      (IsLocalization.map (Localization.Away ((a : B)))
        (algebraMap (FixedPoints.subalgebra R B G) B)
        (Submonoid.powers_le_comap_algebraMap R a)).comp ψ = φ

-- [PROVED] Uniqueness of descent along the invariants morphism, in restriction-stable form: for an open immersion `j : W ⟶ Spec Bᴳ`, two morphisms out of `W` agreeing after precomposition with the pullback of `invariantsπ` along `j` are equal.
variable (G B) in
theorem invariantsπ_hom_ext_of_isOpenImmersion [Finite G] {W Y : Scheme.{u}}
    (j : W ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G)))
    [IsOpenImmersion j] (h₁ h₂ : W ⟶ Y)
    (H : pullback.snd (invariantsπ G B R) j ≫ h₁ =
      pullback.snd (invariantsπ G B R) j ≫ h₂) :
    h₁ = h₂

-- [PROVED] Uniqueness of descent along the invariants morphism: `invariantsπ` is an epimorphism of schemes.
variable (G B) in
theorem invariantsπ_hom_ext [Finite G] {Y : Scheme.{u}}
    (h₁ h₂ : Spec (CommRingCat.of (FixedPoints.subalgebra R B G)) ⟶ Y)
    (H : invariantsπ G B R ≫ h₁ = invariantsπ G B R ≫ h₂) :
    h₁ = h₂

-- [PROVED] Existence of descent: every `G`-invariant morphism out of `Spec B` factors through the invariants morphism.
variable (G B) in
theorem exists_invariantsπ_lift [Finite G] {Y : Scheme.{u}}
    (f : Spec (CommRingCat.of B) ⟶ Y) (hf : ∀ g : G, specSMul g ≫ f = f) :
    ∃ q : Spec (CommRingCat.of (FixedPoints.subalgebra R B G)) ⟶ Y,
      invariantsπ G B R ≫ q = f

-- [PROVED] **The affine quotient by a finite group** ([Loeffler, *Modular curves*, Prop 3.6.1], affine case; SGA I V.1.1; Stacks 07S7): `Spec Bᴳ` together with the invariants morphism represents the functor `Y ↦ {G-invariant morphisms Spec B ⟶ Y}` — every `G`-invariant morphism out of `Spec B` factors uniquely through `invariantsπ : Spec B ⟶ Spec Bᴳ`.
variable (G B) in
theorem existsUnique_invariantsπ_lift [Finite G] {Y : Scheme.{u}}
    (f : Spec (CommRingCat.of B) ⟶ Y) (hf : ∀ g : G, specSMul g ≫ f = f) :
    ∃! q : Spec (CommRingCat.of (FixedPoints.subalgebra R B G)) ⟶ Y,
      invariantsπ G B R ≫ q = f

-- [PROVED] **Invariant basic opens form a basis of the stable opens** (the separation step of the quotient construction, isolated): inside `Spec B`, every `G`-stable open neighbourhood of a point contains an invariant basic open neighbourhood `D((a : B))`, `a ∈ Bᴳ`.
variable (G B) in
theorem exists_mem_basicOpen_subset_of_stable [Finite G]
    {U : Set (Spec (CommRingCat.of B))} (hU : IsOpen U)
    (hstable : ∀ (g : G) (x : Spec (CommRingCat.of B)), x ∈ U → specSMul g x ∈ U)
    (x : Spec (CommRingCat.of B)) (hx : x ∈ U) :
    ∃ a : FixedPoints.subalgebra R B G,
      x ∈ PrimeSpectrum.basicOpen ((a : B)) ∧
      (↑(PrimeSpectrum.basicOpen ((a : B))) : Set (PrimeSpectrum B)) ⊆ U

-- [PROVED] The invariants morphism is a topological quotient map (it is a closed surjection).
variable (G B) in
theorem invariantsπ_isQuotientMap [Finite G] :
    Topology.IsQuotientMap ⇑(invariantsπ G B R).base

-- [PROVED] Images of `G`-stable opens under the invariants morphism are open.
variable (G B) in
theorem isOpen_image_invariantsπ_of_stable [Finite G]
    {U : Set (Spec (CommRingCat.of B))} (hU : IsOpen U)
    (hstable : ∀ (g : G) (x : Spec (CommRingCat.of B)), x ∈ U → specSMul g x ∈ U) :
    IsOpen (⇑(invariantsπ G B R).base '' U)

-- [DATA] The `G`-action on `pullback π j` covering `specSMul` (the `j`-relative action of the descent theory).
variable (G B) in
noncomputable def pullbackSpecSMul {Q' : Scheme.{u}}
    (j : Q' ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G))) (g : G) :
    pullback (invariantsπ G B R) j ⟶ pullback (invariantsπ G B R) j

-- [PROVED]
@[reassoc (attr := simp)]
theorem pullbackSpecSMul_fst {Q' : Scheme.{u}}
    (j : Q' ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G))) (g : G) :
    pullbackSpecSMul G B R j g ≫ pullback.fst (invariantsπ G B R) j =
      pullback.fst (invariantsπ G B R) j ≫ specSMul g

-- [PROVED]
@[reassoc (attr := simp)]
theorem pullbackSpecSMul_snd {Q' : Scheme.{u}}
    (j : Q' ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G))) (g : G) :
    pullbackSpecSMul G B R j g ≫ pullback.snd (invariantsπ G B R) j =
      pullback.snd (invariantsπ G B R) j

-- [PROVED] **`j`-relative existence of descent** (the keystone of the glued quotient): for an open immersion `j : Q' ⟶ Spec Bᴳ`, every morphism out of `pullback π j` that is invariant for the relative action descends to `Q'`.
variable (G B) in
theorem exists_invariantsπ_lift_of_isOpenImmersion [Finite G] {Q' Y : Scheme.{u}}
    (j : Q' ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G)))
    [IsOpenImmersion j]
    (f : pullback (invariantsπ G B R) j ⟶ Y)
    (hf : ∀ g : G, pullbackSpecSMul G B R j g ≫ f = f) :
    ∃ q : Q' ⟶ Y, pullback.snd (invariantsπ G B R) j ≫ q = f
```
(12 public declarations)

## ModularCurves/ForMathlib/AwayCongr.lean  (107 lines)
Transport ring isomorphism for `HomogeneousLocalization.Away 𝒜 s` along element equalities `s = t`, with a `subst`-derived API on `Away.mk` normal forms and naturality against `Away.map`.

```lean
namespace ModularCurves
variable {ι R A : Type*} [AddCommMonoid ι] [DecidableEq ι]
  [CommRing R] [CommRing A] [Algebra R A]
  {𝒜 : ι → Submodule R A} [GradedAlgebra 𝒜]

-- [DATA] Transport an `Away` ring along an equality of localization elements.
noncomputable def awayCongr {s t : A} (h : s = t) : Away 𝒜 s ≃+* Away 𝒜 t

-- [PROVED]
@[simp]
lemma awayCongr_rfl {s : A} :
    (awayCongr (rfl : s = s) : Away 𝒜 s ≃+* Away 𝒜 s) = RingEquiv.refl _

-- [PROVED]
lemma awayCongr_mk {s t : A} (h : s = t) {i : ι} (hs : s ∈ 𝒜 i) (n : ℕ) (a : A)
    (ha : a ∈ 𝒜 (n • i)) :
    awayCongr (𝒜 := 𝒜) h (HomogeneousLocalization.Away.mk 𝒜 hs n a ha) =
      HomogeneousLocalization.Away.mk 𝒜 (h ▸ hs) n a ha

variable {σ B S : Type*} [CommRing S] [CommRing B] [Algebra S B]
  {ℬ : ι → Submodule S B} [GradedAlgebra ℬ]

-- [PROVED] `awayCongr` is natural against the graded `Away.map`.
lemma awayCongr_map {s t : A} (h : s = t) (g : GradedRingHom 𝒜 ℬ) (x : Away 𝒜 s) :
    HomogeneousLocalization.Away.map g t (awayCongr (𝒜 := 𝒜) h x) =
      awayCongr (𝒜 := ℬ) (congrArg g h)
        (HomogeneousLocalization.Away.map g s x)

-- [PROVED]
lemma awayCongr_trans {s t u : A} (h₁ : s = t) (h₂ : t = u) (x : Away 𝒜 s) :
    awayCongr (𝒜 := 𝒜) h₂ (awayCongr (𝒜 := 𝒜) h₁ x) =
      awayCongr (𝒜 := 𝒜) (h₁.trans h₂) x

-- [PROVED]
lemma awayCongr_self {s : A} (h : s = s) (x : Away 𝒜 s) :
    awayCongr (𝒜 := 𝒜) h x = x

-- [PROVED] `Away.map` only depends on the graded hom up to propositional equality, through the transport.
lemma awayMap_congr {g₁ g₂ : GradedRingHom 𝒜 ℬ} (h : g₁ = g₂) (s : A) (x : Away 𝒜 s) :
    HomogeneousLocalization.Away.map g₂ s x =
      awayCongr (𝒜 := ℬ) (congrArg (fun g : GradedRingHom 𝒜 ℬ => g s) h)
        (HomogeneousLocalization.Away.map g₁ s x)

variable {τ C T : Type*} [CommRing T] [CommRing C] [Algebra T C]
  {𝒞 : ι → Submodule T C} [GradedAlgebra 𝒞]

-- [PROVED] Applied form of `Away.map_comp`.
lemma awayMap_map (f : GradedRingHom 𝒜 ℬ) (g : GradedRingHom ℬ 𝒞) (s : A)
    (x : Away 𝒜 s) :
    HomogeneousLocalization.Away.map g (f s)
        (HomogeneousLocalization.Away.map f s x) =
      HomogeneousLocalization.Away.map (g.comp f) s x

variable {S' B' : Type*} [CommRing S'] [CommRing B'] [Algebra S' B']
  {ℬ' : ι → Submodule S' B'} [GradedAlgebra ℬ']

-- [PROVED] Comparing the two ways around a commuting square of graded homs, with transports along any equalities of the localization elements.
lemma awayMap_square {f₁ : GradedRingHom 𝒜 ℬ} {g₁ : GradedRingHom ℬ 𝒞}
    {f₂ : GradedRingHom 𝒜 ℬ'} {g₂ : GradedRingHom ℬ' 𝒞}
    (hsq : g₁.comp f₁ = g₂.comp f₂) (s : A) (x : Away 𝒜 s)
    {t : C} (h₁ : g₁ (f₁ s) = t) (h₂ : g₂ (f₂ s) = t) :
    awayCongr (𝒜 := 𝒞) h₁
        (HomogeneousLocalization.Away.map g₁ (f₁ s)
          (HomogeneousLocalization.Away.map f₁ s x)) =
      awayCongr (𝒜 := 𝒞) h₂
        (HomogeneousLocalization.Away.map g₂ (f₂ s)
          (HomogeneousLocalization.Away.map f₂ s x))
```
(9 public declarations)

## ModularCurves/ForMathlib/BijectiveResidueField.lean  (135 lines)
Bijectivity of a linear map between finite (flat) modules is detected on residue-field fibres, over a local ring and over any commutative ring at all maximal ideals.

```lean
-- section Local
variable {R : Type u} {M : Type v} {N : Type w} [CommRing R] [IsLocalRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

-- [PROVED] Over a local ring, a linear map into a finite module is surjective as soon as it is surjective after tensoring with the residue field (Nakayama).
theorem IsLocalRing.surjective_of_surjective_lTensor_residueField [Module.Finite R N]
    (φ : M →ₗ[R] N) (h : Surjective (φ.lTensor (ResidueField R))) :
    Surjective φ

-- [PROVED] Over a local ring, a linear map from a finite module to a finite flat module is bijective as soon as it is bijective after tensoring with the residue field.
theorem IsLocalRing.bijective_of_bijective_lTensor_residueField
    [Module.Finite R M] [Module.Finite R N] [Module.Flat R N]
    (φ : M →ₗ[R] N) (h : Bijective (φ.lTensor (ResidueField R))) :
    Bijective φ

-- section Global
variable {R : Type u} {M : Type v} {N : Type w} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

-- [PROVED] A linear map from a finite module to a finite flat module is bijective as soon as it is bijective after tensoring with the residue field of every maximal ideal.
theorem LinearMap.bijective_of_forall_bijective_lTensor_residueField
    [Module.Finite R M] [Module.Finite R N] [Module.Flat R N] (φ : M →ₗ[R] N)
    (h : ∀ (J : Ideal R) [J.IsMaximal], Bijective (φ.lTensor J.ResidueField)) :
    Bijective φ
```
(3 public declarations)

## ModularCurves/ForMathlib/CharpolyNorm.lean  (58 lines)
For a finite free `R`-algebra `B` and `b : B`, the characteristic polynomial of multiplication by `b` is the norm of `X ⊗ 1 − 1 ⊗ b` relative to `(R[X] ⊗[R] B)/R[X]` (KM 1.8.2).

```lean
namespace Algebra
variable (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B]
  [Module.Free R B] [Module.Finite R B]

-- [PROVED] **Characteristic polynomial as a norm** (KM 1.8.2): for a finite free `R`-algebra `B` and `b : B`, the characteristic polynomial of multiplication by `b` equals the norm, relative to `(R[X] ⊗[R] B) / R[X]`, of `X ⊗ 1 − 1 ⊗ b` ("`T − b`").
theorem charpoly_lmul_eq_norm (b : B) :
    (Algebra.lmul R B b).charpoly =
      Algebra.norm R[X] ((X : R[X]) ⊗ₜ[R] (1 : B) - (1 : R[X]) ⊗ₜ[R] b)
```
(1 public declaration)

## ModularCurves/ForMathlib/EtaleSectionsCount.lean  (184 lines)
For a formally étale, essentially-finite-type algebra over a separably closed field `K`, algebra homomorphisms `A →ₐ[K] K` biject with `PrimeSpectrum A` and number `finrank K A`; scheme form: a finite étale scheme over `Spec k` has exactly `finrank` many sections.

```lean
namespace ModularCurves
variable (K A : Type u) [Field K] [CommRing A] [Algebra K A] [EssFiniteType K A]
  [FormallyEtale K A] [IsSepClosed K]

-- [DATA] Algebra homomorphisms from a formally étale algebra over a separably closed field to the base field biject with the prime spectrum.
noncomputable def algHomEquivPrimeSpectrum : (A →ₐ[K] K) ≃ PrimeSpectrum A where

-- [PROVED] A formally étale, essentially-finite-type algebra over a separably closed field has exactly `finrank` many homomorphisms to the base field.
theorem natCard_algHom_eq_finrank : Nat.card (A →ₐ[K] K) = Module.finrank K A

-- section Schemes
variable {k : Type u} [Field k] [IsSepClosed k]

-- [PROVED] **(T-B6d)** A finite étale scheme over the spectrum of a separably closed field has exactly `finrank` many sections.
theorem natCard_sections_eq_finrank {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsFinite f] [Etale f] (x₀ : ↑(Spec (CommRingCat.of k))) :
    Nat.card { s : Spec (CommRingCat.of k) ⟶ X // s ≫ f = 𝟙 (Spec (CommRingCat.of k)) }
      = f.finrank x₀

-- [DATA] `Spec L`-valued points of `Spec A` over `Spec k` are `k`-algebra homomorphisms `A →ₐ[k] L`.
noncomputable def specPointsEquivAlgHom (k A L : Type u) [CommRing k] [CommRing A]
    [CommRing L] [Algebra k A] [Algebra k L] :
    { h : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of A) //
        h ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) =
          Spec.map (CommRingCat.ofHom (algebraMap k L)) } ≃ (A →ₐ[k] L) where
```
(4 public declarations)

## ModularCurves/ForMathlib/FiniteAbelianRankTwo.lean  (434 lines)
A finite abelian group killed by `N` whose `d`-torsion has exactly `d ^ 2` elements for every divisor `d` of `N` is isomorphic to `(Fin 2 → ZMod N)` — the pure group-theory half of Silverman III.6.4(b)/KM 2.3.5.

```lean
namespace ModularCurves

-- [PROVED] **Torsion-count characterisation of `(ℤ/N)²`** (pure group theory; T-B6e). A group killed by `N ≠ 0` whose `d`-torsion has exactly `d ^ 2` elements for every divisor `d` of `N` is isomorphic to `(Fin 2 → ZMod N)`.
theorem addEquiv_pi_fin_two_zmod_of_natCard (N : ℕ) (hN : N ≠ 0) (H : Type u)
    [AddCommGroup H] (hkill : ∀ x : H, N • x = 0)
    (hcount : ∀ d : ℕ, 0 < d → d ∣ N → Nat.card {x : H // d • x = 0} = d ^ 2) :
    Nonempty (H ≃+ (Fin 2 → ZMod N))
```
(1 public declaration; all helpers are `private`)

## ModularCurves/ForMathlib/FiniteEtaleFiberFunctor.lean  (707 lines)
The fiber functor `CommAlgCat.FiniteEtale.fiber k (SeparableClosure k)` is a Galois fiber functor: each `PreGaloisCategory.FiberFunctor` axiom is reduced to an exactness property of the base change functor `baseChange k Ω`, proved here.

```lean
namespace ModularCurves.FiniteEtaleGalois
variable (k : Type u) [Field k] (Ω : Type u) [Field Ω] [Algebra k Ω]

-- [DATA] The base change functor with both algebra universes pinned to `u`.
noncomputable abbrev baseChangeU :
    CommAlgCat.FiniteEtale.{u} k ⥤ CommAlgCat.FiniteEtale.{u} Ω

-- [DATA] `Ω ⊗[k] k` is the initial finite étale `Ω`-algebra.
noncomputable def baseChangeInitialIso :
    (baseChangeU k Ω).obj (CommAlgCat.FiniteEtale.of k k) ≅
      CommAlgCat.FiniteEtale.of Ω Ω

-- [DATA] `FiniteEtale.of k k` is initial.
noncomputable def isInitialOfSelf : IsInitial (CommAlgCat.FiniteEtale.of k k)

-- [PROVED]
lemma preservesInitial_baseChange :
    PreservesColimit (Functor.empty.{0} (CommAlgCat.FiniteEtale.{u} k))
      (baseChangeU k Ω)

-- [PROVED]
lemma preservesColimitsOfShapePEmpty_baseChange :
    PreservesColimitsOfShape (Discrete PEmpty.{1}) (baseChangeU k Ω)

-- section Products: variable {k Ω}

-- [PROVED] Evaluating a base-changed product at a coordinate is the `piRight` coordinate.
lemma map_eval_eq_piRight_apply {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : ι → CommAlgCat.FiniteEtale.{u} k) (i : ι) (x : Ω ⊗[k] (Π j, A j)) :
    Algebra.TensorProduct.map (AlgHom.id Ω Ω)
        (Pi.evalAlgHom k (fun j => (A j : Type u)) i) x =
      Algebra.TensorProduct.piRight k Ω Ω (fun j => (A j : Type u)) x i

-- [PROVED] Two maps into a base-changed product agreeing on all coordinate projections are equal.
lemma baseChangePi_hom_ext {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : ι → CommAlgCat.FiniteEtale.{u} k) {W : CommAlgCat.FiniteEtale.{u} Ω}
    {u v : W ⟶ (baseChangeU k Ω).obj (CommAlgCat.FiniteEtale.of k (Π j, A j))}
    (h : ∀ i, u ≫ (baseChangeU k Ω).map ((productFan A).π.app ⟨i⟩) =
      v ≫ (baseChangeU k Ω).map ((productFan A).π.app ⟨i⟩)) : u = v

-- [DATA] The base change of the product fan is a limit fan: `Ω ⊗[k] ∏ᵢ Aᵢ` is the product of the `Ω ⊗[k] Aᵢ`, via `piRight`.
noncomputable def isLimitMapConeProductFan {ι : Type} [Finite ι]
    (A : ι → CommAlgCat.FiniteEtale.{u} k) :
    IsLimit ((baseChangeU k Ω).mapCone (productFan A))

-- [PROVED]
lemma preservesLimitsOfShapeDiscrete_baseChange (ι : Type) [Finite ι] :
    PreservesLimitsOfShape (Discrete ι) (baseChangeU k Ω) where

-- section Pushouts: variable {k Ω}, variable {X Y Z : CommAlgCat.FiniteEtale.{u} k} (f : X ⟶ Y) (g : X ⟶ Z)

-- [DATA] The base change of the tensor-product pushout cocone is a colimit cocone.
noncomputable def isColimitMapCoconeSpanPushout :
    IsColimit ((baseChangeU k Ω).mapCocone (spanPushoutCocone f g))

-- [PROVED]
lemma preservesColimitsOfShapeWalkingSpan_baseChange :
    PreservesColimitsOfShape WalkingSpan (baseChangeU k Ω) where

-- section Monos: variable {k Ω}

-- [PROVED] Monomorphisms of finite étale algebras over a field are injective.
theorem injective_of_mono {A B : CommAlgCat.FiniteEtale.{u} k} (j : A ⟶ B) [Mono j] :
    Function.Injective j.hom.hom

-- [PROVED] Base change preserves monomorphisms of finite étale algebras.
lemma preservesMonomorphisms_baseChange :
    (baseChangeU k Ω).PreservesMonomorphisms where

-- section ReflectsIso: variable {k}

-- [PROVED] Hom-sets into the separable closure are finite.
lemma finite_algHom_sepClosure (W : Type u) [CommRing W] [Algebra k W]
    [Module.Finite k W] [Algebra.Etale k W] :
    Finite (W →ₐ[k] SeparableClosure k)

-- [PROVED] The fiber functor of `FiniteEtale k` at the separable closure reflects isomorphisms.
lemma reflectsIsomorphisms_fiber :
    (CommAlgCat.FiniteEtale.fiber k (SeparableClosure k) :
      (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ ⥤ FintypeCat.{u}).ReflectsIsomorphisms

-- section FixedPointsBaseChange: variable {k Ω}, variable {H : Type u} [Monoid H] [Finite H] (F : SingleObj H ⥤ CommAlgCat.FiniteEtale.{u} k)

-- [DATA] The base change of the fixed-point cone is a limit cone.
noncomputable def isLimitMapConeFixedPoints :
    IsLimit ((baseChangeU k Ω).mapCone (actionFixedPointsCone F))

-- [PROVED]
lemma preservesLimitsOfShapeSingleObj_baseChange (H : Type u) [Monoid H] [Finite H] :
    PreservesLimitsOfShape (SingleObj H) (baseChangeU k Ω) where

-- section Assembly

-- [DATA] The factorisation of the fiber functor through base change to the separable closure, with universes pinned.
noncomputable def fiberFactorization :
    (CommAlgCat.FiniteEtale.fiber k (SeparableClosure k) :
      (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ ⥤ FintypeCat.{u}) ≅
    (baseChangeU k (SeparableClosure k)).op ⋙
      CommAlgCat.FiniteEtale.fiber (SeparableClosure k) (SeparableClosure k)

-- [DATA] The fiber functor at the separable closure is a Galois fiber functor.
noncomputable instance : PreGaloisCategory.FiberFunctor
    (CommAlgCat.FiniteEtale.fiber k (SeparableClosure k) :
      (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ ⥤ FintypeCat.{u}) where
```
(19 public declarations)

## ModularCurves/ForMathlib/FiniteEtaleFundamentalGroup.lean  (410 lines)
The absolute Galois group `Gal(k^sep/k)` with its Krull topology is a fundamental group for the fiber functor of `(FiniteEtale k)ᵒᵖ` at the separable closure, yielding the Galois correspondence with finite discrete continuous `Gal`-sets.

```lean
namespace ModularCurves.FiniteEtaleGalois
variable (k : Type u) [Field k]

-- [DATA]
instance (priority := high) isSepClosure_sepClosure :
    IsSepClosure k (SeparableClosure k)

-- [DATA]
instance (priority := high) isGalois_sepClosure :
    IsGalois k (SeparableClosure k)

-- [DATA]
instance (priority := high) normal_sepClosure :
    Normal k (SeparableClosure k)

-- [DATA]
instance (priority := high) isSepClosed_sepClosure :
    IsSepClosed (SeparableClosure k)

-- [DATA]
instance (priority := high) isSeparable_sepClosure :
    Algebra.IsSeparable k (SeparableClosure k)

-- [DATA]
instance (priority := high) compactSpace_galSepClosure :
    CompactSpace (SeparableClosure k ≃ₐ[k] SeparableClosure k)

-- section Action: variable {k}, variable (Ω : Type u) [Field Ω] [Algebra k Ω]

-- [DATA] The Galois group of the geometric point acts on the fibers by post-composition.
noncomputable instance fiberMulAction (X : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ) :
    MulAction (Ω ≃ₐ[k] Ω) ((CommAlgCat.FiniteEtale.fiber k Ω).obj X) where

-- [PROVED]
lemma fiber_smul_def (X : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ) (σ : Ω ≃ₐ[k] Ω)
    (x : (CommAlgCat.FiniteEtale.fiber k Ω).obj X) :
    σ • x = σ.toAlgHom.comp x

-- [DATA]
instance : PreGaloisCategory.IsNaturalSMul
    (CommAlgCat.FiniteEtale.fiber k Ω) (Ω ≃ₐ[k] Ω) where

-- section Connected: variable {k}

-- [PROVED] The carrier of a connected object of `(FiniteEtale k)ᵒᵖ` is nontrivial.
theorem nontrivial_of_isConnected (X : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ)
    [PreGaloisCategory.IsConnected X] : Nontrivial (X.unop : Type u)

-- [PROVED] Connected finite étale algebras over a field are fields.
theorem isField_of_isConnected (X : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ)
    [PreGaloisCategory.IsConnected X] : IsField (X.unop : Type u)

-- section FundamentalGroup: variable {k}

-- [PROVED] The Galois group acts transitively on the points of a connected finite étale algebra: any two embeddings into the separable closure are conjugate.
theorem exists_smul_eq_of_isConnected (X : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ)
    [PreGaloisCategory.IsConnected X]
    (x y : (CommAlgCat.FiniteEtale.fiber k (SeparableClosure k)).obj X) :
    ∃ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k, σ • x = y

-- [PROVED] The stabiliser of a point is the fixing subgroup of a finite-dimensional intermediate field, hence open.
theorem stabilizer_isOpen (X : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ)
    (x : (CommAlgCat.FiniteEtale.fiber k (SeparableClosure k)).obj X) :
    IsOpen {σ : SeparableClosure k ≃ₐ[k] SeparableClosure k | σ • x = x}

-- [PROVED] An automorphism of the separable closure acting trivially on all fibers is the identity.
theorem eq_one_of_smul_eq (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k)
    (h : ∀ (X : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ)
      (x : (CommAlgCat.FiniteEtale.fiber k (SeparableClosure k)).obj X), σ • x = x) :
    σ = 1

-- [DATA]
instance : GaloisCategory (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ where

-- [DATA] The absolute Galois group of `k` is a fundamental group for the fiber functor of `(FiniteEtale k)ᵒᵖ` at the separable closure.
noncomputable instance isFundamentalGroup_galSepClosure :
    PreGaloisCategory.IsFundamentalGroup
    (CommAlgCat.FiniteEtale.fiber k (SeparableClosure k) :
      (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ ⥤ FintypeCat.{u})
    (SeparableClosure k ≃ₐ[k] SeparableClosure k) where

-- section Correspondence: variable {k}

-- [DATA] The comparison isomorphism of a fundamental group with `Aut F`, bundled as a continuous multiplicative equivalence.
open PreGaloisCategory in
noncomputable def toAutContinuousMulEquiv {C : Type*} [Category C] [GaloisCategory C]
    (F : C ⥤ FintypeCat.{u}) [FiberFunctor F] (G : Type*) [Group G]
    [∀ X, MulAction G (F.obj X)] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [IsFundamentalGroup F G] : G ≃ₜ* Aut F

-- [DATA] **The Galois correspondence for finite étale algebras**: the opposite of the category of finite étale `k`-algebras is equivalent to the category of finite discrete sets with continuous action of the absolute Galois group `Gal(k^sep/k)`.
noncomputable def finiteEtaleEquivContAction :
    (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ ≌
      ContAction FintypeCat.{u} (SeparableClosure k ≃ₐ[k] SeparableClosure k)

-- [DATA] The fiber of the finite étale algebra corresponding to a continuous Galois set recovers the set: the counit of the Galois correspondence, at the level of underlying finite sets.
noncomputable def pointsEquivOfContAction
    (X : ContAction FintypeCat.{u} (SeparableClosure k ≃ₐ[k] SeparableClosure k)) :
    ((CommAlgCat.FiniteEtale.fiber k (SeparableClosure k)).obj
      ((finiteEtaleEquivContAction k).inverse.obj X) : Type u) ≃ (X.obj.V : Type u)

-- [PROVED] The counit points-equivalence is Galois-equivariant: the fiber action (by post-composition) corresponds to the action of the continuous Galois set.
lemma pointsEquivOfContAction_smul
    (X : ContAction FintypeCat.{u} (SeparableClosure k ≃ₐ[k] SeparableClosure k))
    (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k)
    (x : ((CommAlgCat.FiniteEtale.fiber k (SeparableClosure k)).obj
      ((finiteEtaleEquivContAction k).inverse.obj X) : Type u)) :
    pointsEquivOfContAction k X (σ • x) =
      (show X.obj.V ⟶ X.obj.V from X.obj.ρ σ) (pointsEquivOfContAction k X x)
```
(20 public declarations)

## ModularCurves/ForMathlib/FiniteEtaleGalois.lean  (765 lines)
Builds `PreGaloisCategory ((CommAlgCat.FiniteEtale k)ᵒᵖ)` leaf by leaf: ambient (co)limit instances for `CommAlgCat k`, finite products, tensor-product pushouts, fixed-point limits, étale subalgebras/quotients, epi = surjective, the direct-summand axiom, and the tensor product as binary coproduct.

```lean
namespace ModularCurves.CommAlgCatLimits
variable (k : Type u) [Field k]

-- [DATA]
instance hasFiniteLimits : HasFiniteLimits (CommAlgCat.{u} k) where

-- [DATA]
instance hasFiniteColimits : HasFiniteColimits (CommAlgCat.{u} k) where

-- [DATA]
instance hasColimitsOfShapeSingleObjCommRingCat (G : Type u) [Group G] :
    HasColimitsOfShape (SingleObj G) CommRingCat.{u}

-- [DATA]
instance hasColimitsOfShapeSingleObjUnder (G : Type u) [Group G] :
    HasColimitsOfShape (SingleObj G) (Under (CommRingCat.of k))

-- [DATA]
instance hasColimitsOfShapeSingleObj (G : Type u) [Group G] :
    HasColimitsOfShape (SingleObj G) (CommAlgCat.{u} k)

namespace ModularCurves.FiniteEtaleGalois  -- (second namespace of the file)
variable (k : Type u) [Field k]

-- [DATA]
instance subsingletonHomFromSelf (A : CommAlgCat.FiniteEtale.{u} k) :
    Subsingleton (CommAlgCat.FiniteEtale.of k k ⟶ A)

-- [DATA]
instance nonemptyHomFromSelf (A : CommAlgCat.FiniteEtale.{u} k) :
    Nonempty (CommAlgCat.FiniteEtale.of k k ⟶ A)

-- [DATA]
instance hasInitial : HasInitial (CommAlgCat.FiniteEtale.{u} k)

-- variable {k}

-- [DATA] The product fan on a finite family of finite étale algebras, with pointwise-product vertex.
noncomputable def productFan {ι : Type} [Finite ι] (A : ι → CommAlgCat.FiniteEtale.{u} k) :
    Fan A

-- [DATA] The product fan is a limit fan.
noncomputable def productFanIsLimit {ι : Type} [Finite ι]
    (A : ι → CommAlgCat.FiniteEtale.{u} k) : IsLimit (productFan A)

-- [DATA]
instance hasFiniteProducts : HasFiniteProducts (CommAlgCat.FiniteEtale.{u} k) where

-- section Pushout: variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
--   [Algebra k A] [Algebra k B] [Algebra k C]
--   [Algebra A B] [Algebra A C] [IsScalarTower k A B] [IsScalarTower k A C]

-- [PROVED] The tensor product of finite étale `k`-algebras over a finite étale `k`-algebra is étale over `k` (uses the two-out-of-three property for étale maps).
theorem etale_tensorProduct [Algebra.Etale k A] [Algebra.Etale k B] [Algebra.Etale k C] :
    Algebra.Etale k (B ⊗[A] C)

-- [PROVED] The tensor product of finite `k`-algebras over a `k`-algebra is finite over `k`.
theorem finite_tensorProduct [Module.Finite k B] [Module.Finite k C] :
    Module.Finite k (B ⊗[A] C)

-- section PushoutCat: variable {X Y Z : CommAlgCat.FiniteEtale.{u} k} (f : X ⟶ Y) (g : X ⟶ Z)

-- [DATA] The pushout cocone on a span of finite étale `k`-algebras, with the tensor product as vertex (the `X`-algebra structures on `Y` and `Z` come from the span legs).
noncomputable def spanPushoutCocone : PushoutCocone f g

-- [DATA] The tensor-product cocone is a colimit cocone: `FiniteEtale k` has pushouts.
noncomputable def spanPushoutCoconeIsColimit : IsColimit (spanPushoutCocone f g)

-- [DATA]
instance hasPushouts : HasPushouts (CommAlgCat.FiniteEtale.{u} k) where

-- section EtaleSubalgebra: variable {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]

-- [PROVED] Every element of a finite étale algebra over a field is separable.
theorem isSeparable_of_etale [Module.Finite k A] [Algebra.Etale k A] (x : A) :
    IsSeparable k x

-- [PROVED] A finite reduced algebra over a field all of whose elements are separable is étale.
theorem etale_of_isSeparable (B : Type u) [CommRing B] [Algebra k B] [Module.Finite k B]
    [IsReduced B] (hsep : ∀ x : B, IsSeparable k x) : Algebra.Etale k B

-- [PROVED] A subalgebra of a finite étale algebra over a field is étale.
theorem etale_subalgebra [Module.Finite k A] [Algebra.Etale k A] (B : Subalgebra k A) :
    Algebra.Etale k B

-- [PROVED] Every quotient of a finite étale algebra over a field is étale.
theorem etale_quotient [Module.Finite k A] [Algebra.Etale k A] (J : Ideal A) :
    Algebra.Etale k (A ⧸ J)

-- section FixedPoints: variable {k : Type u} [Field k] {H : Type u} [Monoid H]
--   (F : SingleObj H ⥤ CommAlgCat.FiniteEtale.{u} k)

-- [DATA] The fixed points of a monoid action (by `k`-algebra endomorphisms) on a finite étale algebra, as a subalgebra.
def actionFixedPoints : Subalgebra k (F.obj (SingleObj.star H)).obj where

-- [DATA] The fixed-point cone on an `H`-action.
noncomputable def actionFixedPointsCone : Cone F where

-- [DATA] The fixed-point cone is a limit cone.
noncomputable def actionFixedPointsConeIsLimit : IsLimit (actionFixedPointsCone F) where

-- [DATA]
instance hasLimitsOfShapeSingleObj :
    HasLimitsOfShape (SingleObj H) (CommAlgCat.FiniteEtale.{u} k) where

-- section EpiSurjective: variable {k : Type u} [Field k]

-- [PROVED] A finite étale algebra over `k` has exactly `finrank` many homomorphisms into the separable closure of `k`.
theorem natCard_algHom_sepClosure (A : Type u) [CommRing A] [Algebra k A]
    [Module.Finite k A] [Algebra.Etale k A] :
    Nat.card (A →ₐ[k] SeparableClosure k) = Module.finrank k A

-- [PROVED] Epimorphisms in the category of finite étale algebras over a field are surjective.
theorem surjective_of_epi {X Y : CommAlgCat.FiniteEtale.{u} k} (π : Y ⟶ X) [Epi π] :
    Function.Surjective π.hom.hom

-- section EpiSplitting: variable {k : Type u} [Field k]

-- [PROVED] Chinese remainder splitting along an epimorphism of finite étale algebras: the source is the binary product of the target and the quotient by a complement of the kernel.
theorem monoInducesIsoOnDirectSummand_op {X Y : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ}
    (i : X ⟶ Y) [Mono i] : ∃ (Z : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ) (u : Z ⟶ Y),
    Nonempty (IsColimit (BinaryCofan.mk i u))

-- section PreGalois: variable {k : Type u} [Field k]

-- [DATA] The opposite of the one-object category of a monoid is the one-object category of the opposite monoid.
def singleObjOpEquiv (M : Type*) [Monoid M] : SingleObj Mᵐᵒᵖ ≌ (SingleObj M)ᵒᵖ where

-- [DATA]
instance hasQuotientsByFiniteGroupsOp (G : Type u) [Group G] [Finite G] :
    HasColimitsOfShape (SingleObj G) (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ

-- [DATA] The opposite of the category of finite étale algebras over a field is a PreGalois category in the sense of SGA1/Lenstra: axioms (G1)–(G3) hold.
instance : PreGaloisCategory (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ where

-- section TensorCoproduct: variable {k : Type u} [Field k], variable (A B : CommAlgCat.FiniteEtale.{u} k)

-- [DATA]
instance : Algebra.Etale k ((A : Type u) ⊗[k] (B : Type u))

-- [DATA]
instance : Module.Finite k ((A : Type u) ⊗[k] (B : Type u))

-- [DATA] The tensor product of two finite étale algebras, as an object.
noncomputable def tensorObj : CommAlgCat.FiniteEtale.{u} k

-- [DATA] The coproduct cofan on the tensor product.
noncomputable def tensorBinaryCofan : BinaryCofan A B

-- [DATA] The tensor product is the binary coproduct of finite étale algebras.
noncomputable def tensorBinaryCofanIsColimit :
    IsColimit (tensorBinaryCofan A B)

-- [DATA] The op of the tensor cofan is a binary product fan in `(FiniteEtale k)ᵒᵖ`.
noncomputable def tensorBinaryFanOpIsLimit :
    IsLimit ((tensorBinaryCofan A B).op)
```
(36 public declarations: 5 in `CommAlgCatLimits`, 31 in `FiniteEtaleGalois`)

## ModularCurves/ForMathlib/FinitePresentationCancel.lean  (56 lines)
Cancellation for `LocallyOfFinitePresentation`: if `f ≫ g` is locally of finite presentation and `g` is locally of finite type, then `f` is locally of finite presentation (Stacks 01TX).

```lean
namespace AlgebraicGeometry

-- [PROVED]
theorem LocallyOfFinitePresentation.of_comp_of_locallyOfFiniteType
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (h : LocallyOfFinitePresentation (f ≫ g)) (hg : LocallyOfFiniteType g) :
    LocallyOfFinitePresentation f
```
(1 public declaration)

## ModularCurves/ForMathlib/FinrankExact.lean  (85 lines)
Rank additivity in short exact sequences `0 → M → N → P → 0`: splitting when `P` is projective, `finrank` additivity for finite free outer terms, and `rankAtStalk` additivity for finite flat outer terms.

```lean
-- section Split
variable {R : Type u} {M : Type v} {N : Type w} {P : Type x} [Semiring R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module R M] [Module R N] [Module R P]
  {f : M →ₗ[R] N} {g : N →ₗ[R] P}

-- [PROVED] A short exact sequence `0 → M → N → P → 0` with `P` projective splits: `N ≅ M × P`.
theorem Function.Exact.nonempty_linearEquiv_prod_of_projective [Module.Projective R P]
    (h : Function.Exact f g) (hf : Function.Injective f) (hg : Function.Surjective g) :
    Nonempty (N ≃ₗ[R] M × P)

-- [PROVED] Rank additivity in a short exact sequence `0 → M → N → P → 0` of modules with `M` and `P` finite free.
theorem Module.finrank_eq_add_of_exact [StrongRankCondition R] [Module.Free R M] [Module.Finite R M]
    [Module.Free R P] [Module.Finite R P] (h : Function.Exact f g) (hf : Function.Injective f)
    (hg : Function.Surjective g) : finrank R N = finrank R M + finrank R P

-- section RankAtStalk
variable {R : Type u} {M : Type v} {N : Type w} {P : Type x} [CommRing R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module R M] [Module R N] [Module R P]
  {f : M →ₗ[R] N} {g : N →ₗ[R] P}

-- [PROVED] Pointwise rank additivity in a short exact sequence `0 → M → N → P → 0` with the outer terms finite flat: `rank_p N = rank_p M + rank_p P` at every prime `p`.
attribute [local instance] free_of_flat_of_isLocalRing in
theorem Module.rankAtStalk_eq_add_of_exact [Module.Finite R M] [Module.Flat R M] [Module.Finite R P]
    [Module.Flat R P] (h : Function.Exact f g) (hf : Function.Injective f)
    (hg : Function.Surjective g) (p : PrimeSpectrum R) :
    rankAtStalk N p = rankAtStalk M p + rankAtStalk P p
```
(3 public declarations)

## ModularCurves/ForMathlib/FunctorMapZpow.lean  (26 lines)
A monoidal functor's action on morphisms into a group object preserves integer powers: `F.map (f ^ n) = (F.map f) ^ n`.

```lean
namespace CategoryTheory.Functor
variable {C D : Type*} [Category* C] [Category* D]
  [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal] {X G : C} [GrpObj G]

-- [PROVED] A monoidal functor's action on morphisms into a group object preserves integer powers.
open scoped _root_.CategoryTheory.Obj in
@[to_additive]
lemma map_zpow' (f : X ⟶ G) (n : ℤ) : F.map (f ^ n) = (F.map f) ^ n
```
(1 public declaration)

## ModularCurves/ForMathlib/GradedQuotient.lean  (243 lines)
The quotient of a graded algebra by a homogeneous ideal is graded: `quotientGrading I n := (𝒜 n).map mk` with its `GradedAlgebra` instance, the graded quotient hom, its irrelevant-ideal compatibility, and functoriality.

```lean
namespace HomogeneousIdeal
variable {ι R A : Type*} [DecidableEq ι] [AddCommMonoid ι] [CommRing R] [CommRing A]
  [Algebra R A] {𝒜 : ι → Submodule R A} [GradedAlgebra 𝒜] (I : HomogeneousIdeal 𝒜)

-- [DATA] The grading on `A ⧸ I` induced by a grading on `A` and a homogeneous ideal `I`: the `n`-th piece is the image of `𝒜 n`.
def quotientGrading (n : ι) : Submodule R (A ⧸ I.toIdeal)

-- [PROVED]
lemma mk_mem_quotientGrading {n : ι} {a : A} (ha : a ∈ 𝒜 n) :
    Ideal.Quotient.mk I.toIdeal a ∈ quotientGrading I n

-- [DATA]
instance : SetLike.GradedMonoid (quotientGrading I) where

-- [DATA]
instance : DirectSum.Decomposition (quotientGrading I) where

-- [DATA] The quotient of a graded algebra by a homogeneous ideal is a graded algebra.
instance quotientGradingGradedAlgebra : GradedAlgebra (quotientGrading I)

-- [PROVED] The decomposition of the class of a homogeneous element is the evident single component.
lemma decompose_quotientGrading_mk {n : ι} {a : A} (ha : a ∈ 𝒜 n) :
    DirectSum.decompose (quotientGrading I) (Ideal.Quotient.mk I.toIdeal a) =
      DirectSum.of _ n ⟨Ideal.Quotient.mk I.toIdeal a, mk_mem_quotientGrading I ha⟩

-- [DATA] The canonical ring homomorphism from `R` to the degree-zero part of the quotient grading.
def algebraMapGradeZero : R →+* quotientGrading I 0 where

-- [PROVED]
@[simp]
lemma coe_algebraMapGradeZero (r : R) :
    (algebraMapGradeZero I r : A ⧸ I.toIdeal) = algebraMap R (A ⧸ I.toIdeal) r

-- [DATA]
instance : IsScalarTower R (↥(quotientGrading I 0)) (A ⧸ I.toIdeal)

-- [DATA] The quotient map `A → A ⧸ I` as a graded ring homomorphism onto the quotient grading.
def quotientGradingHom : 𝒜 →+*ᵍ quotientGrading I where

-- [PROVED]
lemma quotientGradingHom_surjective :
    Function.Surjective (quotientGradingHom I)

-- [PROVED]
@[simp]
lemma quotientGradingHom_apply (a : A) :
    quotientGradingHom I a = Ideal.Quotient.mk I.toIdeal a

-- [PROVED] Componentwise description of the quotient decomposition on classes.
lemma decompose_quotientGrading_mk_apply (a : A) (n : ι) :
    (DirectSum.decompose (quotientGrading I) (Ideal.Quotient.mk I.toIdeal a) n :
        A ⧸ I.toIdeal) =
      Ideal.Quotient.mk I.toIdeal (DirectSum.decompose 𝒜 a n)

-- section Irrelevant: variable [PartialOrder ι] [CanonicallyOrderedAdd ι]

-- [PROVED] The irrelevant ideal of the quotient grading is contained in the image of the irrelevant ideal — the hypothesis of `Proj.map` for the quotient map.
lemma quotientGradingHom_irrelevant_le :
    HomogeneousIdeal.irrelevant (quotientGrading I) ≤
      HomogeneousIdeal.map (quotientGradingHom I) (HomogeneousIdeal.irrelevant 𝒜)

-- section Map: variable {τ B S : Type*} [CommRing S] [CommRing B] [Algebra S B]
--   {ℬ : ι → Submodule S B} [GradedAlgebra ℬ]

-- [DATA] Functoriality of the quotient grading: a graded ring homomorphism mapping `I` into `J` descends to a graded homomorphism of the quotient gradings.
def quotientGradingMap (φ : GradedRingHom 𝒜 ℬ) (I : HomogeneousIdeal 𝒜)
    (J : HomogeneousIdeal ℬ) (h : I.toIdeal ≤ J.toIdeal.comap φ.toRingHom) :
    GradedRingHom (quotientGrading I) (quotientGrading J) where

-- [PROVED]
@[simp]
lemma quotientGradingMap_mk (φ : GradedRingHom 𝒜 ℬ) (I : HomogeneousIdeal 𝒜)
    (J : HomogeneousIdeal ℬ) (h : I.toIdeal ≤ J.toIdeal.comap φ.toRingHom) (a : A) :
    quotientGradingMap φ I J h (Ideal.Quotient.mk I.toIdeal a) =
      Ideal.Quotient.mk J.toIdeal (φ a)
```
(16 public declarations)

## ModularCurves/ForMathlib/IdealSheafComapMul.lean  (269 lines)
The scheme-theoretic preimage of ideal sheaves is multiplicative: `(I * J).comap f = I.comap f * J.comap f`, packaged as a monoid homomorphism with a finite-product corollary.

```lean
namespace AlgebraicGeometry.Scheme.IdealSheafData
variable {X Y : Scheme.{u}}

-- [PROVED] Over affine schemes, the scheme-theoretic preimage of an ideal sheaf has top-value the extension of the top-value: `(I.comap f).ideal ⊤ = (I.ideal ⊤).map f.appTop`.
theorem comap_ideal_top_of_isAffine [IsAffine X] [IsAffine Y]
    (I : Y.IdealSheafData) (f : X ⟶ Y) (hX : IsAffineOpen (⊤ : X.Opens))
    (hY : IsAffineOpen (⊤ : Y.Opens)) :
    (I.comap f).ideal ⟨⊤, hX⟩ =
      (I.ideal ⟨⊤, hY⟩).map (f.appTop).hom

-- [PROVED] Over affine schemes, the scheme-theoretic preimage of ideal sheaves is multiplicative.
theorem comap_mul_of_isAffine [IsAffine X] [IsAffine Y]
    (I J : Y.IdealSheafData) (f : X ⟶ Y) :
    (I * J).comap f = I.comap f * J.comap f

-- [PROVED] The `⊤`-value of the double preimage along an affine `U ≤ f⁻¹V`, expressed through the restriction `f.resLE`.
theorem comap_comap_ι_ideal_top (K : Y.IdealSheafData) (f : X ⟶ Y)
    (U : X.affineOpens) (V : Y.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    haveI : IsAffine U.1.toScheme := U.2
    haveI : IsAffine V.1.toScheme := V.2
    ((K.comap f).comap U.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩ =
      ((K.comap V.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩).map
        ((f.resLE V.1 U.1 hUV).appTop).hom

-- [PROVED] **The scheme-theoretic preimage of ideal sheaves is multiplicative.** (Its docstring continues: "REMAINING WORK (T-D6a-i; affine case and the resLE ⊤-value formula are proven above): glue `comap_mul_of_isAffine` over a cover…" — the declaration nonetheless carries a full tactic proof, no sorry.)
theorem comap_mul (I J : Y.IdealSheafData) (f : X ⟶ Y) :
    (I * J).comap f = I.comap f * J.comap f

-- [DATA] Scheme-theoretic preimage as a monoid homomorphism on ideal sheaves.
noncomputable def comapMonoidHom (f : X ⟶ Y) :
    Y.IdealSheafData →* X.IdealSheafData where

-- [PROVED]
@[simp] lemma comapMonoidHom_apply (f : X ⟶ Y) (K : Y.IdealSheafData) :
    comapMonoidHom f K = K.comap f

-- [PROVED] The scheme-theoretic preimage of a finite product of ideal sheaves.
lemma comap_prod {ι : Type*} (s : Finset ι) (K : ι → Y.IdealSheafData) (f : X ⟶ Y) :
    (∏ i ∈ s, K i).comap f = ∏ i ∈ s, (K i).comap f
```
(7 public declarations)

## ModularCurves/ForMathlib/InvariantBaseChange.lean  (312 lines)
Base change for rings of invariants (KM A7): the `G`-action on `A ⊗[R] R'` through the left factor, the comparison map `Aᴳ ⊗[R] R' →ₐ (A ⊗[R] R')ᴳ`, and its bijectivity for flat `R'` or when `#G` is invertible in `R`.

```lean
variable {G : Type*} [Group G]
variable {R : Type u} {A : Type u} {R' : Type u}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [MulSemiringAction G A] [SMulCommClass G R A] [SMulCommClass R G A]
variable [CommRing R'] [Algebra R R']

namespace MulSemiringAction

-- [DATA] The action of `G` on a base change `A ⊗[R] R'` through the left factor, as a ring action (KM A7.1: "the group G acts R'-linearly on A ⊗_R R' [by g(a⊗r') = g(a)⊗r']").
instance : MulSemiringAction G (A ⊗[R] R') where

-- [PROVED]
omit [SMulCommClass G R A] in
theorem smul_tmul_baseChange (g : G) (a : A) (r : R') :
    g • (a ⊗ₜ[R] r) = (g • a) ⊗ₜ[R] r

-- [DATA]
instance : SMulCommClass G R (A ⊗[R] R') where

end MulSemiringAction

-- [DATA] **The base-change comparison map for rings of invariants** (KM A7.1: the natural homomorphism `A^G ⊗_R R' → (A ⊗_R R')^G` whose bijectivity is the statement `∗(A, G, R, R')`).
noncomputable def fixedPointsBaseChange :
    (FixedPoints.subalgebra R A G) ⊗[R] R' →ₐ[R]
      FixedPoints.subalgebra R (A ⊗[R] R') G

-- [PROVED]
@[simp]
theorem fixedPointsBaseChange_tmul (a : FixedPoints.subalgebra R A G) (r : R') :
    (fixedPointsBaseChange (G := G) (R := R) (A := A) (R' := R') (a ⊗ₜ[R] r) : A ⊗[R] R') =
      (a : A) ⊗ₜ[R] r

-- [PROVED] **∗(A, G, R, R') holds for flat R'** (KM A7.1.3 (1)): the comparison map is bijective when `R'` is flat over `R`.
theorem fixedPointsBaseChange_bijective_of_flat [Finite G] [Module.Flat R R'] :
    Function.Bijective
      (fixedPointsBaseChange (G := G) (R := R) (A := A) (R' := R'))

-- [PROVED] **∗(A, G, R, R') holds when `#G` is invertible in `R`** (KM A7.1.3 (4)): the comparison map is bijective — via the divided trace `T = (1/#G)·Σ_g g`, which exhibits `A^G` as a direct `R`-module factor of `A`.
theorem fixedPointsBaseChange_bijective_of_isUnit [Finite G]
    (h : IsUnit ((Nat.card G : ℕ) : R)) :
    Function.Bijective
      (fixedPointsBaseChange (G := G) (R := R) (A := A) (R' := R'))
```
(7 public declarations)

## ModularCurves/ForMathlib/InvariantLocalization.lean  (213 lines)
A group action on a ring descends to the localization away from an invariant element: the `awayHom` endomorphisms and bundled action, plus "invariants of the localization = localization of the invariants" (surjectivity and injectivity halves).

```lean
variable {G : Type*} [Group G] {B : Type u} [CommRing B] [MulSemiringAction G B]
variable {h : B}

namespace MulSemiringAction

-- [PROVED]
theorem powers_le_comap_toRingHom (hfix : ∀ g : G, g • h = h) (g : G) :
    Submonoid.powers h ≤ (Submonoid.powers h).comap (toRingHom G B g)

-- [DATA] The ring endomorphism of `Localization.Away h` induced by localizing `g • ·` at the invariant element `h`.
noncomputable def awayHom (hfix : ∀ g : G, g • h = h) (g : G) :
    Localization.Away h →+* Localization.Away h

-- [PROVED]
theorem awayHom_algebraMap (hfix : ∀ g : G, g • h = h) (g : G) (b : B) :
    awayHom hfix g (algebraMap B (Localization.Away h) b) =
      algebraMap B (Localization.Away h) (g • b)

-- [PROVED]
theorem awayHom_mk' (hfix : ∀ g : G, g • h = h) (g : G) (b : B)
    (s : Submonoid.powers h) :
    awayHom hfix g (IsLocalization.mk' (Localization.Away h) b s) =
      IsLocalization.mk' (Localization.Away h) (g • b)
        (⟨g • (s : B), Submonoid.mem_comap.mp
          (powers_le_comap_toRingHom hfix g s.2)⟩ : Submonoid.powers h)

-- [PROVED] `awayHom` on a fraction with invariant denominator `hⁿ`: only the numerator moves.
theorem awayHom_mk'_pow (hfix : ∀ g : G, g • h = h) (g : G) (b : B) (n : ℕ) :
    awayHom hfix g (IsLocalization.mk' (Localization.Away h) b
        (⟨h ^ n, n, rfl⟩ : Submonoid.powers h)) =
      IsLocalization.mk' (Localization.Away h) (g • b)
        (⟨h ^ n, n, rfl⟩ : Submonoid.powers h)

-- [PROVED]
theorem awayHom_one (hfix : ∀ g : G, g • h = h) (x : Localization.Away h) :
    awayHom hfix (1 : G) x = x

-- [PROVED]
theorem awayHom_mul (hfix : ∀ g : G, g • h = h) (g g' : G) (x : Localization.Away h) :
    awayHom hfix (g * g') x = awayHom hfix g (awayHom hfix g' x)

-- [DATA] The action of `G` on `Localization.Away h` induced by localizing each `g • ·` at the invariant element `h`.
@[implicit_reducible]
noncomputable def away (hfix : ∀ g : G, g • h = h) :
    MulSemiringAction G (Localization.Away h) where

-- [PROVED] **Invariants of a localization are the localization of the invariants** (surjectivity half, T-Q3b): for a finite group and an invariant element `h`, every fixed element of `Localization.Away h` is `b / hⁿ` for an invariant numerator `b`.
theorem exists_fixed_mk'_eq_of_forall_awayHom_eq [Finite G]
    (hfix : ∀ g : G, g • h = h) (x : Localization.Away h)
    (hx : ∀ g : G, awayHom hfix g x = x) :
    ∃ (b : B) (n : ℕ), (∀ g : G, g • b = b) ∧
      IsLocalization.mk' (Localization.Away h) b
        (⟨h ^ n, n, rfl⟩ : Submonoid.powers h) = x

end MulSemiringAction

-- section FixedSubalgebra: variable (R : Type v) [CommRing R] [Algebra R B] [SMulCommClass G R B]

-- [PROVED]
theorem Submonoid.powers_le_comap_algebraMap (h : FixedPoints.subalgebra R B G) :
    Submonoid.powers h ≤ (Submonoid.powers (h : B)).comap
      (algebraMap (FixedPoints.subalgebra R B G) B)

-- [PROVED] The localization at `h` of the inclusion of the fixed subalgebra is injective (T-Q3c(i)).
theorem fixedPoints_awayMap_injective (h : FixedPoints.subalgebra R B G) :
    Function.Injective (IsLocalization.map (Localization.Away (h : B))
      (algebraMap (FixedPoints.subalgebra R B G) B)
      (Submonoid.powers_le_comap_algebraMap R h) :
        Localization.Away h →+* Localization.Away (h : B))

-- [PROVED] The range of the localized inclusion `(Bᴳ)_h → B_h` consists exactly of the fixed points of the localized action (T-Q3c(ii)).
theorem mem_range_fixedPoints_awayMap_iff [Finite G]
    (h : FixedPoints.subalgebra R B G) (x : Localization.Away (h : B)) :
    x ∈ Set.range (IsLocalization.map (Localization.Away (h : B))
        (algebraMap (FixedPoints.subalgebra R B G) B)
        (Submonoid.powers_le_comap_algebraMap R h) :
          Localization.Away h →+* Localization.Away (h : B)) ↔
      ∀ g : G, MulSemiringAction.awayHom (fun g => h.2 g) g x = x
```
(12 public declarations)

## ModularCurves/ForMathlib/InvariantTorsor.lean  (112 lines)
KM A7.1.1/A7.1.2 statements: the freeness predicate `IsFreeAlgebraAction`, the torsor-multiplication comparison `A ⊗[Aᴳ] A → (G → A)`, and the finite-étale-torsor plus base-change conclusions — the four main theorems are deliberate WIP `sorry`s per ticket T-Q2's statement-only scope.

```lean
variable (G : Type*) [Group G]
variable (R A : Type u)
variable [CommRing R] [CommRing A] [Algebra R A]
variable [MulSemiringAction G A] [SMulCommClass G R A] [SMulCommClass R G A]

-- [DATA] **KM A7.1.1's freeness condition**: `G` acts freely on the `R`-algebra `A` if for every nonzero `R`-algebra `R'` no `g ≠ 1` fixes an `R`-algebra point `A →ₐ[R] R'`.
def IsFreeAlgebraAction : Prop

-- namespace MulSemiringAction

-- [DATA] The torsor-multiplication comparison map `A ⊗[Aᴳ] A → (G → A)`, `x ⊗ y ↦ (x · (g • y))_g` (KM A7.1.1).
noncomputable def torsorMul :
    A ⊗[FixedPoints.subalgebra R A G] A →ₐ[FixedPoints.subalgebra R A G] (G → A)

-- [PROVED]
omit [SMulCommClass R G A] in
@[simp]
theorem torsorMul_tmul (x y : A) (g : G) :
    torsorMul G R A (x ⊗ₜ y) g = x * g • y

-- variable [Finite G]

-- [SORRY] **KM A7.1.1, finiteness part** (statement; proof: SGA III Exp. V Thm 4.1): for a free action, `A` is finite over the invariants.
theorem Module.Finite.of_isFreeAlgebraAction (hfree : IsFreeAlgebraAction G R A) :
    Module.Finite (FixedPoints.subalgebra R A G) A

-- [SORRY] **KM A7.1.1, étaleness part** (statement; proof: SGA III Exp. V Thm 4.1): for a free action, `A` is étale over the invariants.
theorem Algebra.Etale.of_isFreeAlgebraAction (hfree : IsFreeAlgebraAction G R A) :
    Algebra.Etale (FixedPoints.subalgebra R A G) A

-- [SORRY] **KM A7.1.1, torsor part** (statement): for a free action the multiplication comparison `A ⊗[Aᴳ] A ≅ ∏_G A` is bijective — `Spec A` is a `G`-torsor over `Spec Aᴳ`.
theorem torsorMul_bijective_of_isFreeAlgebraAction
    (hfree : IsFreeAlgebraAction G R A) :
    Function.Bijective (MulSemiringAction.torsorMul G R A)

-- [SORRY] **KM A7.1.2** (statement): free actions satisfy base change for rings of invariants — `∗(A, G, R, R')` for every `R'`.
theorem fixedPointsBaseChange_bijective_of_isFreeAlgebraAction
    (hfree : IsFreeAlgebraAction G R A)
    (R' : Type u) [CommRing R'] [Algebra R R'] :
    Function.Bijective
      (fixedPointsBaseChange (G := G) (R := R) (A := A) (R' := R'))
```
(7 public declarations; 4 [SORRY])

## ModularCurves/ForMathlib/NormBaseChange.lean  (74 lines)
For a finite free `R`-algebra `B`, the norm of `A ⊗[R] B` over `A` commutes with base change along a map `ψ : A →ₐ[R] A'` of coefficient algebras.

```lean
namespace ModularCurves
variable {R B A A' : Type*} [CommRing R] [CommRing B] [CommRing A] [CommRing A']
variable [Algebra R B] [Algebra R A] [Algebra R A']
variable [Module.Free R B] [Module.Finite R B]

-- [PROVED] The norm of a finite free extension commutes with base change along a map of coefficient algebras.
theorem norm_tensor_map (ψ : A →ₐ[R] A') (f : A ⊗[R] B) :
    Algebra.norm A' (Algebra.TensorProduct.map ψ (AlgHom.id R B) f) =
      ψ (Algebra.norm A f)
```
(1 public declaration)

## ModularCurves/ForMathlib/ProjClosedImmersion.lean  (243 lines)
`Proj` of a quotient grading is a closed subscheme of `Proj`: `Proj.map (quotientGradingHom I)` is a closed immersion, with the chartwise kernel computed as principal for `I = (F)`.

```lean
namespace HomogeneousIdeal
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] (I : HomogeneousIdeal 𝒜)

-- [PROVED]
theorem away_map_quotientGradingHom_surjective {d : ℕ} {s : A} (hs : s ∈ 𝒜 d) :
    Function.Surjective (Away.map (quotientGradingHom I) s)

-- [PROVED] **`Proj` of a quotient is a closed subscheme**: the morphism induced by the quotient map on a homogeneous ideal is a closed immersion.
set_option backward.isDefEq.respectTransparency false in
theorem isClosedImmersion_proj_map_quotientGradingHom :
    IsClosedImmersion (Proj.map (quotientGradingHom I)
      (quotientGradingHom_irrelevant_le I))

-- [PROVED] **The chartwise kernel is principal**: for `I = (F)` with `F` homogeneous of degree `d` and `s` homogeneous of degree `1`, the kernel of `(A_s)₀ → ((A/I)_s)₀` is generated by `F/sᵈ`.
theorem ker_away_map_quotientGradingHom {d : ℕ} {F : A} (hF : F ∈ 𝒜 d)
    (hI : I.toIdeal = Ideal.span {F}) {s : A} (hs : s ∈ 𝒜 1) :
    RingHom.ker (Away.map (quotientGradingHom I) s) =
      Ideal.span {HomogeneousLocalization.Away.mk 𝒜 hs d F (by simpa using hF)}
```
(3 public declarations)

## ModularCurves/ForMathlib/ProjectiveSpaceChart.lean  (396 lines)
The degree-zero homogeneous localization of `R[X_j : j ∈ σ]` away from a variable `X i` is a polynomial ring on the remaining variables (`(R[X]_{X i})₀ ≃+* R[u_j : j ≠ i]` by dehomogenisation), with naturality in the coefficient ring.

```lean
namespace HomogeneousLocalization
variable {ι R A : Type*} [AddCommMonoid ι] [DecidableEq ι] [CommRing R] [CommRing A]
  [Algebra R A] {𝒜 : ι → Submodule R A} [GradedAlgebra 𝒜] (x : Submonoid A)

-- [DATA] `HomogeneousLocalization.val` as a ring homomorphism.
def valRingHom : HomogeneousLocalization 𝒜 x →+* Localization x where

-- [PROVED]
@[simp]
lemma valRingHom_apply (y : HomogeneousLocalization 𝒜 x) : valRingHom x y = y.val

namespace MvPolynomial  -- (second namespace of the file)
variable (R : Type*) {σ : Type*} [CommRing R] [DecidableEq σ]
-- attribute [local instance] MvPolynomial.gradedAlgebra

-- [PROVED]
omit [DecidableEq σ] in
lemma X_mem_homogeneousSubmodule_one (i : σ) :
    (X i : MvPolynomial σ R) ∈ homogeneousSubmodule σ R 1

-- [DATA] The dehomogenising evaluation `R[X] → R[u_j : j ≠ i]`, `X_i ↦ 1`, `X_j ↦ u_j`.
noncomputable def dehomogenizeAux (i : σ) :
    MvPolynomial σ R →+* MvPolynomial {j : σ // j ≠ i} R

-- [PROVED]
@[simp]
lemma dehomogenizeAux_C (i : σ) (r : R) : dehomogenizeAux R i (C r) = C r

-- [PROVED]
@[simp]
lemma dehomogenizeAux_X_self (i : σ) : dehomogenizeAux R i (X i) = 1

-- [PROVED]
@[simp]
lemma dehomogenizeAux_X_ne (i : σ) {j : σ} (h : j ≠ i) :
    dehomogenizeAux R i (X j) = X ⟨j, h⟩

-- [PROVED] Dehomogenisation commutes with coefficient maps.
lemma dehomogenizeAux_map {S : Type*} [CommRing S] (g : R →+* S) (i : σ)
    (p : MvPolynomial σ R) :
    dehomogenizeAux S i (MvPolynomial.map g p) =
      MvPolynomial.map g (dehomogenizeAux R i p)

-- [DATA] Dehomogenisation at the variable `X i`: the chart map `(R[X]_{X i})₀ → R[u_j : j ≠ i]`.
noncomputable def dehomogenizeAt (i : σ) :
    Away (homogeneousSubmodule σ R) (X i : MvPolynomial σ R) →+*
      MvPolynomial {j : σ // j ≠ i} R

-- [DATA] The constants `R` inside the chart ring `(R[X]_{X i})₀`.
noncomputable def awayConst (i : σ) (r : R) :
    Away (homogeneousSubmodule σ R) (X i : MvPolynomial σ R)

-- [PROVED]
omit [DecidableEq σ] in
lemma val_awayConst' (i : σ) (r : R) :
    (awayConst R i r).val =
      Localization.mk (C r) (⟨(X i : MvPolynomial σ R) ^ 0, 0, rfl⟩ :
        Submonoid.powers (X i : MvPolynomial σ R))

-- [PROVED]
omit [DecidableEq σ] in
@[simp]
lemma val_awayConst (i : σ) (r : R) :
    (awayConst R i r).val = Localization.mk (C r) 1

-- [DATA] The chart coordinate `X_j / X_i` in `(R[X]_{X i})₀`.
noncomputable def awayVar (i : σ) (j : {j : σ // j ≠ i}) :
    Away (homogeneousSubmodule σ R) (X i : MvPolynomial σ R)

-- [PROVED]
omit [DecidableEq σ] in
lemma val_awayVar' (i : σ) (j : {j : σ // j ≠ i}) :
    (awayVar R i j).val =
      Localization.mk (X j.1) (⟨(X i : MvPolynomial σ R) ^ 1, 1, rfl⟩ :
        Submonoid.powers (X i : MvPolynomial σ R))

-- [DATA] The constants, as a ring homomorphism into the chart ring.
noncomputable def awayConstHom (i : σ) :
    R →+* Away (homogeneousSubmodule σ R) (X i : MvPolynomial σ R) where

-- [DATA] Homogenisation into the chart at `X i`: `u_j ↦ X_j/X_i`.
noncomputable def homogenizeAt (i : σ) :
    MvPolynomial {j : σ // j ≠ i} R →+*
      Away (homogeneousSubmodule σ R) (X i : MvPolynomial σ R)

-- [PROVED] Homogenisation commutes with coefficient maps, through the graded `Away.map` and the transport along `map g (X i) = X i`.
set_option backward.isDefEq.respectTransparency false in
lemma homogenizeAt_map {S : Type*} [CommRing S] (g : R →+* S) (i : σ)
    (p : MvPolynomial {j : σ // j ≠ i} R) :
    homogenizeAt S i (MvPolynomial.map g p) =
      ModularCurves.awayCongr (𝒜 := homogeneousSubmodule σ S)
        (MvPolynomial.map_X g i)
        ((HomogeneousLocalization.Away.map
          (⟨MvPolynomial.map g, fun {n x} hx =>
            (mem_homogeneousSubmodule _ _).mpr
              (((mem_homogeneousSubmodule _ _).mp hx).map g)⟩ :
            GradedRingHom (homogeneousSubmodule σ R) (homogeneousSubmodule σ S))
          (X i)) (homogenizeAt R i p))

-- [PROVED] Dehomogenising after homogenising is the identity.
lemma dehomogenizeAt_comp_homogenizeAt (i : σ) :
    (dehomogenizeAt R i).comp (homogenizeAt R i) = RingHom.id _

-- [PROVED] `dehomogenizeAt` on the normal form `p / X_iⁿ`.
lemma dehomogenizeAt_mk (i : σ) {n : ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ homogeneousSubmodule σ R (n • 1)) :
    dehomogenizeAt R i
        (Away.mk _ (X_mem_homogeneousSubmodule_one R i) n p hp) =
      dehomogenizeAux R i p

-- [PROVED] Homogenising after dehomogenising is the identity on the chart ring.
lemma homogenizeAt_comp_dehomogenizeAt (i : σ) :
    (homogenizeAt R i).comp (dehomogenizeAt R i) = RingHom.id _

-- [DATA] **The chart of projective space at `X i`**: the degree-zero homogeneous localization away from `X i` is a polynomial ring on the remaining variables.
noncomputable def chartRingEquiv (i : σ) :
    Away (homogeneousSubmodule σ R) (X i : MvPolynomial σ R) ≃+*
      MvPolynomial {j : σ // j ≠ i} R

-- [PROVED] Homogenising the dehomogenisation of a degree-`n` homogeneous polynomial gives `p / X_iⁿ`.
lemma homogenizeAt_dehomogenizeAux (i : σ) {p : MvPolynomial σ R} {n : ℕ}
    (hmem : p ∈ homogeneousSubmodule σ R (n • 1)) :
    homogenizeAt R i (dehomogenizeAux R i p) =
      HomogeneousLocalization.Away.mk _ (X_mem_homogeneousSubmodule_one R i) n p hmem
```
(22 public declarations)

## ModularCurves/ForMathlib/ReducedSeparation.lean  (56 lines)
In a reduced commutative ring, elements vanishing (resp. agreeing) under every ring hom to a field are zero (resp. equal).

```lean
variable {A : Type u} [CommRing A] [IsReduced A]

-- [PROVED] In a reduced commutative ring, an element vanishing under every ring hom to a field is zero.
theorem IsReduced.eq_zero_of_forall_ringHom_field (a : A)
    (h : ∀ (K : Type u) [Field K] (φ : A →+* K), φ a = 0) : a = 0

-- [PROVED] In a reduced commutative ring, two elements agreeing under every ring hom to a field are equal.
theorem IsReduced.eq_of_forall_ringHom_field {a b : A}
    (h : ∀ (K : Type u) [Field K] (φ : A →+* K), φ a = φ b) : a = b
```
(2 public declarations)

## ModularCurves/ForMathlib/RepresentableAut.lean  (97 lines)
Natural endomorphisms of a representable presheaf transport monoidally to endomorphisms of the representing object, giving `Aut F →* Aut Y` — the Yoneda step of Katz–Mazur 4.7.

```lean
namespace CategoryTheory.Functor.RepresentableBy
variable {C : Type u₁} [Category.{v₁} C] {F : Cᵒᵖ ⥤ Type v} {Y : C}

-- [DATA] Transport a natural endomorphism of `F` to an endomorphism of a representing object: the image of the universal element under `η`, reflected through the representing bijection.
noncomputable def transportHom (r : F.RepresentableBy Y) (η : F ⟶ F) : Y ⟶ Y

-- [PROVED] The characterizing property of `transportHom`: postcomposition with the transported endomorphism realizes `η` under the representing bijections.
theorem homEquiv_comp_transportHom (r : F.RepresentableBy Y) (η : F ⟶ F)
    {X : C} (v : X ⟶ Y) :
    r.homEquiv (v ≫ r.transportHom η) = η.app (op X) (r.homEquiv v)

-- [PROVED]
@[simp]
theorem transportHom_id (r : F.RepresentableBy Y) :
    r.transportHom (𝟙 F) = 𝟙 Y

-- [PROVED]
theorem transportHom_comp (r : F.RepresentableBy Y) (η θ : F ⟶ F) :
    r.transportHom (η ≫ θ) = r.transportHom η ≫ r.transportHom θ

-- [DATA] **Automorphisms of a representable presheaf transport to automorphisms of the representing object**, as a group homomorphism.
noncomputable def autMulHom (r : F.RepresentableBy Y) : Aut F →* Aut Y where

-- [PROVED]
@[simp]
theorem autMulHom_apply_hom (r : F.RepresentableBy Y) (e : Aut F) :
    (r.autMulHom e).hom = r.transportHom e.hom
```
(6 public declarations)

## ModularCurves/ForMathlib/SchemeQuotient.lean  (1037 lines)
Group actions on schemes (`SchemeAction`), stable opens and the induced section-ring action, local quotients of stable affine opens with open-immersion transition maps, and the glued quotient `X/G` with its full universal property (T-Q5).

```lean
namespace AlgebraicGeometry
variable (G : Type*) [Group G]

-- [DATA] An action of a group `G` on a scheme `X`, as a family of endomorphisms with the covariant composition laws (each `hom g` is automatically an isomorphism, `SchemeAction.isIso_hom`). Fields:
structure SchemeAction (X : Scheme.{u}) where
  hom : G → (X ⟶ X)
  hom_one : hom 1 = 𝟙 X
  hom_mul : ∀ g h : G, hom (g * h) = hom g ≫ hom h

namespace SchemeAction
-- variable {G}

-- [DATA] The scheme action packaged from a group homomorphism into `Aut X`, taking `g` to `(ψ g).inv` (the inversion converts `Aut`'s reversed composition into the covariant `hom (g * h) = hom g ≫ hom h` convention).
def ofAut {X : Scheme.{u}} (ψ : G →* Aut X) : SchemeAction G X where

-- [PROVED]
@[simp]
theorem ofAut_hom {X : Scheme.{u}} (ψ : G →* Aut X) (g : G) :
    (ofAut ψ).hom g = (ψ g).inv

-- variable {X : Scheme.{u}} (σ : SchemeAction G X)

-- [DATA]
instance isIso_hom (g : G) : IsIso (σ.hom g)

-- [DATA] The tautological action on `Spec B` induced by a ring action (`specSMul`).
variable (G) in
noncomputable def spec (B : Type u) [CommRing B] [MulSemiringAction G B] :
    SchemeAction G (Spec (CommRingCat.of B)) where

-- [PROVED]
@[simp]
theorem spec_hom (B : Type u) [CommRing B] [MulSemiringAction G B] (g : G) :
    (spec G B).hom g = specSMul g

-- [DATA] A `G`-stable open of `X`: each `σ g` restricts to it.
def IsStableOpen (U : X.Opens) : Prop

-- [PROVED]
theorem IsStableOpen.le_preimage {σ : SchemeAction G X} {U : X.Opens}
    (hU : σ.IsStableOpen U) (g : G) : U ≤ (σ.hom g) ⁻¹ᵁ U

-- [DATA] The induced action on the sections over a `G`-stable open, through `Scheme.Hom.appLE` (no `eqToHom` transport).
@[implicit_reducible]
noncomputable def gammaMulSemiringAction {U : X.Opens} (hU : σ.IsStableOpen U) :
    MulSemiringAction G ↑Γ(X, U) where

-- [PROVED]
@[simp]
theorem gammaMulSemiringAction_smul_def {U : X.Opens} (hU : σ.IsStableOpen U)
    (g : G) (s : ↑Γ(X, U)) :
    (gammaMulSemiringAction σ hU).smul g s =
      ((σ.hom g).appLE U U (hU.le_preimage g)).hom s

-- [PROVED] **Stable-affine refinement** (T-Q5b): if the `σ`-orbit of a point lies in an affine open of a scheme with affine diagonal (e.g. any separated scheme), then the point has a `G`-stable affine open neighbourhood, namely `⨅ g, (σ.hom g) ⁻¹ᵁ U`.
theorem exists_isStableOpen_isAffineOpen [Finite G]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    {U : X.Opens} (hU : IsAffineOpen U)
    (x : X) (horbit : ∀ g : G, σ.hom g x ∈ U) :
    ∃ V : X.Opens, σ.IsStableOpen V ∧ IsAffineOpen V ∧ x ∈ V

-- [DATA] The local quotient of a `G`-stable affine open: `Spec (Γ(X, V)ᴳ)` (T-Q5c, local piece).
@[reducible]
noncomputable def localQuotient {V : X.Opens} (hV : σ.IsStableOpen V) : Scheme.{u}

-- [DATA] The local quotient map `V ⟶ Spec (Γ(X, V)ᴳ)` on a `G`-stable affine open: the affine identification followed by the invariants morphism of the section-ring action.
noncomputable def localQuotientπ {V : X.Opens} (hV : σ.IsStableOpen V)
    (hVa : IsAffineOpen V) : (V : Scheme.{u}) ⟶ σ.localQuotient hV

-- [PROVED] The affine identification intertwines the geometric action restricted to a stable affine open with the `Spec` of the section-ring action (the c3 bridge: `resLE`/`isoSpec` naturality).
@[reassoc]
theorem resLE_isoSpec_hom {V : X.Opens} (hV : σ.IsStableOpen V)
    (hVa : IsAffineOpen V) (g : G) :
    letI := σ.gammaMulSemiringAction hV
    (σ.hom g).resLE V V (hV.le_preimage g) ≫ hVa.isoSpec.hom =
      hVa.isoSpec.hom ≫ specSMul g

-- [PROVED] The local quotient map coequalizes the restricted action (T-Q5c, local invariance).
@[reassoc]
theorem resLE_localQuotientπ {V : X.Opens} (hV : σ.IsStableOpen V)
    (hVa : IsAffineOpen V) (g : G) :
    (σ.hom g).resLE V V (hV.le_preimage g) ≫ σ.localQuotientπ hV hVa =
      σ.localQuotientπ hV hVa

-- [PROVED] Inverse form of the intertwiner bridge.
@[reassoc]
theorem specSMul_isoSpec_inv {V : X.Opens} (hV : σ.IsStableOpen V)
    (hVa : IsAffineOpen V) (g : G) :
    letI := σ.gammaMulSemiringAction hV
    specSMul g ≫ hVa.isoSpec.inv =
      hVa.isoSpec.inv ≫ (σ.hom g).resLE V V (hV.le_preimage g)

-- [PROVED] The restricted action commutes with the inclusion of a smaller stable open.
@[reassoc]
theorem resLE_homOfLE {W V : X.Opens} (hW : σ.IsStableOpen W)
    (hV : σ.IsStableOpen V) (hWV : W ≤ V) (g : G) :
    (σ.hom g).resLE W W (hW.le_preimage g) ≫ X.homOfLE hWV =
      X.homOfLE hWV ≫ (σ.hom g).resLE V V (hV.le_preimage g)

-- variable [Finite G]

-- [DATA] The descended map between the local quotients of nested stable affine opens: the (unique) morphism under `invariantsπ` induced by the inclusion `W ≤ V`.
noncomputable def localQuotientMap {W V : X.Opens} (hW : σ.IsStableOpen W)
    (hWa : IsAffineOpen W) (hV : σ.IsStableOpen V) (hVa : IsAffineOpen V)
    (hWV : W ≤ V) : σ.localQuotient hW ⟶ σ.localQuotient hV

-- [PROVED] Defining property of `localQuotientMap`.
theorem invariantsπ_localQuotientMap {W V : X.Opens} (hW : σ.IsStableOpen W)
    (hWa : IsAffineOpen W) (hV : σ.IsStableOpen V) (hVa : IsAffineOpen V)
    (hWV : W ≤ V) :
    letI := σ.gammaMulSemiringAction hW
    invariantsπ G ↑Γ(X, W) ℤ ≫ σ.localQuotientMap hW hWa hV hVa hWV =
      hWa.isoSpec.inv ≫ X.homOfLE hWV ≫ σ.localQuotientπ hV hVa

-- [PROVED] The local quotient maps are compatible with the local quotient projections.
@[reassoc]
theorem localQuotientπ_localQuotientMap {W V : X.Opens} (hW : σ.IsStableOpen W)
    (hWa : IsAffineOpen W) (hV : σ.IsStableOpen V) (hVa : IsAffineOpen V)
    (hWV : W ≤ V) :
    σ.localQuotientπ hW hWa ≫ σ.localQuotientMap hW hWa hV hVa hWV =
      X.homOfLE hWV ≫ σ.localQuotientπ hV hVa

-- section OpenImmersion: variable {W V : X.Opens}

-- [DATA] **The local quotient maps are open immersions** (T-Q5 (α)): the descended map between the local quotients of nested stable affine opens is an isomorphism onto the saturated image open.
instance isOpenImmersion_localQuotientMap (hW : σ.IsStableOpen W)
    (hWa : IsAffineOpen W) (hV : σ.IsStableOpen V) (hVa : IsAffineOpen V)
    (hWV : W ≤ V) :
    IsOpenImmersion (σ.localQuotientMap hW hWa hV hVa hWV)

-- [PROVED] Intersections of stable opens are stable.
omit [Finite G] in
theorem IsStableOpen.inf {τ : SchemeAction G X} {U V : X.Opens}
    (hU : τ.IsStableOpen U) (hV : τ.IsStableOpen V) :
    τ.IsStableOpen (U ⊓ V)

-- [PROVED] The local quotient map at equal opens is the identity.
theorem localQuotientMap_self {W : X.Opens} (hW : σ.IsStableOpen W)
    (hWa : IsAffineOpen W) :
    σ.localQuotientMap hW hWa hW hWa le_rfl = 𝟙 _

-- [PROVED] The local quotient maps compose along inclusions.
@[reassoc]
theorem localQuotientMap_trans {W V U : X.Opens} (hW : σ.IsStableOpen W)
    (hWa : IsAffineOpen W) (hV : σ.IsStableOpen V) (hVa : IsAffineOpen V)
    (hU : σ.IsStableOpen U) (hUa : IsAffineOpen U) (hWV : W ≤ V) (hVU : V ≤ U) :
    σ.localQuotientMap hW hWa hV hVa hWV ≫ σ.localQuotientMap hV hVa hU hUa hVU =
      σ.localQuotientMap hW hWa hU hUa (hWV.trans hVU)

-- [PROVED] Local quotient maps along equal opens are isomorphisms.
theorem isIso_localQuotientMap_of_le_le {W V : X.Opens} (hW : σ.IsStableOpen W)
    (hWa : IsAffineOpen W) (hV : σ.IsStableOpen V) (hVa : IsAffineOpen V)
    (hWV : W ≤ V) (hVW : V ≤ W) :
    IsIso (σ.localQuotientMap hW hWa hV hVa hWV)

-- section Glue: variable [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
-- variable (V : X → X.Opens) (hVs : ∀ x, σ.IsStableOpen (V x)) (hVa : ∀ x, IsAffineOpen (V x))

-- [DATA] **The quotient of a scheme by a finite group action** (T-Q5d): the local quotients of a stable affine atlas, glued.
@[reducible]
noncomputable def quotient : Scheme.{u}

-- variable (hVmem : ∀ x : X, x ∈ V x)

-- [DATA] The quotient projection `X ⟶ X/G`, glued from the local quotient projections.
noncomputable def quotientπ : X ⟶ σ.quotient V hVs hVa

-- [PROVED] Defining property of the quotient projection on each chart.
theorem opensι_quotientπ (x : X) :
    (V x).ι ≫ σ.quotientπ V hVs hVa hVmem =
      σ.localQuotientπ (hVs x) (hVa x) ≫ (quotientGlueData σ V hVs hVa).ι x

-- [PROVED] **Invariance of the quotient projection** (T-Q5d contract, part 1): `σ.hom g ≫ quotientπ = quotientπ`.
theorem hom_quotientπ (g : G) :
    σ.hom g ≫ σ.quotientπ V hVs hVa hVmem = σ.quotientπ V hVs hVa hVmem

-- [PROVED] **Uniqueness of descent along the quotient projection** (T-Q5d contract, part 2).
theorem quotientπ_hom_ext {Y : Scheme.{u}} (h₁ h₂ : σ.quotient V hVs hVa ⟶ Y)
    (H : σ.quotientπ V hVs hVa hVmem ≫ h₁ = σ.quotientπ V hVs hVa hVmem ≫ h₂) :
    h₁ = h₂

-- [PROVED] **Existence of descent along the quotient projection** (T-Q5d contract, part 3).
theorem exists_quotientπ_lift {Y : Scheme.{u}} (F : X ⟶ Y)
    (hF : ∀ g : G, σ.hom g ≫ F = F) :
    ∃ q : σ.quotient V hVs hVa ⟶ Y, σ.quotientπ V hVs hVa hVmem ≫ q = F

-- [PROVED] **The universal property of the quotient** (T-Q5d contract, part 4): `quotientπ` is the categorical quotient of `X` by `G` — every invariant morphism factors uniquely through it.
theorem existsUnique_quotientπ_lift {Y : Scheme.{u}} (F : X ⟶ Y)
    (hF : ∀ g : G, σ.hom g ≫ F = F) :
    ∃! q : σ.quotient V hVs hVa ⟶ Y, σ.quotientπ V hVs hVa hVmem ≫ q = F
```
(32 public declarations)

## ModularCurves/ForMathlib/SheafDisjointUnion.lean  (73 lines)
For a sheaf (valued in a suitable concrete category) and a pairwise disjoint family of opens with `U i ≤ V ≤ ⨆ i, U i`, restriction of sections is a bijection `F(V) ≃ Π i, F(U i)`.

```lean
namespace TopCat.Sheaf
variable {C : Type*} [Category* C] {FC : C → C → Type*} {CC : C → Type*}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
variable [Limits.HasLimitsOfSize.{x, x} C]
variable [(CategoryTheory.forget C).ReflectsIsomorphisms]
variable [Limits.PreservesLimitsOfSize.{x, x} (CategoryTheory.forget C)]
variable {X : TopCat.{x}} (F : Sheaf C X)

-- [PROVED] Sections of a sheaf over the empty open form a subsingleton.
theorem subsingleton_toType_obj_bot : Subsingleton (ToType (F.1.obj (op (⊥ : Opens X))))

-- [PROVED] For a pairwise disjoint family of opens `U : ι → Opens X` and an open `V` with `U i ≤ V ≤ ⨆ i, U i`, restriction of sections is a bijection `F(V) ≃ Π i, F(U i)`.
open scoped Function in
theorem bijective_restrict_pi_of_pairwise_disjoint {ι : Type*} (U : ι → Opens X)
    (V : Opens X) (hle : ∀ i, U i ≤ V) (hcover : V ≤ ⨆ i, U i)
    (hdisj : Pairwise (Disjoint on U)) :
    Function.Bijective fun (s : ToType (F.1.obj (op V))) (i : ι) ↦
      F.1.map (homOfLE (hle i)).op s
```
(2 public declarations)

## ModularCurves/ForMathlib/SpecGroupAction.lean  (148 lines)
The induced `G`-action `specSMul` on `Spec B` and the invariants morphism `invariantsπ : Spec B ⟶ Spec Bᴳ`: invariant under the action, integral, surjective, with fibres exactly the `G`-orbits.

```lean
namespace AlgebraicGeometry
variable (G : Type*) [Group G]
variable {B : Type u} [CommRing B] [MulSemiringAction G B]
-- section SpecSMul: variable {G}

-- [DATA] The automorphism of `Spec B` induced by the action of `g : G` on `B`.
noncomputable def specSMul (g : G) :
    Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of B)

-- [PROVED]
@[simp]
theorem specSMul_one : specSMul (1 : G) (B := B) = 𝟙 _

-- [PROVED]
theorem specSMul_mul (g h : G) :
    specSMul (g * h) (B := B) = specSMul g ≫ specSMul h

-- [DATA]
instance (g : G) : IsIso (specSMul (B := B) g)

-- [PROVED]
theorem specSMul_apply (g : G) (p : Spec (CommRingCat.of B)) :
    specSMul g p = PrimeSpectrum.comap (MulSemiringAction.toRingHom G B g) p

-- [PROVED] The scheme-theoretic action and the pointwise action on prime ideals: `specSMul g` sends a prime `p` to `g⁻¹ • p`.
theorem specSMul_apply_asIdeal (g : G) (p : Spec (CommRingCat.of B)) :
    (specSMul g p).asIdeal = g⁻¹ • p.asIdeal

-- variable (R : Type v) [CommRing R] [Algebra R B] [SMulCommClass G R B]
-- variable (B)

-- [DATA] Every fixed point of `B` lies in the fixed subalgebra — the tautological `Algebra.IsInvariant` instance for the honest invariants.
instance : Algebra.IsInvariant (FixedPoints.subalgebra R B G) B G

-- [DATA] The invariants morphism `Spec B ⟶ Spec (Bᴳ)`: the affine orbit map of the `G`-action, induced by the inclusion of the fixed subalgebra.
noncomputable def invariantsπ :
    Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G))

-- [PROVED] The invariants morphism coequalizes the `G`-action.
@[reassoc (attr := simp)]
theorem specSMul_invariantsπ (g : G) :
    specSMul g ≫ invariantsπ G B R = invariantsπ G B R

-- [DATA] For a finite group, the invariants morphism is integral (in particular affine and universally closed).
instance invariantsπ_isIntegralHom [Finite G] : IsIntegralHom (invariantsπ G B R)

-- [PROVED] For a finite group, the invariants morphism is surjective: every prime of the fixed subalgebra lies under a prime of `B`.
theorem invariantsπ_surjective [Finite G] :
    Function.Surjective (invariantsπ G B R).base

-- [PROVED] The fibres of the invariants morphism are exactly the `G`-orbits: two primes of `B` lie over the same prime of `Bᴳ` iff they differ by the action of some `g : G`.
theorem invariantsπ_apply_eq_iff [Finite G] (x y : Spec (CommRingCat.of B)) :
    invariantsπ G B R x = invariantsπ G B R y ↔ ∃ g : G, specSMul g x = y
```
(12 public declarations)

## ModularCurves/ForMathlib/StandardSmoothHypersurface.lean  (324 lines)
The hypersurface `R[Xⱼ]/(f)` localized away from a partial derivative `∂f/∂Xᵢ` is standard smooth over `R` of relative dimension `#σ − 1`, via the model quotient `R[Option σ]/(f, X none·∂f − 1)`.

```lean
namespace ModularCurves
variable {R : Type*} [CommRing R] {σ : Type} [Fintype σ] [DecidableEq σ]
  (f : MvPolynomial σ R) (i : σ)

-- [DATA] The two relations of the localized hypersurface: `f` and `X none · ∂f/∂Xᵢ - 1`.
noncomputable def hypersurfaceRels : Fin 2 → MvPolynomial (Option σ) R

-- [DATA] The model quotient presenting the localized hypersurface.
noncomputable abbrev HypersurfaceModel : Type _

-- [DATA] The naive presentation of the model quotient, with section `(Xᵢ, w)`.
noncomputable def hypersurfacePresentation :
    Algebra.PreSubmersivePresentation R (HypersurfaceModel f i) (Option σ) (Fin 2)

-- [PROVED]
lemma pderiv_none_rename_some (p : MvPolynomial σ R) :
    pderiv (none : Option σ) (rename Option.some p) = 0

-- [PROVED]
lemma hypersurfacePresentation_jacobian_isUnit :
    IsUnit (hypersurfacePresentation f i).jacobian

-- [DATA] The submersive presentation of the model quotient.
noncomputable def hypersurfaceSubmersivePresentation :
    Algebra.SubmersivePresentation R (HypersurfaceModel f i) (Option σ) (Fin 2) where

-- [PROVED]
lemma hypersurfaceModel_isStandardSmoothOfRelativeDimension :
    Algebra.IsStandardSmoothOfRelativeDimension (Fintype.card σ - 1) R
      (HypersurfaceModel f i)

-- section AwayEquiv

-- [DATA] The model quotient `R[Option σ]/(f, X none·∂f - 1)` is the hypersurface localized away from `∂f/∂Xᵢ`.
noncomputable def hypersurfaceAwayEquiv :
    HypersurfaceModel f i ≃ₐ[R] Localization.Away
      (Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f))

-- [PROVED] **Localized hypersurfaces are standard smooth** of relative dimension `#σ - 1`: inverting a partial derivative of `f` on `R[Xⱼ]/(f)` yields a standard smooth `R`-algebra.
theorem isStandardSmoothOfRelativeDimension_away_pderiv :
    Algebra.IsStandardSmoothOfRelativeDimension (Fintype.card σ - 1) R
      (Localization.Away (Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f)))
```
(9 public declarations)

## ModularCurves/ForMathlib/TateNormalForm.lean  (350 lines)
VENDORED from mathlib4 PR #25218 (Kenny Lau): the Tate normal form `y² + (1−c)xy − by = x³ − bx²` of a Weierstrass curve with a point `P` satisfying `P, 2P, 3P ≠ 0` (as unit conditions over any `CommRing`), plus project additions — uniqueness of the normalising variable change and the `Ψ₃` division-polynomial bridge.

```lean
namespace WeierstrassCurve

namespace Affine.Point
variable {R : Type*} [CommRing R] {W : WeierstrassCurve R} (P : W.toAffine.Point)

-- [DATA] Typeclass for a given point not being zero (the point at infinity). Fields:
@[mk_iff]
class NeZero : Prop where
  neZero : P ≠ 0

-- [DATA] The `X` coordinate of a given point. For the point at infinity, this returns `0` (junk value).
def X : W.toAffine.Point → R

-- [DATA] The `Y` coordinate of a given point. For the point at infinity, this returns `0` (junk value).
def Y : W.toAffine.Point → R

-- [PROVED]
variable (W) in
@[simp] lemma not_neZero_zero : ¬(NeZero (0 : W.toAffine.Point))

-- [PROVED]
lemma equation_X_Y [NeZero P] : W.toAffine.Equation P.X P.Y

-- [PROVED]
lemma equation_X_Y' [NeZero P] : P.Y^2 + W.a₁ * P.X * P.Y + W.a₃ * P.Y
    = P.X^3 + W.a₂ * P.X^2 + W.a₄ * P.X + W.a₆

-- [DATA] The partial derivative `∂W/∂X` of the Weierstrass cubic at a given point `P`.
def pX : R

-- [DATA] The partial derivative `∂W/∂Y` of the Weierstrass cubic at a given point `P`.
def pY : R

-- [DATA] The condition `2 • P ≠ 0` on all fibres. Fields:
@[mk_iff]
class TwiceNeZero : Prop extends P.NeZero where
  twiceNeZero : IsUnit P.pY

-- [PROVED]
lemma isUnit_pY [P.TwiceNeZero] : IsUnit P.pY

-- [PROVED]
lemma pY_ne_zero [P.TwiceNeZero] [Nontrivial R] : P.pY ≠ 0

-- [DATA] The inverse of `pY` as a unit, whenever `2 • P ≠ 0` (i.e. `P.TwiceNeZero`).
def pY_inv [P.TwiceNeZero] : Rˣ

-- [PROVED]
@[simp] lemma pY_mul_inv [P.TwiceNeZero] : P.pY * P.pY_inv = 1

-- [PROVED]
@[simp] lemma pY_inv_mul [P.TwiceNeZero] : (P.pY_inv : R) * P.pY = 1

-- [PROVED]
@[simp] lemma pY_inv_inv [P.TwiceNeZero] : P.pY_inv⁻¹ = P.pY

-- [DATA] A quantity that determines whether `3 • P = 0`.
def μ [P.TwiceNeZero] : R

-- [DATA] The condition `3 • P ≠ 0` on all fibres. Fields:
@[mk_iff]
class ThriceNeZero : Prop extends P.NeZero where
  thriceNeZero : IsUnit ((W.a₂ + 3 * P.X) * P.pY ^ 2 + P.pX * W.a₁ * P.pY - P.pX ^ 2)

-- [PROVED]
lemma thriceNeZero_isUnit [P.ThriceNeZero] :
    IsUnit ((W.a₂ + 3 * P.X) * P.pY ^ 2 + P.pX * W.a₁ * P.pY - P.pX ^ 2)

-- [PROVED]
lemma isUnit_μ [P.TwiceNeZero] [P.ThriceNeZero] : IsUnit P.μ

-- [DATA] The inverse of `μ` as a unit, whenever `3 • P ≠ 0` (i.e. `P.ThriceNeZero`).
def μ_inv [P.TwiceNeZero] [P.ThriceNeZero] : Rˣ

-- [PROVED]
@[simp] lemma μ_mul_inv [P.TwiceNeZero] [P.ThriceNeZero] : P.μ * P.μ_inv = 1

-- [PROVED]
@[simp] lemma μ_inv_mul [P.TwiceNeZero] [P.ThriceNeZero] : (P.μ_inv : R) * P.μ = 1

-- [PROVED]
@[simp] lemma μ_inv_inv [P.TwiceNeZero] [P.ThriceNeZero] : P.μ_inv⁻¹ = P.μ

end Affine.Point

namespace Affine
variable {R : Type*} [CommRing R] (W : Affine R) (P : W.toAffine.Point)

-- [DATA] Whenever a point is not zero, we can transform the Weierstrass cubic to move the point to the origin `(0, 0)`, which eliminates the `a₆` coefficient.
def ofNeZero : VariableChange R where

-- [PROVED]
@[simp] lemma ofNeZero_a₆ [P.NeZero] : (W.ofNeZero P • W).a₆ = 0

-- [PROVED]
@[simp] lemma ofNeZero_a₄ : (W.ofNeZero P • W).a₄ = -P.pX

-- [PROVED]
@[simp] lemma ofNeZero_a₃ : (W.ofNeZero P • W).a₃ = P.pY

-- [PROVED]
@[simp] lemma ofNeZero_a₂ : (W.ofNeZero P • W).a₂ = W.a₂ + 3 * P.X

-- [PROVED]
@[simp] lemma ofNeZero_a₁ : (W.ofNeZero P • W).a₁ = W.a₁

-- [DATA] The intermediate step used in `ofTwiceNeZero`.
def ofTwiceNeZero_aux [P.TwiceNeZero] : VariableChange R where

-- [DATA] Whenever a point `P` satisfies `2 • P ≠ 0`, we can transform the Weierstrass cubic to move the point to the origin `(0, 0)`, and also transform the tangent line at `(0, 0)` to be horizontal.
def ofTwiceNeZero [P.TwiceNeZero] : VariableChange R where

-- [PROVED]
lemma ofTwiceNeZero_eq [P.TwiceNeZero] : W.ofTwiceNeZero P =
    W.ofTwiceNeZero_aux P * W.ofNeZero P

-- [PROVED]
@[simp] lemma ofTwiceNeZero_a₆ [P.TwiceNeZero] : (W.ofTwiceNeZero P • W).a₆ = 0

-- [PROVED]
@[simp] lemma ofTwiceNeZero_a₄ [P.TwiceNeZero] : (W.ofTwiceNeZero P • W).a₄ = 0

-- [PROVED]
@[simp] lemma ofTwiceNeZero_a₃ [P.TwiceNeZero] : (W.ofTwiceNeZero P • W).a₃ = P.pY

-- [PROVED]
@[simp] lemma ofTwiceNeZero_a₂ [P.TwiceNeZero] : (W.ofTwiceNeZero P • W).a₂ = P.μ

-- [DATA] The intermediate step used in `toTateNF`.
def toTateNF_aux [P.TwiceNeZero] [P.ThriceNeZero] : VariableChange R where

-- [DATA] Whenever a point `P` satisfies `3 • P ≠ 0`, we can transform the Weierstrass cubic to move the point to the origin `(0, 0)`, and also transform the tangent line at `(0, 0)` to be horizontal, and also make the x-intercept and y-intercept the same.
def toTateNF [P.TwiceNeZero] [P.ThriceNeZero] : VariableChange R where

-- [PROVED]
lemma toTateNF_eq [P.TwiceNeZero] [P.ThriceNeZero] : W.toTateNF P =
    W.toTateNF_aux P * W.ofTwiceNeZero P

-- [PROVED]
lemma toTateNF_a₆ [P.TwiceNeZero] [P.ThriceNeZero] : (W.toTateNF P • W).a₆ = 0

-- [PROVED]
lemma toTateNF_a₄ [P.TwiceNeZero] [P.ThriceNeZero] : (W.toTateNF P • W).a₄ = 0

-- [PROVED]
lemma toTateNF_a₂₃ [P.TwiceNeZero] [P.ThriceNeZero] :
    (W.toTateNF P • W).a₂ = (W.toTateNF P • W).a₃

end Affine

-- ## Project additions (NOT in PR #25218 — AINTLIB, upstream candidates)

namespace Affine.Point  -- (reopened)
variable {R : Type*} [CommRing R] {W : WeierstrassCurve R} (P : W.toAffine.Point)

-- [PROVED]
@[simp] lemma X_some {x y : R} (h : W.toAffine.Nonsingular x y) :
    (Affine.Point.some x y h).X = x

-- [PROVED]
@[simp] lemma Y_some {x y : R} (h : W.toAffine.Nonsingular x y) :
    (Affine.Point.some x y h).Y = y

-- [PROVED] On the curve, the `ThriceNeZero` quantity is the value of the `3`-division polynomial: `(a₂ + 3X)·pY² + pX·a₁·pY − pX² = Ψ₃.eval X`.
lemma Ψ₃_eval_X [P.NeZero] :
    W.Ψ₃.eval P.X
      = (W.a₂ + 3 * P.X) * P.pY ^ 2 + P.pX * W.a₁ * P.pY - P.pX ^ 2

-- [PROVED] Bridge: a point on the curve with `IsUnit (ψ₂-value)` satisfies `TwiceNeZero`.
lemma twiceNeZero_of_isUnit [P.NeZero] (h : IsUnit (W.ψ₂.evalEval P.X P.Y)) :
    P.TwiceNeZero where

-- [PROVED] Bridge: a point on the curve with `IsUnit (Ψ₃-value)` satisfies `ThriceNeZero`.
lemma thriceNeZero_of_isUnit [P.NeZero] (h : IsUnit (W.Ψ₃.eval P.X)) :
    P.ThriceNeZero where

end Affine.Point

namespace Affine  -- (reopened)
variable {R : Type*} [CommRing R] (W : Affine R) (P : W.toAffine.Point)

-- [PROVED]
@[simp] lemma toTateNF_r [P.TwiceNeZero] [P.ThriceNeZero] : (W.toTateNF P).r = P.X

-- [PROVED]
@[simp] lemma toTateNF_t [P.TwiceNeZero] [P.ThriceNeZero] : (W.toTateNF P).t = P.Y

-- [PROVED] **Uniqueness of the Tate-normalising variable change** (the uniqueness half of Loeffler Prop 3.3.4; not in PR #25218): a variable change carrying `P` to `(0,0)` (`r = P.X`, `t = P.Y`) whose result has `a₄ = 0` and `a₂ = a₃` is `toTateNF`.
theorem toTateNF_unique [P.TwiceNeZero] [P.ThriceNeZero] (vc : VariableChange R)
    (hr : vc.r = P.X) (ht : vc.t = P.Y)
    (h₄ : (vc • W).a₄ = 0) (h₂₃ : (vc • W).a₂ = (vc • W).a₃) :
    vc = W.toTateNF P
```
(50 public declarations)

---

## Totals

| # | File | Lines | Public decls | PROVED | DATA | SORRY |
|---|------|-------|--------------|--------|------|-------|
| 1 | AffinePointVariableChange.lean | 415 | 38 | 31 | 7 | 0 |
| 2 | AffineQuotient.lean | 916 | 12 | 11 | 1 | 0 |
| 3 | AwayCongr.lean | 107 | 9 | 8 | 1 | 0 |
| 4 | BijectiveResidueField.lean | 135 | 3 | 3 | 0 | 0 |
| 5 | CharpolyNorm.lean | 58 | 1 | 1 | 0 | 0 |
| 6 | EtaleSectionsCount.lean | 184 | 4 | 2 | 2 | 0 |
| 7 | FiniteAbelianRankTwo.lean | 434 | 1 | 1 | 0 | 0 |
| 8 | FiniteEtaleFiberFunctor.lean | 707 | 19 | 11 | 8 | 0 |
| 9 | FiniteEtaleFundamentalGroup.lean | 410 | 20 | 7 | 13 | 0 |
| 10 | FiniteEtaleGalois.lean | 765 | 36 | 9 | 27 | 0 |
| 11 | FinitePresentationCancel.lean | 56 | 1 | 1 | 0 | 0 |
| 12 | FinrankExact.lean | 85 | 3 | 3 | 0 | 0 |
| 13 | FunctorMapZpow.lean | 26 | 1 | 1 | 0 | 0 |
| 14 | GradedQuotient.lean | 243 | 16 | 8 | 8 | 0 |
| 15 | IdealSheafComapMul.lean | 269 | 7 | 6 | 1 | 0 |
| 16 | InvariantBaseChange.lean | 312 | 7 | 4 | 3 | 0 |
| 17 | InvariantLocalization.lean | 213 | 12 | 10 | 2 | 0 |
| 18 | InvariantTorsor.lean | 112 | 7 | 1 | 2 | 4 |
| 19 | NormBaseChange.lean | 74 | 1 | 1 | 0 | 0 |
| 20 | ProjClosedImmersion.lean | 243 | 3 | 3 | 0 | 0 |
| 21 | ProjectiveSpaceChart.lean | 396 | 22 | 14 | 8 | 0 |
| 22 | ReducedSeparation.lean | 56 | 2 | 2 | 0 | 0 |
| 23 | RepresentableAut.lean | 97 | 6 | 4 | 2 | 0 |
| 24 | SchemeQuotient.lean | 1037 | 32 | 20 | 12 | 0 |
| 25 | SheafDisjointUnion.lean | 73 | 2 | 2 | 0 | 0 |
| 26 | SpecGroupAction.lean | 148 | 12 | 7 | 5 | 0 |
| 27 | StandardSmoothHypersurface.lean | 324 | 9 | 4 | 5 | 0 |
| 28 | TateNormalForm.lean | 350 | 50 | 35 | 15 | 0 |

**Total: 336 public top-level declarations** (210 [PROVED], 122 [DATA], 4 [SORRY], 0 [DATA-SORRY]).
The only sorries in the directory are the four KM A7.1.1/A7.1.2 statement-only theorems in `InvariantTorsor.lean` (`Module.Finite.of_isFreeAlgebraAction`, `Algebra.Etale.of_isFreeAlgebraAction`, `torsorMul_bijective_of_isFreeAlgebraAction`, `fixedPointsBaseChange_bijective_of_isFreeAlgebraAction`).
