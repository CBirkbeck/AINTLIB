# Decomposition — STREAM-E4: the KM 4.7.0 receipts under the level-4 B2 resolution

*2026-07-20. Board v10.342 (B2 adjudicated → level-4 rigidifier; b2_log `B2-DECISION`).
Source of record: Katz–Mazur, "Arithmetic Moduli of Elliptic Curves" (KM), scan at
`refs/ModularCurves/katz-mazur-arithmetic-moduli-FULL.pdf`, **pdf page = print page + 11**.
All quotes below transcribed verbatim from the scan this session.*

Status key: leaves are marked READY-mathlib / READY-project / API-GAP / ASSEMBLY.
The Lean skeleton for the new declarations is written by this pass (see §Skeleton).

---

## 0. Verbatim source-quote bank (KM)

### KM 2.2.2 (print p. 68) — ω as a nowhere-vanishing one-form
> "Zariski locally on S, we may choose an 𝒪_S-basis ω of ω_{E/S}; such an ω is nothing
> other than a nowhere-vanishing one-form on E/S, i.e., an isomorphism 𝒪 ≅ Ω¹_{E/S}.
> This ω is necessarily translation-invariant […]"

### KM 2.2.5 (print pp. 68–69) — the pole filtration and adapted x, y
> "For each integer n ≥ 1, the invertible sheaf I(0) has f_*(I^{-n}(0)) = locally free of
> rank n on S. Once we have chosen an 𝒪_S-basis ω of ω_{E/S} over an affine S = Spec(A),
> we have f_*(I^{-2}(0)) is free on 1, x with x uniquely determined up to x ↦ x + a by the
> normalization x ~ (1/T²)(1 + higher terms), […] and f_*(I^{-3}(0)) is free on 1, x, y
> with y uniquely determined up to y ↦ y + ax + b by the normalization
> y ~ (1/T³)(1 + higher terms). We say that such x, y are 'adapted to ω'."

### KM 2.2.5.1 (print p. 69) — the generalized Weierstrass equation
> "Therefore we obtain a generalized Weierstrass equation
> (2.2.5.1)  y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆,
> and indeed the affine ring H⁰(E − {0}; 𝒪) = lim_n H⁰(E, I^{-n}(E)) is none other than
> A[x,y]/(this Weierstrass equation)."

### KM print p. 70 — invertibility normalizations
> "When 2 is invertible in A, there is a unique choice of y adapted to ω such that
> a₁ = a₃ = 0. When 3 is invertible in A, there is a unique choice of x adapted to ω
> such that a₂ = 0."

### KM 2.2.8 (print pp. 70–71) — Case II (Legendre), the ± pinning
> "So the points of order two are the origin and the three points with y = 0. Let us
> specify two of these, say P₂, Q₂; x(P₂) = e₁, x(Q₂) = e₂. […] So we may eliminate the
> x ↦ x + a indeterminacy if we insist that x(P₂) = 0. We may normalize ω up to ± if we
> require that this x, already normalized by x(P₂) = 0, satisfy x(Q₂) = 1."

*(The "up to ±" is exactly the μ₂ that twists the Legendre torsor — the B2 wall.)*

### KM 2.2.9 (print p. 71) — the Legendre family
> "Then the Legendre family y² = x(x−1)(x−λ), ω = −dx/y over ℤ[1/2, λ][1/λ(λ−1)] is the
> universal (E, ω, P₂, Q₂) everywhere finite points of order two such that x(P₂) = 0,
> x(Q₂) = 1) over schemes where 2 is invertible."

### KM 2.2.10 (print pp. 71–72) — Case III (naive level three): the METHOD
> "Case III. (Naive level three) 3 invertible: again we pick a local on S basis ω of
> ω_{E/S}. Now x is unique, y free up to y ↦ y + ax + b, and the equation is
> y² + a₁xy + a₃y = x³ + a₄x + a₆. By Abel's theorem the points of order three are the
> nine flex points of this cubic. Suppose given a nowhere-trivial point of order 3, say
> P₃. Then locally over S there exists a function with a triple zero at P₃, and a triple
> pole at zero, so a linear combination of 1, x, y. So there is a unique such function of
> the form y + ax + b. Taking this to be y, we get an equation of the form
> y² + a₁xy + a₃y = x³. This cubic is smooth if and only if (a₁³ − 27a₃)a₃ is invertible."

> "Now suppose given a second nowhere-trivial point Q₃ of order three, which is disjoint
> from both P₃ = (0,0) and −P₃ = (0, −a₃). By Abel, Q₃ is the triple zero of a unique
> function of the form y − Ax − B. We claim that A is invertible. […] Because A is
> invertible, there is a unique choice of ω for which A = 1."

### KM 2.2.11 (print p. 73) — the ℰ₃ universal family (the pattern ℰ₄ mirrors)
> "(2.2.11) Thus a₁ = 3C − 1, a₃ = −3C² − B − 3BC, and the curve y² + a₁xy + a₃y = x³
> with marked points P₃ = (0,0), Q₃ = (C, B+C) over the ring
> ℤ[1/3, B, C][1/((a₁³−27a₃)a₃C)]/(B³ = (B+C)³) is the universal (E, non-trivial P₃,
> non-trivial Q₃ ≠ ±P₃) over a ℤ[1/3]-algebra."

### KM 4.6 (print p. 110) — the naive level-N problem is a GL₂-torsor
> "The basic example of a moduli problem 𝒫 étale over (Ell) is provided by the 'naive'
> level N moduli problem (N ≥ 1 arbitrary): E/S ↦ the set of S-group-scheme isomorphisms
> (ℤ/Nℤ)² ≅ E[N]. The corresponding S-scheme 𝒫_{E/S} is concentrated over S[1/N], over
> which it is a finite étale GL(2, ℤ/Nℤ)-torsor."

### KM 4.6.1 (print p. 110) — level 3 is representable (the bootstrap)
> "(4.6.1) We have already seen explicitly (2.2.11) that for N = 3 the naive level N
> moduli problem is representable, and its representing scheme is a smooth affine
> connected curve over ℤ[1/3]."

### KM 4.6.2 (print p. 111) — the Legendre example (REFUTED as a constant-group torsor)
> "(4.6.2) Another example of a moduli problem 𝒫 which is étale over (Ell) is the
> Legendre moduli problem 2.2.9: E/S ↦ pairs (φ₂, ω) consisting of an S-group-scheme
> isomorphism φ₂ : (ℤ/2ℤ)² ≅ E[2] together with an S-basis ω of ω_{E/S} for which the
> adapted x satisfies x(P₂) = 0, x(Q₂) = 1. The corresponding S-scheme 𝒫_{E/S} is
> concentrated over S[1/2], over which it is a finite étale GL(2, ℤ/2ℤ) × {±1} torsor."

*(Refutation on file: b2_log 2026-07-19 entry (functor level, machine-checked) +
B2-DECISION entry (scheme level: the six marking-components over the universal Legendre
base are pairwise non-isomorphic quadratic étale algebras — square classes
1, −1, λ, −λ, λ−1, 1−λ — so no constant group acts fibre-transitively; the honest group
is a twisted μ₂-extension of GL₂(𝔽₂).)*

### KM 4.7.0 + axioms (print pp. 111–112) — the Scholie and the two axioms
> "SCHOLIE (4.7.0). Let 𝒫 be relatively representable and affine over (Ell); then a
> necessary and sufficient condition that 𝒫 be representable is that 𝒫 be rigid."

> "Let N ≥ 1 be an integer, G a finite group, and δ a relatively representable and
> affine moduli problem on (Ell) which satisfies the following axioms:
> 1) δ is representable, by an affine ℤ[1/N]-scheme
> 2) G operates upon δ, in such a way that for every elliptic curve E/S with S a
>    ℤ[1/N]-scheme, the S-scheme δ_{E/S} is a finite étale G-torsor.
> We claim that over ℤ[1/N], 𝒫 is represented by the affine ℤ[1/N]-scheme 𝔐(𝒫,δ)/G.
> Once we have verified this claim, we simply apply it successively with
> (N = 2, δ = Legendre problem, G = GL(2,ℤ/2ℤ) × {±1}) and with (N = 3, δ = naive level
> three problem, G = GL(2,𝔽₃))."

*(STREAM-E4 replaces the first instantiation by (N = 2, δ = naive level FOUR problem,
G = GL(2, ℤ/4ℤ)) — a genuine instance of KM's own axioms by the 4.6 quote above, since
4 is invertible iff 2 is. The engine (`representable_of_rigidNoeth_of_torsor` +
recollement) is the proven Lean form of the claim's proof; only the two axiom inputs
change.)*

### KM 4.7.1 (print p. 116) — the recollement corollary
> "COROLLARY 4.7.1. Any relatively representable moduli problem 𝒫 which is affine and
> étale over (Ell), and rigid, is representable by a smooth affine curve over ℤ."

### KM 4.7.2 (print p. 117) — naive level N for N ≥ 3 (the receipts' shape)
> "COROLLARY 4.7.2. For N ≥ 3, the naive level N moduli problems of 4.6 is
> representable, by a smooth affine curve Y(N) over ℤ[1/N]. Proof. This results from
> 4.7.1 above, thanks to the rigidity 2.7.2 and the relative representability 3.7.1 of
> naive level N structures. Q.E.D."

### KM 3.7.1 (print p. 104) — relative representability at invertible N
> "THEOREM 3.7.1. Let N ≥ 1 be an integer, S a scheme on which N is invertible […] and
> E/S an elliptic curve. Consider the four functors on (Sch/S) given by T ↦ Γ(N)-
> structures on E_T/T […]. Each is represented by a finite étale S-scheme."

### KM 1.4.1 / 1.4.2 (print p. 17) — exact order N; killed by N (B3 boundary)
> "(1.4.1) […] We say that a point P ∈ C(S) has 'exact order N' if the effective Cartier
> divisor D := [P] + [2P] + ⋯ + [NP] in C/S of degree N is a subgroup of C/S."

> "LEMMA 1.4.2. If P ∈ C(S) has 'exact order N', then NP = 0. Proof. Any finite locally
> free commutative group-scheme of rank N is known to be killed by N (cf. [Oort-Tate]).
> Therefore every section, in particular P, of the effective Cartier divisor Σ₁^N [aP]
> is killed by N. Q.E.D."

*(B3 boundary: the cited fact is Deligne's order-kills theorem — [Oort–Tate 1970] §1,
Tate "Finite flat group schemes" §3.8, Stix's notes — independent of the O–T
classification. At INVERTIBLE N (the only regime any current receipt states), the fact
has the elementary étale/Lagrange proof via KM 1.4.4/3.7.2 and is NOT a wall.)*

### KM 1.4.4 (print p. 18) — invertible-N equivalences (the étale/Lagrange route)
> "LEMMA 1.4.4. Suppose that N is invertible on S. Let P ∈ C(S) be a point killed by N.
> Then the following conditions are equivalent. (1) P has 'exact order N' in C/S. (2)
> For every geometric point Spec(k) → S […] (3) […] the N points {aP_k}, a = 1,…,N are
> all distinct in C(k). (4) The effective Cartier divisor Σ [aP] in C/S is finite étale
> over S. (5) The unique S-group homomorphism ℤ/Nℤ → C which maps '1' to P defines a
> closed S-immersion ℤ/Nℤ ↪ C which identifies the constant S-scheme ℤ/Nℤ with the
> Cartier divisor Σ[aP]."

---

## 1. Streams and their trees

(§2–§7 filled by this pass after the code-mapping reports: E4-A the ℰ₄-machine,
E4-B the level-4 torsor package, E4-C the engine rewire + Legendre quarantine,
E4-D the mouth core, E4-E the recollement glue, E4-F the Drinfeld invertible-N cone.)

---

## 2. E4-A — the ℰ₄-machine (`naiveLevelFour_representable_by_affine`)

### Plain-English proof (KM 2.2.10–2.2.11's METHOD run at level 4; Loeffler Prop 3.3.4/Cor 3.3.5)

Let R be a ring with 2 invertible. A naive full level-4 structure on E/S is a pair of
sections (P,Q) with 4P = 4Q = 0 killing and fibrewise generation of E[4] ≅ (ℤ/4)²
(`IsNaiveFullLevel 4`, in-tree). Since P has exact order 4 fibrewise, P, 2P, 3P ≠ 0 in
every fibre, so the **full Tate normal form applies** (Loeffler 3.3.4; in-tree
`ForMathlib/TateNormalForm.lean` `toTateNF` + `toTateNF_unique`): unique coordinates with
P = (0,0), a₄ = a₆ = 0, a₂ = a₃ =: B. Order-4 of P then forces a₁ = 1: indeed
2P = (−B, 0) and −2P = (−B, a₁B − B), so 4P = 0 ⟺ B(a₁−1) = 0 ⟺ a₁ = 1 (B divides Δ,
so B is a unit). The curve is E(1,B): y² + xy + By = x³ + Bx², Δ = B⁴(1−16B)
(sympy-verified 2026-07-20; to be `ring`-certified in Lean).

Adjoin Q = (u,v). The condition "Q completes P to a basis" is fibrewise equivalent to:
Q on the curve, 2Q ∈ E[2] ∖ {0, 2P}. The 2-torsion abscissas split as
ψ₂²(x) = (x+B)(4x² + x + B) with x(2P) = −B the first factor. The locus {2Q = 2P} is
{x(Q) ∈ {0, −2B}} (sympy: gcd analysis; the four points P + E[2]). The **single cleared
relation** for "2Q lands on the other pair" is the u-quartic

    e4Rel(B,u) := 2u⁴ + u³ + 3Bu² + 4B²u + 2B³ = 0,

via the master identity (sympy-verified, mod the curve equation):

    ψ₂(Q)³ · ψ₂(2Q-coords) ≡ u·(2B+u)·e4Rel(B,u).

On the honest datum locus, u = x(Q)−x(P) and u+2B are units (their vanishing loci are
exactly {2Q = 2P}, fibrewise excluded), so "2Q is 2-torsion" (the LINEAR section
condition ψ₂ at 2Q — nilpotent-safe, no square roots) is equivalent to e4Rel = 0.
Conversely in the localized ring the constants e4Rel(B,0) = 2B³ and
e4Rel(B,−2B) = 2B³(16B−1) are units, so u and u+2B are automatically units, and
res_u(e4Rel, ψ₂²-abscissa-poly) = 8B⁸(16B−1)² makes ψ₂(Q) an automatic unit (2Q ≠ 0);
disc_u(e4Rel) = 4B⁶(16B−1)³ makes the quartic separable (étale, 4×2 = 8 fibre points =
|GL₂(ℤ/4)|/#{order-4 pts} = 96/12 ✓).

**The universal object:**
E4ModuliRing := R[B,u,v][1/(B(1−16B))] / (v²+uv+Bv−u³−Bu², e4Rel(B,u)), with universal
curve ⟨1, B, B, 0, 0⟩, P = (0,0), Q = (u,v). Killing: [4]P = 0 since 2P = (−B,0)
satisfies ψ₂ = 2y+x+B identically; [4]Q = 0 since e4Rel + units force 2Q onto the
2-torsion (the degenerate y-fibre over a root of 4x²+x+B is a single 2-torsion point).
Generation over every geometric point k̄ (char ≠ 2): E[4](k̄) ≅ (ℤ/4)²
(`torsion_geometricFibre_rank_two 4`, general-N, in-tree) and the pair (P̄,Q̄) with
ord P̄ = ord Q̄ = 4, 2Q̄ ∉ {0, 2P̄} generates — by the elementary case analysis
(`combos4_ne_zero`, NEW): for (a,b) ≢ (0,0) mod 4 with aP̄+bQ̄ = 0: (a,b odd,odd) ⟹
2P̄+2Q̄ = 0 ⟹ 2Q̄ = 2P̄ ✗; (odd,0) ⟹ P̄ = 0 ✗; (odd,2) ⟹ 2Q̄ = odd·P̄ order 4 ✗;
(0/2 cases symmetric); (2,2),(2,0),(0,2) ⟹ 2P̄+2Q̄=0 / 2P̄=0 / 2Q̄=0 ✗. Then
`pair_generates_iff_combos_ne_zero 4` (general-N, in-tree) concludes.

**Classifying map** (every naive Γ(4)-structure is an ℰ₄-datum): per base point take an
atlas chart; the marking pipeline (`E3DatumAssembly` marking layer, N-agnostic) puts P
at (0,0); `toTateNF` (+ `toTateNF_unique` for well-definedness/gluing) normalizes to
a₄ = a₆ = 0, a₂ = a₃; bridge-A (from the RING-DBL doubling identity at the 4-torsion
section P) yields B(a₁−1) = 0 with B a unit, so a₁ = 1; bridge-Q (the master identity +
unit certificates u, u+2B from fibrewise 2Q ≠ 2P) yields e4Rel(B, x(Q)-chart) = 0.
The chart tuple (B, u, v) glues (uniqueness of the Tate normal form ⟹ local witnesses
agree on overlaps ⟹ sheaf-glue, exactly the `e3GammaGlued` pattern), defining
E4ModuliRing → Γ(X.base) → the classifying EllHom; the two round-trips are the
`e3ClassifyingEllHom_pulled`/`pullSection_e3ClassifyingEllHom` pattern (N-agnostic
packaging, §5 of the ℰ₃ map).

### Lean skeleton targets (written by this pass; file `Moduli/UniversalLevelFour.lean`
unless noted; every leaf `:= by sorry`)

- **E4A-1** (defs; ASSEMBLY): `e4CurveRel`, `e4Rel` (MvPolynomial (Fin 3) R; X 0 = B,
  X 1 = u, X 2 = v), `E4Quotient`, `e4Delta` (:= B(1−16B) class), `E4ModuliRing`,
  `e4B/e4U/e4V`, `universalE4 := ⟨1, e4B, e4B, 0, 0⟩`, `universalE4Obj/P/Q`.
  Source: KM 2.2.11 pattern (§0 quote) + Loeffler Cor 3.3.5; certificates above.
- **E4A-2** (leaf): `universalE4_Δ : (universalE4 R).Δ = unit-normal form` +
  `IsElliptic` instance. Discharge: `ring` + `isUnit_of_mul_isUnit`-style, mirroring
  `universalE3_Δ` (UniversalLevelThree:86–120). Sympy cert: Δ = −B⁴(16B−1).
- **E4A-3** (leaves): unit lemmas `isUnit_e4B`, `isUnit_one_sub_16B`, `isUnit_e4U`,
  `isUnit_e4U_add_two_e4B`, `isUnit_psiTwo_e4Q` — from e4Rel(B,0) = 2B³,
  e4Rel(B,−2B) = 2B³(16B−1), res(e4,ψ₂²) = 8B⁸(16B−1)² (Bezout witnesses computed at
  ticket time by polyrith/linear_combination; sympy certs above).
- **E4A-4** (leaves): equation witnesses `universalE4_equation_zero/(Q)`, and
  `two_zsmul_universalE4P = section(−B,0)`-form + `psiTwo`-vanishing ⟹
  **`four_zsmul_universalE4P_of_isUnit : (4:ℤ) • universalE4P = 0`** and
  **`four_zsmul_universalE4Q_of_isUnit`**. Route: mirror the E3 Stage-D killing
  (reduced universal base ℤ[1/2]-version + `universalE4_section_killing` via
  `nsmul_section_eq_zero_of_forall_specPoint` + Stage-D transport along
  `zInvTwoHom` — the `zInvThreeHom` pattern at 879–976 of UniversalLevelThree).
- **E4A-5** (leaf, NEW group theory): **`combos4_ne_zero`** (file
  `ForMathlib/PairGeneratesOfCardSq.lean`, alongside `combos3_ne_zero`): for an ab.
  group point set with 4P = 4Q = 0, 2P ≠ 0, 2Q ≠ 0, 2Q ≠ 2P: all 15 nontrivial
  (ℤ/4)-combos aP + bQ ≠ 0. Proof: the 4-case analysis in the prose. Consumed with
  `pair_generates_iff_combos_ne_zero 4` + `torsion_geometricFibre_rank_two 4`.
- **E4A-6** (keystone): **`universalE4_generation`** — mirror of
  `universalE3_generation` (UniversalLevelThree:1001) with the Stage-B dictionary
  (N-agnostic) + E4A-5. Fibre facts: P̄ = (0,0) order 4 (2P̄ = (−B̄,0) ≠ 0 from B̄ ≠ 0);
  Q̄ order 4 (ψ₂(Q̄) ≠ 0 from E4A-3); 2Q̄ ≠ 2P̄ (x(2Q̄) root of 4x²+x+B̄,
  x(2P̄) = −B̄, common root ⟹ 4B̄² = 0 ✗).
- **E4A-7** (defs + leaf): `IsE4Form`, `IsE4Datum`, `IsE4Datum.map` — the E3 pattern
  (UniversalLevelThree:437/1410/1478) with (a₁=1 ∧ a₂=a₃=B ∧ a₄=a₆=0), marks P@(0,0),
  Q@(u,v), units {B, 1−16B, u, u+2B, ψ₂(u,v)}, relation e4Rel(B,u) = 0.
- **E4A-8** (bridge master; file `Moduli/E4Bridge.lean`): `hdbl4_of_marked_four_torsion`
  — the RING-DBL doubling identity at a marked 4-torsion section (mirror of
  `hdbl_of_marked_three_torsion`, BridgeAssembly:221, with `two_zsmul_affineSection` +
  `equation_dblXY` + `isUnit_tangentDen`-analogue; tangent-denominator unit = ψ₂(P)
  from P not-2-torsion fibrewise).
- **E4A-9** (leaf): **`bridgeA_holds`** — marked Tate-form chart + 4-torsion P ⟹
  B·(a₁ − 1) = 0, and with `isUnit_B_of_marked` ⟹ a₁ = 1.
- **E4A-10** (leaf): **`bridgeQ4_holds`** — marked chart in E(1,B)-form + 4-torsion Q +
  fibrewise 2Q ≠ 2P ⟹ e4Rel(B, p) = 0 (master identity + unit certs `isUnit_p`,
  `isUnit_p_add_twoB` via the `isUnit_x_of_marked_pair` pattern,
  E3DatumAssembly:569, from `pull`-disjointness of 2Q and 2P).
- **E4A-11** (assembly): **`isE4Datum_of_bridges`** — mirror of
  `isE3Datum_of_bridges` (E3DatumAssembly:413): atlas charts, marking pipeline
  (N-agnostic layer), `ofNeZero`/`toTateNF` normalization (TateNormalForm.lean —
  note: E3 could not use `toTateNF` (flex points fail `ThriceNeZero`), E4 CAN and
  should), bridge-A, bridge-Q4, unit certificates.
- **E4A-12** (classifying chain): `e4BaseMap/e4QuotientMap/e4ClassifyingRingHom/
  e4ClassifyingMap/e4Top/e4ClassifyingEllHom` + glued witnesses `e4BGlued/e4UGlued/
  e4VGlued` + `e4Delta_glued_isUnit` — the 1723–2542 pattern of UniversalLevelThree
  (chart-witness gluing via `toTateNF_unique`-agreement, `E4Witness` pullback-gluing).
- **E4A-13** (round-trips): `pullSection_e4ClassifyingEllHom_P/_Q`,
  `e4ClassifyingEllHom_pulled` — the 2616/2646/3015 pattern.
- **E4A-14** (glue): **`naiveLevelFourRepresentableBy`** +
  **`naiveLevelFour_representable_by_affine_of_conditions`** +
  (Bootstrap) **`naiveLevelFour_representable_by_affine (hR : IsUnit (2 : R))`** —
  verbatim the §5 N-agnostic packaging with `EllObj.isUnit_two/four` helper.

Sizing: source anchors — KM 2.2.10–11 is 2.5 print pages for level 3; the landed ℰ₃
Lean realization is ≈ 3113 + 800 + 550 lines. E4 saves the flex/quotient-ring dance
(polynomial ring, 2 honest relations; full `toTateNF` available; Stage-D killing
trivialized by explicit 2P) but adds the second relation bookkeeping; estimate
**≈ 2500–3500 lines total across UniversalLevelFour/E4Bridge**, multi-session.

### Attacks attempted (tree-level; per-leaf attack logs to be extended at ticket time)
- Counterexample/edge search: e4Rel roots vs excluded loci — checked symbolically:
  e4(0), e4(−2B) units (Q ∉ ⟨P⟩ automatic); res(e4, ψ₂²) unit (Q never 2-torsion);
  disc unit (separable). Degenerate B: B = 0 and 16B = 1 excluded by Δ-localization —
  matches Δ(E(1,B)) exactly; no hidden component (fibre count 8 = 96/12 ✓).
- Hypothesis-strength: `IsUnit (2:R)` is necessary (E[4] étale fails at char 2;
  KM 4.6: problem "concentrated over S[1/N]"); no hidden noetherian/reduced hypothesis
  (bridge-Q avoids the reducedness trap — the LINEAR ψ₂-condition at the 2Q SECTION is
  used, never the squared abscissa relation; the identity ψ₂³·ψ₂(2Q) = u(2B+u)e4Rel
  was verified mod curve over ℤ[B,u,v], so it holds in every chart ring).
- Source-drift: KM 4.6 quote asserts the naive level-N problem is a finite étale
  GL₂(ℤ/N)-torsor over S[1/N] — for N = 4 this is the axiom-2 instance replacing
  the refuted Legendre one; KM 4.6.1+2.2.11 is the ANALOGOUS bootstrap at 3, and the
  4.7.0 proof (quoted) uses only axioms 1)+2), so the substitution is licensed by the
  source's own axiomatization. Loeffler 3.3.4/3.3.5 quoted for the Tate-form leg.
- Prior-B2 consultation: b2_log has T-E15-NORM (E3 ring over-representing from a
  missing localization). The E4 analogue was attacked directly: the quartic's constant
  terms at the bad loci are UNITS (2B³, 2B³(16B−1)), so no analogous degenerate
  component exists — the γ-style fix is not needed at level 4. Also T-H4/T-H6
  (orbit-presheaf falsity) do not apply: `gammaFullNaiveProblem` (pairs of sections
  with fibrewise generation) is the H = ⊥ SECTION functor, not an orbit functor.

## 3. E4-B — the level-4 torsor package (`exists_levelFourTorsorData_ulift`)

Per the LevelThreeTorsor generality map (agent report, session record): every
mathematical component is already general-N or general-group; **no ZMod-4-ring wall
exists** (rank-two torsion = `addEquiv_pi_fin_two_zmod_of_natCard`, pure group theory;
matrix inverses via `mul_eq_one_comm` over CommRing). The package is a re-instantiation:

- **E4B-1** (leaves, wrappers ×~8): `levelFourData` (+`_Z/_f/_finite/_etale`),
  `levelFourEquivariantData`, `levelFour_surjective`, `levelFour_torsor` — copy the
  levelThree wrappers at N=4 under `IsUnit ((4:ℕ):R)` (⟸ IsUnit 2), consuming the
  general-N `gammaFullNaive_relRepData` body, `isFinite_fullLevelSpaceStruct`,
  `levelSpaceΓπ_etale` (receipt 7 — CLEAN), `exists_isNaiveFullLevel_of_isAlgClosed`,
  `exists_glSmul_eq` (2 ≤ 4), `glSmul_eq_one_of_eq_self`,
  `isIso_torsorSigmaDesc_of_existsUnique` (general engine).
- **E4B-2** (leaf): `exists_levelFourTorsorData` (Type 0) + **`_ulift`** (Type u) —
  the same `MulEquiv.ulift`/`Sigma.whiskerEquiv` transport, γ⁻¹ convention kept
  ([B2-TD-CONV]).

Sizing: LevelThreeTorsor is 891 lines with the general engine inside; the wrappers are
≈ 250–400 lines. One session.

## 4. E4-C — engine rewire + Legendre quarantine

- **E4C-1**: rewrite `EngineWiring.representable_baseChange_two` (EngineWiring.lean:75)
  onto φ₄ := (gammaFullNaiveGlAction R2 4).comp MulEquiv.ulift, X0 from
  `naiveLevelFour_representable_by_affine R2 (isUnit-2)`, TorsorData from E4B-2 —
  a term-level mirror of `representable_baseChange_three`; drop the LegendreTorsor
  import. `representable_of_affineOverEll_of_rigidNoeth` UNCHANGED.
- **E4C-2**: quarantine the Legendre subtree as documented non-goals
  (theorem_statement_protected pattern): `legendreDeltaGAction` B2 object +
  LegendreTorsor residuals (4 sorries) + SqrtCoverGlue `scaleTorsor_spec` (2 sorries)
  get NON-GOAL docstrings citing b2_log B2-DECISION; no receipt cone retains them.
  (Files stay; nothing deleted; sorry-census for receipt cones goes to zero here.)

## 5. E4-D — mouth core `exists_localModel_core_at` (EngineDescent.lean:2525, sorry :2593)

Route of record: board v10.339 + v10.339-addendum + v10.340 (read this session;
Stage-1/2 BANKED in the proof body). Remaining stages, all assembly:
- **E4D-1** (Stage 3a): global ω over L := Localization S via
  `nonempty_omegaBasis_of_finite_maximalSpectrum` / `_of_subsingleton_pic_bridge`
  (ForMathlib/SemilocalOmegaBasis.lean:172/186 — LANDED, axiom-clean; consumes
  mathlib `Pic.instFreeOfSubsingleton` via PicSubsingletonFree). Adapt orbit charts
  to the global ω ⟹ chart transVC cocycle lands in the nilpotent translation group
  T = {(1,r,s,t)}.
- **E4D-2** (Stage 3b): split the T-valued chart-Čech cocycle over Spec L: central
  extension 0 → (L,+) → T → (L²,+) → 0; each additive layer splits by the
  partition-of-unity / coprime-cover machinery
  (ForMathlib/AffineCechH1.lean:76/114/154 `exists_sub_liftOfLE_eq_of_isCoprime` —
  LANDED; the orbit cover is finite basic; iterate pairwise or n-cover partition per
  the v10.339-addendum recipe, ~150–300 lines).
- **E4D-3** (Stage 3c): correct charts (`pointedIso_hom_of_transVC_eq_one`), glue
  coefficients (structure-sheaf sheaf condition) to W₀L/L; glue the presentation ρ
  NATIVELY over A_a (`glueMorphisms_hf_of_agree`, `isPullback_projModelBaseChange`,
  `projModelZero_baseChange`) — F's direct-over-A_a route (no EGA IV §8).
- **E4D-4** (Stage 4, DONE): `exists_cocycle_hρact_of_presentation` (banked).
- **E4D-5** (Stage 5): coboundary over local Lᴳ via `exists_coboundary`, spread its
  4 entries + W₀L coefficients + CvcL entries to A_a via `fixedAwayMap` /
  `existsUnique_factor_fixedPoints_away` (Part-2 pattern of
  `exists_away_invariant_descent`).
Sizing: board estimate ~1000 lines in-body; multi-session by volume, no research gap.
Source: KM 2.2.2–2.2.5 quotes (§0) — ω Zariski-locally free + adapted coordinates —
run semilocally where Pic vanishes; the gluing is the in-tree route of record.

## 6. E4-E — recollement glue `glueEllObj_representableBy` (Recollement.lean:1484)

In-file recipe is complete (docstrings at :1392/:1441/:1484, read this session):
- **E4E-1**: produce `zglue : ZariskiSheaf P a b` from Stack.lean's
  `moduliProblem_fppf_separated` + `moduliProblem_fppf_descent` at the two-chart
  Zariski cover ([R-sheaf-P] assembly; import verified acyclic).
- **E4E-2**: `homGlueDescentData` (:1392 sorry) — [R-chart-eqv] (adjunction
  `baseChangeRingHomEquiv` + `representableBy_baseChangeRing` + `glueJa/glueJb`,
  matched on overlaps by `overlapIso`) + [R-hom-glue] (glue the EllHom fields via
  `glueBase_hom_ext`/`glueTotal_hom_ext`/pushout.desc; isPullback Zariski-local).
- **E4E-3**: discharge :1484 as
  `glueEllObj_representableBy_of_zariskiGlue a b hab hrel repr_a repr_b zglue`
  (parametrized skeleton LANDED).
Consumption spec preserved at
`.mathlib-quality/glueEllObj_consumption_spec.md` (copied from the prior session's
scratchpad this session). Sizing: register-box class, 1–2 sessions.

## 7. E4-F — Drinfeld invertible-N cone (receipts 2/3/6)

(filled from the cone-census agent report — see board v10.343 when posted; plan:
reroute any general-base sorried lemma actually in cone to an invertible-N instance
via the étale/Lagrange route per KM 1.4.4 (§0 quote); over-ℤ Deligne order-kills stays
out of scope as the documented future project.)

### §7 filled — E4-F census result (cone-census agent, 2026-07-20)

**Architecture:** the receipt statements in GammaH.lean are upstream "held" sorries; the
real assembled proofs live in `Moduli/GammaHClosure.lean` (0 sorries):
`gammaFullDrinfeld_rigid_and_representable` (:134) and the PIN-FREE
`gammaOneDrinfeld_rigid_and_representable` (:176, hbound discharged by `hbound_of_kvc`,
KeystoneGeometricPoint.lean:642). Definitions are sorry-free (no sorryAx via
`gammaOneDrinfeldProblem`/`gammaFullDrinfeldProblem`).

**Receipt 2 (gammaFullDrinfeld):** cone = SHARED ENGINE ONLY (EngineDescent:2593,
Recollement:1392/:1491). The invertible-N Drinfeld↔naive bridge
(`gammaFullDrinfeldNaiveIso` → `isFullLevel_iff_naive'` → FullLevelBridge.lean) is
sorry-free; naive rigidity/affineOverEll clean. **No Drinfeld-specific work.**

**Receipts 3/6 (gammaOneDrinfeld + prep):** cone = shared engine + exactly TWO leaves:
- **E4F-1**: `RelEffCartierDiv.IsSubgroup.smul_eq_zero_of_factors`
  (LevelStructure/ExactOrder.lean:113, sorry :117) — stated over a GENERAL base, but
  invertibility is available at both consumer sites (GammaHMaster:1194 hinvSpec;
  DrinfeldRepresentability:153 affineOverEll is gratuitously general — the receipt
  supplies hinv). PLAN: add `smul_eq_zero_of_factors_of_invertible` (invertible N:
  rank-N subgroup divisor is finite étale ⟹ étale-locally constant ⟹ killed by N by
  Lagrange — KM 1.4.4/3.7.2 route, §0 quotes) + restate `gammaOneDrinfeld_affineOverEll`
  with `hinv` + repoint the two sites. General-base `:117` and the DeligneOrder.lean
  boxes stay statement-protected as the future over-ℤ project.
- **E4F-2**: `Section.HasExactOrder.pull_nsmul_jetData` (ExactOrder.lean:832, sorry
  :849) — already carries `NIsInvertible`; its sole consumer is
  `pull_nsmul_ne_zero` (GammaHMaster:1206 site). PLAN: prove the consumer-level fact
  directly at invertible N (KM 1.4.4(3): exact order N + N invertible ⟹ the N points
  {aP̄} are distinct at every geometric point ⟹ a•P̄ ≠ 0 for 0 < a < N), bypassing
  the char-p jet keystone entirely; `:849` stays statement-protected (future over-ℤ).

**Quarantined non-goals confirmed NOT in any receipt cone:** GammaH trio :483/:496/:508
(general-H naive, FALSE for H ≠ ⊥ per T-H4/T-H6 b2 entries); DrinfeldRegularity.lean:269
(file imported nowhere); ExactOrder :917/:948 (naive-bridge/dead); DeligneOrder
:172/:2061/:2121; Subgroup.lean:317; EllCategory :298/:324 (bypassed old interface).

## 8. Receipt closure matrix (what flips what)

| Receipt | needs E4-A/B/C (D2 mouth) | needs E4-D (mouth core) | needs E4-E (glue) | needs E4-F |
|---|---|---|---|---|
| 1 gammaFullNaive | ✓ | ✓ | ✓ | — |
| 2 gammaFullDrinfeld | ✓ | ✓ | ✓ | — |
| 3 gammaOneDrinfeld | ✓ | ✓ | ✓ | F1+F2 |
| 4 gammaBot | ✓ | ✓ | ✓ | — |
| 5 gammaH_of_orderOf | ✓ | ✓ | ✓ | — |
| 6 gammaOneDrinfeld prep | ✓ | ✓ | ✓ | F1+F2 |
| 7 levelSpaceΓπ_etale | CLEAN | | | |

(The D(3) leg is sorry-free; `representable_baseChange_three` carries no open leaf.)
