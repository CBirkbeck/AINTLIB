# STREAM-NISOG decomposition — cyclic N-isogenies + cyclicity as a closed condition (KM Ch. 6)

*/develop --decompose planning worker, 2026-07-08. Stream: the review-Q8 named N-Isog block +
the Γ₀(N)-via-isogenies layer — standard cyclic subgroups, the N-isogeny `E → E/C`, cyclicity
as a closed/constructible condition on subgroup divisors, as KM Ch. 6 develops it.*

**Source read in FULL**: `refs/ModularCurves/katz-mazur-arithmetic-moduli-FULL.pdf`, Chapter 6
"CYCLICITY", print pp. 152–185 (PDF 163–196), plus the Ch. 5 inputs 5.5.4/5.5.7/5.5.8 (print
pp. 146–150, PDF 157–161). PDF page = print page + 11.

**Skeleton**: `projects/ModularCurves/ModularCurves/GroupScheme/NIsogeny.lean` (805 lines,
52 declarations, registered in the root `ModularCurves.lean`). `lake build
ModularCurves.GroupScheme.NIsogeny` **GREEN** (2026-07-08). 31 raw sorries = 29 theorem-level
+ 2 DS-data (§DS below); 21 declarations sorry-free in their own proofs (all `choose_spec`
pins, the `Iff.rfl` fppf-bridge, `primeOrderDivisor_degree` via the proven
`sectionsDivisor_degree`, and the BB-DELIGNE-routed `pointSubgroup_le_torsion`).

---

## 0. Register and design decisions (RR-only; the T-SG2 GATE respected)

- **Divisor register.** Cyclicity of record is `IsGammaZeroFppf` (T-D10 statement in the HELD
  `LevelStructure/Basic.lean`; T-SG2's `IsCyclic`/`GammaZeroStructure` sit on top). All of
  Ch. 6's generator bookkeeping is stated on `RelEffCartierDiv E.π`; the subgroup-scheme
  packaging is provided where KM needs a scheme (`standardCyclicSubgroup` via the proven
  `ofRelEffCartierDiv` bridge). No Γ₀ statement targets the geometric surrogate `IsGammaZero`.
- **RR-only.** Every moduli statement is relative to a fixed `E : EllipticCurve S` (a
  classifying finite `S`-scheme with per-test-morphism equivalences, T-W8-style). KM 6.6.1's
  (Ell)-global clauses (degree `ψ(N)`, regularity, [Γ₁]→[Γ₀] of rank φ(N)) and all of KM 6.8.1–
  6.8.9 except 6.8.7 are **out of stream** (global-moduli phase; see §6.6/§6.8 notes).
- **Choose-pattern, small DS surface.** Data whose existence is a KM theorem
  (`generatorSpace`, `standardCyclicDivisor`, `imageDivisor`) are *real* `Classical.choose`
  definitions off sorried ∃-theorems, with pins proved from `choose_spec` — the sorry stays
  theorem-level (T-W8/levelSpaces precedent; DS-adjacent, flagged in §DS). Only the
  [T-G3D-INFRA]-gated quotient-curve pair is honest DS-data.
- **Quotients are NEVER built here.** Everything needing `E/C` cites the named gate
  [T-G3D-INFRA] (p0's `SubgroupQuotient.lean` interface); the elliptic-curve upgrade is the
  two DS-defs, construction gated on that stream landing ([T-G3D-INFRA-CURVE]).

### Fibrewise vs closed-condition inventory (binding item 1)

KM's standard proof scheme in Ch. 6 is a four-step pipeline; each leaf below records which
steps it uses:
(i) **fppf-localize** to a generator (the *definition* of cyclic is fppf-local — KM 3.7.1:
"the notion of cyclicity is by definition local for the f.p.p.f. topology");
(ii) **reduce to the universal case** — the moduli problem of the data in play is flat over ℤ
(KM 5.1.1 / 6.6.1; gate [KM-FMT-FLAT]) so it suffices to treat `S` flat over ℤ, noetherian;
(iii) **check over the dense open `S⊗ℤ[1/N]`** — a *fibrewise/elementary* statement (finite
abelian groups: "physically obvious");
(iv) **conclude by a closed-condition lemma** — the locus of truth is closed in `S`
(Useful Lemma 6.7.3 / flattening 6.4.3 / the generator-scheme loci).

- **Fibrewise/geometric-point statements**: Lemma 6.4.2 (field fibres of `G^×` — over
  arbitrary fields, NOT just algebraically closed); the fibre counts in 6.5.1's finiteness
  (over `k̄`: `(ℤ/pⁿ)²`-subgroup count, `Ker Fⁿ` supersingular, `μ_{p^a} × p^{n−b}ℤ/pⁿℤ`
  ordinary); every step-(iii) check.
- **Closed-condition-over-the-base statements**: 6.4.1 (cyclicity locus), 6.4.3 (flattening
  stratification), 6.7.3 (Useful Lemma — in-project at divisor level as the PROVEN
  `RelEffCartierDiv.exists_incidenceLocusEQ`, T-D15), the generator-scheme representability
  (KM 6.1 / 1.10.13 — in-project route via `exists_incidenceLocusEQ`), and the implicit loci
  in the 6.7.2/6.7.4/6.7.11 proofs.
- **fppf-local statements** (neither): cyclicity itself, 6.7.2's construction of `G_d`,
  6.7.13's criterion.

---

## 1. KM Chapter 6, prose proofs preserving KM's structure

### 6.1 The Main Theorem (print pp. 152–155)

**KM 6.1 (p. 152, verbatim)**: *"We say that G is cyclic if, locally f.p.p.f. on S, G admits
a generator, (a "ℤ/Nℤ-generator" in the notations of (1.10.5)) i.e., a section P ∈ G(S) such
that its N multiples {aP}, a = 0,1,…,N−1 form a "full set of sections" of G/S. The functor on
(Sch/S), T ↦ generators of G_T/T, is representable by a closed subscheme G^× of G, defined,
locally on S, by finitely many equations (G^× is the scheme denoted "ℤ/Nℤ-Gen(G/S)" in
(1.10.13)) … We refer to G^× as the "scheme of generators" of G. It is a finite S-scheme of
finite presentation, whose formation commutes with arbitrary change of base S′ → S."*

**KM 6.1.1 (pp. 152–153, verbatim)**: *"Let E/S be an elliptic curve over an arbitrary base
S, N ≥ 1 an integer, and G ⊂ E[N] a finite locally free commutative S-subgroup-scheme of
E/S, of rank N over S. Then (1) G is cyclic if and only if its scheme of generators G^× is
finite locally free over S, of rank φ(N). (2) Suppose that G/S is cyclic, and that P ∈ G(S)
is a generator. Then the Cartier divisor D in E defined by D = Σ_{(a,N)=1, a mod N} [aP]
lies in G, and we have an equality of closed subschemes of G: D = G^×."*

**KM's proof, structure preserved.**
1. (⟸ of (1), p. 153): *"If G^× is finite locally free over S, of rank φ(N), then G is
   certainly cyclic, for it acquires a generator after the f.p.p.f. base change G^× → S."*
   (`φ(N) ≥ 1` makes `G^× → S` surjective; flat + lfp are part of "finite locally free".)
2. (⟹ of (1) reduces to (2), p. 153): *"The question is f.p.p.f. local on S, so we may
   assume that G admits a generator P ∈ G(S). In this case, (1) follows from (2), for the
   Cartier divisor D is visibly finite locally free over S, of degree φ(N)."* Reduce to
   `N = pⁿ` by the *"factorization into prime powers" lemma (1.7.3, 1.10.15)*; note *"(2) is
   physically obvious if N is invertible on S"* (3.7.2).
3. (`D ⊆ G^×`, pp. 153–154): `D ⊆ G` is clear since *"G as a Cartier divisor in E is given
   by G = Σ_{a mod N} [aP]"*. For `D ⊆ G^×`: *"it suffices, by reduction to the universal
   case, to treat the case when S is affine, S = Spec(A), and flat over ℤ (simply because
   [Γ₁(N)] is flat over ℤ). Let Q ∈ G(D) = G_D(D) be the tautological section … We must show
   that Q is a generator of G_D. Let {f_i} be … functions … which define the closed subscheme
   G^×. We must show that f_i(Q) = 0 in Γ(D, O_D). But D is flat over ℤ … and we know that
   the assertion is true if we invert N."* — steps (ii)+(iii) with flatness of `D/ℤ` closing.
4. (`G^× ⊆ D`, pp. 154–162): both finite over `S`, so `D ⊆ G^×` is a closed immersion; to
   show it is an isomorphism, pass to the universal case via two auxiliary moduli problems
   `𝒫₁, 𝒫₂` of triples `(P, G, Q)` (`Q ∈ D(S)` resp. `Q ∈ G^×(S)`), a morphism `𝒫₁ → 𝒫₂`,
   and *"a variant of the homogeneity argument of (5.2)"*:
   - **6.2.1 Axiomatic Isomorphism Theorem (p. 155, verbatim)**: *"Suppose that (1) Both 𝒫₁
     and 𝒫₂ satisfy axioms Reg. 1, Reg. 3, and Reg. 4A of (5.2). (2) After inverting p, the
     induced morphism … is an isomorphism 𝒫₁⊗ℤ[1/p] ≅ 𝒫₂⊗ℤ[1/p]. (3) For any algebraically
     closed field k of characteristic p, and any supersingular elliptic curve E₀/k with
     universal formal deformation E/W(k)[[T]], the morphism of finite W[[T]]-schemes
     𝒫₁,E/W[[T]] → 𝒫₂,E/W[[T]] is an isomorphism. Then the given morphism is an isomorphism."*
     Proof: kernel ⊕ cokernel of the corresponding coherent sheaves vanish on an open set
     containing all points (as in 5.2.1).
   - **6.3 (pp. 156–162)**: check (3) explicitly. `A = W[[T,P]]/I` (the subgroup-scheme
     condition on `∏_{1≤a≤pⁿ}(X − [a](P))`), `A₁ = A[[Q]]/J`,
     `J = (∏_{(b,p)=1, b mod pⁿ}(Q − [b](P)))`, `A₂ = A[[Q]]/K` (equality of the two monic
     polynomials). `A₂ → A₁` surjective with kernel `Ker`; Nakayama:
     `Ker = 0 ⟺ Ker/QKer = 0`; serpent lemma against "multiplication by Q";
     **Lemma 6.3.4** (mult-by-`Q` injective on `A₁`: Weierstrass preparation, `A₁` A-free on
     `1,Q,…,Q^{φ(pⁿ)−1}`, determinant `= ∏_{(b,p)=1}[b](P)`, non-zero since `P` is part of a
     regular parameter system and the `(ℤ/pⁿℤ)ˣ`-action transports this);
     **Lemma 6.3.5** (`A₂/QA₂ ≅ A₁/QA₁`: compare the ideal of coefficients of
     `X^{pⁿ} − ∏(X−[a](P))` with the principal ideal `(∏[b](P))` via the degree
     `pⁿ − φ(pⁿ)` coefficient); **Lemma 6.3.6** (`[a](P) = P·(unit)` if `(a,p)=1`,
     `P·(elt of max A)` if `p ∣ a` — from `[a](X) = aX mod X²`).

### 6.4 Cyclicity as a closed condition (pp. 162–164) — T-SG3

**KM 6.4.1 (p. 162, verbatim)**: *"Then there exists a closed subscheme W ⊂ S, defined
locally on S by finitely many equations, which is universal for the condition "G is cyclic",
in the sense that for any morphism T → S, the inverse image G_T/T is cyclic if and only if
the map T → S factors through the closed subscheme W."* Proof: Zariski-local, reduce to `S`
noetherian; `G^× = Spec(𝓕)`; *"the condition … that G_T be cyclic is that its scheme of
generators (G_T)^× … be a finite locally free scheme over T of rank φ(N)"* (6.1.1 — **both
directions**); then:

**KM 6.4.2 (p. 163, verbatim, FIBREWISE)**: *"For any field-valued point Spec(k) → S of S,
the fiber 𝓕⊗k is a k-vector space, whose dimension is given by: dim_k(𝓕⊗k) = φ(N) if G_k/k
is cyclic, 0 if not. … If G_k/k is not cyclic, then, k being a field, G_k never becomes
cyclic after any field extension. Therefore the k-scheme (G_k)^× has no field-valued points,
hence it is the empty scheme, i.e., its affine ring is the zero-ring."*

**KM 6.4.3 (p. 163, verbatim, CLOSED-CONDITION)**: *"Given a noetherian scheme S, a coherent
sheaf 𝓕 on S, and an integer n such that for all s ∈ S, dim_{k(s)}(𝓕⊗k(s)) ≤ n, the
condition on S-schemes T → S that 𝓕_T be locally free of rank n on T is represented by a
closed subscheme W of S."* Proof: Mumford's flattening stratification, direct construction:
local presentation `(O_U)^m →α (O_U)^n →π 𝓕|U → 0` where the `n` sections span each fibre
(Nakayama); `W ∩ U = V(nm matrix coefficients of α)`; converse via a splitting `β`
(`πβ = id`) and Cramer's rule ("α = 0" ⟺ "β surjective" ⟸ `det β` invertible).

### 6.5 The moduli problem [N-Isog] (pp. 164–166) — review-Q8 block

**KM (pp. 164–165, verbatim)**: *"[N-Isog](E/S) = the set of finite locally free commutative
S-subgroup-schemes G ⊂ E[N] which are of rank N over S."* **Prop 6.5.1**: *"The moduli
problem [N-Isog] is relatively representable and finite over (Ell)."* Proof: view `E[N] =
Spec 𝓕`, `𝓕` a bi-algebra locally free of rank `N²`; *"A subgroup G ⊂ E[N] of the type
being sought is nothing other than a locally free rank-N quotient 𝔥 of 𝓕, such that the
locally free rank N²−N kernel 𝒦 ⊂ 𝓕 is a bi-ideal in 𝓕. Therefore [N-Isog] is relatively
represented by a closed subscheme of the Grassmannian of all rank N quotients of 𝓕."*
Finiteness of fibres over algebraically closed `k`: reduce to `N = pⁿ`; `char k ≠ p`:
finitely many subgroups of `(ℤ/pⁿℤ)²`; `char k = p` supersingular: the unique `Ker(Fⁿ)`;
ordinary: `E[pⁿ] ≅ μ_{pⁿ} × ℤ/pⁿℤ` and `G ≅ G^conn × G^ét` gives exactly the `n+1` subgroups
`μ_{p^a} × (p^{n−b}ℤ/pⁿℤ)`, `a+b = n`.

### 6.6 [Γ₀(N)] and the First Main Theorem for it (pp. 166–167)

**KM 6.6.1 (p. 166, verbatim, the RR-core sentence)**: *"For any E/S, [Γ₀(N)] is relatively
represented by the closed subscheme of the finite S-scheme [N-Isog]_{E/S} over which the
universal N-isogeny is cyclic."* (then, (Ell)-globally: finite flat of degree
`(N²/φ(N))·∏_{p|N}(1−1/p²)` = `N·∏(1+1/p)`; `[Γ₁(N)] → [Γ₀(N)]` is relatively representable
by *"the scheme of generators G^× of the universal cyclic N-group"*, finite flat of rank
φ(N) by 6.1.1; regularity descends from `[Γ₁(N)]` (5.1.1) since it is finite flat "under"
it, [A-K VII 4.8]; then finite flat over (Ell) [A-K V 3.8]). **Stream boundary**: only the
RR-core sentence is in the skeleton (`exists_gammaZeroSpace`); degree/regularity/rank-φ(N)
clauses are FMT-phase, boarded to the representability stream (T-E9/T-H9 lineage).

### 6.7 Standard cyclic subgroups + factorizations (pp. 167–178)

**KM 6.7.1 (p. 167, verbatim)**: *""cyclic group (over S) of order N" … shorthand for
"finite locally free commutative S-group-scheme, of rank N, and cyclic", and the expression
"cyclic N-isogeny" to mean an isogeny whose kernel is a cyclic group of order N."*

**KM 6.7.2 (p. 167, verbatim)**: *"For every divisor d of N, there is a "standard" cyclic
subgroup G_d ⊂ G of order d, which may be described, f.p.p.f. locally on S, in terms of any
generator P of G, as the cyclic subgroup of order d generated by (N/d)P."* Proof: construct
fppf-locally; for generators `P, P′`, *"By (5.5.7), the points (N/d)P and (N/d)P′ both have
"exact order d""* [KM 5.5.7(2), p. 148, verbatim: *"If P has "exact order N" on E/S, then
for every divisor d of N, the point dP has "exact order N/d" on E/S."*]; both `G_d, G_d′`
lie in `G` as divisors (`G = Σ_{a mod N}[aP]`, `G_d = Σ_{b mod d}[b(N/d)P]`); to show
`G_d = G_d′`: steps (ii) (universal case = `[Γ₁(N)] ×_{[Γ₀(N)]} [Γ₁(N)]`, finite flat over
`[Γ₀(N)]` of degree φ(N)² by 6.6.1, hence flat over ℤ), (iii) (physically obvious when `N`
invertible), (iv):

**KM 6.7.3 USEFUL LEMMA (p. 168, verbatim)**: *"Let S be a noetherian scheme, W a finite
flat S-scheme, and Z₁, Z₂ two closed subschemes of W, each of which is finite flat over S.
Then the locus "Z₁ = Z₂" is a closed subscheme of S."* Proof: `W = Spec 𝓕`; the locus is
where both maps `α : I → 𝓕/J`, `β : J → 𝓕/I` of locally free sheaves vanish. **In-project**:
at the divisor level this is exactly `RelEffCartierDiv.exists_incidenceLocusLE/EQ`
(T-D14/T-D15, PROVED sorry-free in `LevelStructure/Incidence.lean`) — and every Ch. 6 use
(6.7.2/6.7.4/6.7.9/6.7.11) is on subschemes of the curve or of a kernel in it, i.e.
divisors. **No new lemma is minted for 6.7.3.**

**KM 6.7.4 (p. 169, verbatim)**: *"Then the quotient group G′ = G mod G_d in the quotient
elliptic curve E′ = E mod G_d is cyclic of order N/d. If P is a generator of G, then its
image P′ in G′ generates G′. If d|d′|N, then G_d ⊂ G_{d′} is the standard cyclic subgroup of
G_{d′} of order d, and the quotient G_{d′}/G_d in G/G_d is its standard cyclic subgroup of
order (d′/d)."* Proof: fppf-localize to a generator; steps (ii)–(iv), third clause closing
by the Useful Lemma.

**KM 6.7.5 (pp. 169–170, verbatim)**: *"Then we have an equality of Cartier divisors inside
E: G = Σ_{d|N} (G_d)^×. Proof. The equality of two Cartier divisors inside E/S may be
checked f.p.p.f. locally on S. This reduces us to the case when G admits a generator P, in
which case the assertion is obvious; for we have G = Σ_{a mod N} [aP];
G_d^× = Σ_{(b,d)=1, b mod d} [b(N/d)P]."*

**KM 6.7.6 (p. 170, verbatim)**: *"we will refer to G′ = G mod G_d as the standard cyclic
N/d-quotient of the cyclic group G. Given a cyclic N-isogeny π with kernel G … and a divisor
d of N, we will refer to the factorization E →^{π_d} E′ →^{π′} E″ (ker π_d = G_d,
ker π′ = G′) as the standard factorization of the cyclic N-isogeny π into a cyclic d-isogeny
followed by a cyclic N/d-isogeny."* **(6.7.7)**: the pair `(π₁, π₂)` is *cyclic in standard
order* if the composite is cyclic and `Ker(π₁)` is the standard cyclic subgroup of
`Ker(π₂π₁)` of order `d₁`.

**KM 6.7.8 (p. 171, verbatim)**: *"Suppose that π₂ is etale (a condition which is automatic
if d₂ is invertible on S). Then the following are equivalent. (1) The composite π = π₂π₁ is
cyclic. (2) π₁, π₂ and π = π₂π₁ are all cyclic. (3) π, π₁, π₂ are all cyclic, and (π₁,π₂) is
the standard factorization of π."* Proof: fppf-localize to a generator
`φ : ℤ/d₁d₂ℤ → G(S)`; *"Applying the key result (1.11.2), we see that the oblique arrow must
be surjective"* — the exact sequence `0 → Ker π₁ → G → Ker π₂ → 0` receives
`0 → d₂ℤ/d₁d₂ℤ → ℤ/d₁d₂ℤ → ℤ/d₂ℤ → 0` with all verticals generators; `Ker π₁` is generated
by `d₂P`, hence standard.

**KM 6.7.11 BACKING-UP THEOREM (p. 173, verbatim)**: *"Let … E →^{π_d} E′ →^{π′} E″ the
standard factorization of a cyclic N-isogeny … Let P ∈ (Ker π)(S). Then (1) If P generates
Ker π, then π_d P generates Ker π′, and (N/d)P generates Ker(π_d). (2) If N and N/d have the
same prime factors, then P generates Ker π if and only if π_d P generates Ker π′. (In
particular, 0 generates Ker π if and only if 0 generates Ker π′.)"* Proof of (1): the datum
(cyclic N-isogeny + generator) *"is precisely a Γ₁(N)-structure"*; steps (ii)–(iv). Proof of
(2): `π_d` induces `(Ker π)^× → (Ker π′)^×`; the claim is that the square with
`Ker π → Ker π′` is **cartesian**; steps (ii)–(iii), then (iv) *"we simply apply the Useful
Lemma 6.7.3 to the finite flat S-scheme Ker π, its … subscheme (Ker π)^×, and the
fiber-product … finite flat over S because π_d is a finite flat map, and (Ker π′)^× is
finite flat over S."*

**Downstream of the skeleton (documented, NOT stated — no vocabulary yet)**: 6.7.9 (duals:
`(π₁,π₂)` standard ⟺ `(π₂ᵗ,π₁ᵗ)` standard; *"(By (5.5.4, (3)), these duals are also
cyclic.)"* — needs dual-isogeny vocabulary, KM 2.9/T-G3c lineage), 6.7.10 (coprime degrees:
kernel splits `G = G[d₁] × G[d₂]`), 6.7.12/6.7.13 (standard-order criterion), 6.7.14–6.7.15
(chains: standard order ⟺ every 2-step chain standard, by induction + backing-up), 6.7.16
(Frobenius–Verschiebung non-standard example). Board these as Phase-2 leaves
[NISOG-P2-DUAL/COPRIME/CRIT/CHAIN] once quotient + dual vocabulary exists.

### 6.8 More on [N-Isog] (pp. 178–185)

**KM 6.8.7 (p. 183, verbatim)**: *"If N ≥ 1 is a square-free integer, then every N-isogeny
is cyclic, i.e., the closed immersion of moduli problems over (Ell) [Γ₀(N)] ↪ [N-Isog] is an
isomorphism. Proof. … Because [N-Isog] is flat over ℤ, the usual "reduction to the universal
case" reduces us to treating the case when S is flat over ℤ. The locus "G is cyclic" is a
closed subscheme of S, so it suffices to show that G is cyclic over S⊗ℤ[1/N], where it is
physically obvious: an abelian group of square-free order is cyclic."*

**Out of stream** (global-moduli/Serre–Tate phase, documented only): 6.8.1 ([N-Isog] finite
flat over (Ell) via the Axiomatic Finite Flatness Theorem 6.8.2 + Drinfeld's Serre–Tate
theorem 6.8.4 + the one-equation lifting locus 6.8.6), 6.8.8 ([pⁿ-Isog] not normal, `n ≥ 2`,
via `[pⁿ-Isog]⊗ℤ[1/p] ≅ ∐_{2a+b=n}[Γ₀(p^b)]⊗ℤ[1/p]` and the supersingular count), 6.8.9
(normalization of `[pⁿ-Isog]` = `∐ [Γ₀(p^b)]`).

---

## 2. Ordered leaf decomposition (skeleton ↔ KM), with per-leaf discipline

Format per leaf: **[id] Lean decl — KM locator** · quote-key (see §1) · Lean↔source match ·
attacks (≥3) · provability verdict · LOC (grounded in KM's own line counts; a KM page ≈ 30
lines).

### Block A — scheme of generators (KM 6.1 preamble)

**[L1] `exists_locallyFreeRankLocus` — KM 6.4.3 (p. 163)** *(placed first: E-independent)*
· Quote §1/6.4.3. · Match: KM's coherent `𝓕` with fibre bound ↦ finite lfp `f : W ⟶ S` with
the field-fibre dichotomy (empty or flf rank `n`) — the *specialisation actually consumed*
by 6.4.1, since Lemma 6.4.2 outputs the dichotomy, not just `≤ n`; the represented condition
"`𝓕_T` locally free of rank n" ↦ `Flat (pullback.snd f t) ∧ finrank ≡ n`. The general
`≤ n` form is the ForMathlib refinement, sub-leaf [L1-gen] when discharged.
· Attacks: (1) `n = 0` ⇒ locus = complement of the (closed, `f` finite) image — statement
survives; (2) dropping the bound kills representability (rank can jump UP under
specialisation only; a rank-`n+1` generic point has no closed rank-`n` locus through it) —
hypothesis load-bearing; (3) `Flat` on the RHS is required — constant pointwise finrank
without flatness is satisfiable by non-locally-free modules over non-reduced `T`;
(4) noetherian reduction (KM's step) is INSIDE the proof, not the statement — `f` lfp makes
the locus construction spread out.
· Provability: **project-hard, no external gate** — mathlib has no flattening
stratification; the module half (matrix-coefficient locus) is elementary CA; the glue can
mirror Incidence.lean's `vanishingLocus` machinery (affine-local ideal patching, PROVEN).
· LOC: KM ~25 lines ⇒ Lean 350–550 (module lemma 150–250 + scheme glue 200–300).

**[L2] `IsDivisorGenerator` (def, REAL) + [L2′] `isGammaZeroFppf_iff_generator`
(PROVED, `Iff.rfl`) — KM 6.1/1.10.5**
· Quote §1/6.1. · Match: "generator" = exact order `N` + order divisor = `D` after base
change — precisely `IsGammaZeroFppf`'s cover payload (T-D10's spelling, HELD file, untouched).
· Attacks: (1) definitional-bridge canary: if T-D10's spelling drifts, `Iff.rfl` breaks
first; (2) `HasExactOrder` conjunct is NOT redundant given the ideal equation unless `D` is
a subgroup divisor (transport along `RelEffCartierDiv.ext`) — keeping both mirrors KM's "a
section P such that {aP} form a full set of sections OF G" (subgroup-ness is carried by G);
(3) quantifying over `t : T ⟶ S` arbitrary (not fppf) keeps the predicate usable both for
covers and for field points. · Status: **compiled, sorry-free**.

**[L3] `exists_generatorLocus` — KM 6.1 (p. 152) + 1.10.13**
· Quote §1/6.1 ("representable by a closed subscheme G^× of G … finitely many equations").
· Match: KM's `G^×` ⊆ G ↦ ideal-sheaf locus `Z` on `D.ideal.subscheme`; "T-points of G" ↦
pairs `(P, h)` with `h ≫ subschemeι = P.1` (unique since `ι` mono — KM's `G(T)`); the
represented functor is literally KM's "generators of `G_T/T`".
· Attacks: (1) the discharge does NOT need KM Ch. 1's full-set-of-sections machinery: the
generator condition is an order-divisor/ideal EQUALITY, so `exists_incidenceLocusEQ`
(PROVEN) over the base `D.ideal.subscheme` on (orderDivisor of the tautological point) vs
(pullback of `D`) cuts the locus — the base-change transport is `orderDivisor_baseChange`
(PROVEN) + `IsSubgroup.baseChange` (PROVEN); (2) hD is load-bearing (see L2 attack 2; without
it the iff is false — the locus contains points whose order divisor equals a non-subgroup
`D_T`, where `HasExactOrder` fails); (3) the `asSection`-spelling of the tautological point
over `D` is the known normalisation hazard — `exists_exactOrderLocus`'s Tier-5/6 aux layer
(PROVEN) is the in-project template to imitate, so hazard ≠ gate; (4) `N = 1`: every point
of the zero divisor is a generator, locus = ⊤ — consistent.
· Provability: **dischargeable NOW from proven project machinery** (T-D15 + T-D6a-ii L3 +
T-D33 patterns). **← FIRST ACT of the stream.**
· LOC: KM states it in 6 lines (content in 1.10.13); Lean 250–400 (the transport layer
dominates, cf. `exactOrderLocusAux_*` ~450 lines for the analogous statement).

**[L4] `generatorSpace`/`generatorSpaceι`/`generatorSpaceπ` (defs, REAL) +
`generatorSpace_spec` (PROVED)** — choose-pattern off L3. Status: **compiled**.

**[L5] `generatorSpace_baseChange` — KM 6.1 (p. 152) "formation commutes with arbitrary
change of base"**
· Match: base-change compat as ∃-iso over the pullback presentation.
· Attacks: (1) both sides represent the same functor (L3's spec after composing test maps) —
Yoneda closes it, no geometry; (2) the iso must commute with the π's — pinned in the ∃;
(3) iterated base change only up to canonical iso (project convention — no `_baseChange`
identity, cf. `baseChange_baseChange_ideal` note in Subgroup.lean).
· Provability: dischargeable from L3's spec (universal property both ways). LOC 120–200.

### Block B — Main Theorem 6.1.1

**[L6] `isGammaZeroFppf_of_generatorSpace_finiteLocallyFree` — KM 6.1.1(1)⟸ (p. 153)**
· Quote §1/proof-1. · Match: "finite locally free of rank φ(N)" ↦ the four hypotheses on
`generatorSpaceπ`; "acquires a generator after the f.p.p.f. base change `G^× → S`" ↦ the
`IsGammaZeroFppf` cover `T := generatorSpace`, `h := generatorSpaceπ`.
· Attacks: (1) surjectivity: mathlib `Scheme.Hom.one_le_finrank_iff_surjective`
([Flat][IsFinite], VERIFIED present in `Morphisms/FlatRank.lean`) + `Nat.totient_pos`;
`AlgebraicGeometry.Surjective → Function.Surjective .base` via the class field; (2) the
tautological generator over `D^×` = L4's spec at the identity factorisation — the transport
to the cover-presented base change is the L3-attack-3 normalisation, in-project pattern;
(3) `S = ∅`: hypotheses vacuous, conclusion holds with the empty cover — no corner failure.
· Provability: mathlib-verified + project-cited; no external gate. LOC: KM 3 lines ⇒ Lean
100–180 (transport-dominated).

**[L7] `generatorSpace_finiteLocallyFree_of_isGammaZeroFppf` — KM 6.1.1(1)⟹ (pp. 153–162)**
· Quote §1/6.1.1 + proof-2/4. · Match: conclusion = the four clauses; KM's fppf-localisation
+ prime-power reduction + 𝒫₁→𝒫₂ + 6.2.1 + 6.3 pipeline is the proof obligation.
· Attacks: (1) the fppf-local reduction needs *descent of finite-locally-free-of-rank-r
along fppf covers* for the generator scheme — part of [T-D10-FPPF]; (2) the prime-power
factorization (KM 1.7.3/1.10.15) at divisor level = coprime splitting of order divisors —
sub-leaf, elementary but unbuilt; (3) the supersingular formal-deformation check is
[KM-62-63-HOMOG] irreducibly (universal deformation rings `W[[T]]`, `[Γ₁(pⁿ)]` local rings
`A = W[[T,P]]/I` — KM 5.1.1/5.3 infrastructure absent from project).
· Provability: **GATE [KM-62-63-HOMOG] + [KM-FMT-FLAT] + [T-D10-FPPF]**.
· LOC: KM ~7 pages ⇒ Lean 1500+ post-gates (the gate itself is a stream).

**[L8] `primeOrderDivisor` (def, REAL) + `primeOrderDivisor_degree` (PROVED) —
KM 6.1.1(2) `D = Σ_{(a,N)=1}[aP]` (p. 153)**
· Match: the `φ(N)` sections `aP`, `(a,N)=1` ↦ `sectionsDivisor` over
`Fin φ(N) ≃ (ZMod N)ˣ` (`ZMod.card_units_eq_totient`); degree pin = the PROVEN
`sectionsDivisor_degree` (T-D3a) + `E.smooth`.
· Attacks: (1) enumeration choice is a permutation — `sectionsDivisor`'s ideal is a
`Finset.prod` of kernels, hence permutation-invariant on the nose; (2) `N = 1`: `φ(1) = 1`,
divisor `= [0]` — the zero-section divisor, degree 1, consistent; (3) representative choice
`(u : ZMod N).val ∈ [0,N)` vs KM's `a mod N`: the smul only depends on the residue if the
point is killed by `N` — for the DEF no killing is needed (it is a divisor of whatever
sections these are); the comparison lemmas (L9–L11) carry the killing hypotheses.
· Status: **compiled, sorry-free**.

**[L9] `isDivisorGenerator_smul` — KM 6.1.1(2) first half `D ⊆ G^×` (pp. 153–154)**
· Quote §1/proof-3. · Match: "each `aP`, `(a,N)=1`, is a generator" in the raw global form
(the tautological-section trick recovers KM's relative form; artifact note below).
· Attacks: (1) over `ℤ[1/N]` this is elementary (a unit multiple of a generator of a cyclic
group generates), and KM's ONLY route from there to ℤ is flatness of `[Γ₁(N)]`/D over ℤ —
[KM-FMT-FLAT] irreducible; (2) char `p ∣ N` sanity: `Ker F`, generator `0`, `a•0 = 0` ✓;
(3) `hgen` cannot be weakened to "ideals equal after base change to geometric points"
(non-reduced bases — the `ℚ̄[ε]` trap).
· Provability: **GATE [KM-FMT-FLAT]**. LOC: KM ~25 lines ⇒ Lean 200–350 post-gate.

**[L10] `factors_primeOrderDivisor_of_isDivisorGenerator` — KM 6.1.1(2) second half
`G^× ⊆ D` (pp. 154–162)** · Quote §1/proof-4. · Match: "the closed immersion `D ⊂ G^×` is an
isomorphism" in functor-of-points form (every generator lies on `D`).
· Attacks: (1) this direction is where 6.2/6.3 live — no elementary escape (over `ℤ[1/N]`
easy; the supersingular locus needs the determinant argument); (2) stated against the
S-level subscheme of `primeOrderDivisor` (raw factoring, `smul_eq_zero_of_factors'` shape) —
avoids base-changed-divisor spelling; (3) `Q`'s base `T` arbitrary — KM's universal case IS
a particular `T`.
· Provability: **GATE [KM-62-63-HOMOG]**. LOC: with L7 (shared machinery); assembly 150.

**[L11] `isDivisorGenerator_iff_factors_primeOrderDivisor` — KM 6.1.1(2) assembled**
· Match: `D = G^×` as functors of points; scheme-level equality recoverable at the
tautological point (KM's own move, p. 154). · Attacks: (1) ⟸ is L9 base-changed + the
residue-representative bookkeeping (`a•Q₀` with `a = u.val`); (2) ⟹ is L10; (3) the iff at
EVERY `T` is strictly stronger than ideal equality — it is the right statement for
downstream 6.7.11(2). · Provability: assembly of L9+L10. LOC 100–150.

### Block C — closed condition (KM 6.4) = T-SG3

**[L12] `generatorSpace_fibre_isEmpty_of_not_isGammaZeroFppf` — KM 6.4.2 empty half
(p. 163), FIBREWISE**
· Quote §1/6.4.2. · Match: "no field-valued points, hence empty" ↦ `IsEmpty` of the honest
fibre `pullback (generatorSpaceπ) t`; arbitrary `Field k` (KM's generality — NOT `IsAlgClosed`).
· Attacks: (1) the kernel step "never becomes cyclic after any field extension" is the
fppf-descent of cyclicity to field points: a generator over a `k`-algebra cover specialises
to one over a field extension — needs [T-D10-FPPF]-lite (field case); (2) a field-valued
point of the fibre IS a generator over an extension field (L4 spec at that point) —
contradiction closes; (3) the `φ(N)`-rank half of 6.4.2 is NOT a separate leaf: it is L7
base-changed to `Spec k` through L5 (recorded here, consumed inside L13).
· Provability: [T-D10-FPPF]-lite + L4/L5; post-L7 for the companion half. LOC: KM 8 lines ⇒
Lean 120–200.

**[L13] `exists_cyclicityLocus` — KM 6.4.1 (p. 162) = ticket T-SG3, CLOSED-CONDITION**
· Quote §1/6.4.1 (also banked in tickets v10-quotes). · Match: `W ⊆ S` ↦ `Z :
S.IdealSheafData`; "for any T → S … cyclic iff factors" ↦ the stated iff against
`IsGammaZeroFppf` of the base change (the T-SG2 record, per GATE).
· Attacks: (1) assembly: L1 applied to `generatorSpaceπ` with fibre dichotomy from L12 +
(L7 over fields); universality composes L5 (generator scheme commutes with base change) with
L1's universal property + 6.1.1 both ways — the leaf inherits L7's gate; (2) `Z` need NOT be
"finitely many equations" in the statement (KM's extra info) — project locus conventions
(T-D14/15/16) already drop it; (3) hdeg is needed so that base changes stay rank-`N`
(`degree` is stable along the PROVEN divisor `baseChange`).
· Provability: assembly, gated through L7. LOC: KM ~15 lines ⇒ Lean 200–300.

### Block D — [N-Isog] (KM 6.5) — review-Q8 named block

**[L14] `NIsogenyStructure` (structure, REAL) + `smul_eq_zero` + `pointSubgroup_le_torsion`
(PROVED) + `GammaZeroStructure.toNIsogeny` (REAL) — KM 6.5 (p. 164) + 1.4.2**
· Match: "[N-Isog](E/S) = set of flf subgroup-schemes `G ⊂ E[N]` of rank N" ↦ the structure
(subgroup + HasRank N); the `⊆ E[N]` clause is DERIVED (Oort–Tate/KM 1.4.2 through the
registered BB-DELIGNE box — no new box), as KM itself remarks.
· Attacks: (1) datum vs predicate: `[N-Isog]` classifies subgroup schemes (Type), mirroring
`GammaZeroStructure` — the moduli functor quantifies over it; (2) rank as `HasRank` predicate
field matches T-SG1's design (jumping-rank exclusion is intended: KM's "of rank N" is global);
(3) the containment is stated at point level (`pointSubgroup ≤`) not subscheme level —
sufficient for kernels-of-isogeny bookkeeping; the scheme-level factorisation through
`E.torsion N` is a Phase-2 corollary of `torsionι_factors_iff` (same proof shape).
· Status: **compiled; `pointSubgroup_le_torsion` PROVED** (sorryAx transitively from
BB-DELIGNE upstream only).

**[L15] `exists_nIsogSpace` — KM 6.5.1 (p. 165)**
· Quote §1/6.5. · Match: "relatively representable … finite over (Ell)" ↦ RR-only: finite
`w : W ⟶ S` + per-`t` classification of `NIsogenyStructure (E.baseChange t) N`.
· Attacks: (1) **[NISOG-GRASS]**: mathlib has `RingTheory/Grassmannian` (module-quotient
functor) but NO relative Grassmannian scheme — the ambient projective scheme is a genuine
gap; the closed bi-ideal condition on the universal quotient is then Useful-Lemma-type
vanishing (in-project patterns); (2) the per-`t` `Nonempty (≃)` spelling defers the
base-change naturality of the family `e_t` to the construction ticket (T-W8 precedent;
recorded — the honest RR statement needs it); (3) finiteness: KM's fibre count is FIBREWISE
over `k̄` (three cases, incl. the `n+1` ordinary subgroups) — it needs `Gᶜᵒⁿⁿ × Gᵉᵗ`
splitting over perfect fields, a [BB-DIFF]-adjacent input; flagged inside the gate.
· Provability: **GATE [NISOG-GRASS]** (+ fibrewise count sub-leaf). LOC: KM ~30 lines ⇒
Lean 600+ post-gate (Grassmannian itself is ForMathlib-scale).

### Block E — standard cyclic subgroups (KM 6.7.2–6.7.5)

**[L16] `exists_standardCyclicDivisor` — KM 6.7.2 (p. 167)**
· Quote §1/6.7.2 + 5.5.7(2). · Match: `G_d` ↦ ∃ divisor with (i) cyclic of order `d`,
(ii) `≤ D`, (iii) raw + (iv) parametric generator descriptions — clause (iv) doubles as the
DS-style base-change pin; KM's "may be described … in terms of ANY generator" is the ∀ in
(iii)/(iv).
· Attacks: (1) `G_d ≠ G[d]`: for `G = Ker Fⁿ` supersingular, `G[pᵐ] = Ker F^min(n,2m)` has
rank `p^min(n,2m) ≠ pᵐ` (`m < n`) — kernel-of-[d] is the WRONG object; `G_d` = image of
`[N/d]`, only fppf-descent defines it globally (this kills the "just intersect with E[d]"
shortcut); (2) existence-by-descent needs gluing a divisor from an fppf cover with descent
datum from uniqueness — [T-D10-FPPF]; the well-definedness (`G_d = G_d′`) is KM's
(ii)+(iii)+(iv) pipeline — [KM-FMT-FLAT] + in-project `exists_incidenceLocusEQ`;
(3) KM 5.5.7(2) ("(N/d)P has exact order d") is itself a Ch. 5 universal-case theorem —
folded into the same gate, quoted verbatim §1; (4) `d = N` and `d = 1` are honest instances
(identity subgroup / zero divisor `[0]`).
· Provability: **GATES [T-D10-FPPF] + [KM-FMT-FLAT]**; the ℤ[1/N] case is elementary.
· LOC: KM ~20 lines ⇒ Lean 300–450 post-gates.

**[L17] `standardCyclicDivisor` + `standardCyclicSubgroup` (defs, REAL) + 4 pins (PROVED
from `choose_spec`)** — status: **compiled**. The subgroup-scheme register goes through the
PROVEN `ofRelEffCartierDiv` with the `IsSubgroup` conjunct of the cyclicity pin.

**[L18] `standardCyclicDivisor_unique` — KM 6.7.2's `G_d = G_d′` step**
· Attacks: (1) fppf-descent of an ideal equality along a cover that admits a generator
(exists by `hG`) — [T-D10-FPPF] cleanly isolated; (2) needs only clause (iv) of both
candidates; (3) equality as divisors via `RelEffCartierDiv.ext` (ideal-level, PROVEN
pattern). · Provability: **GATE [T-D10-FPPF]**. LOC 80–150.

**[L19] `standardCyclicDivisor_trans` — KM 6.7.4 third clause, within `E` (p. 169)**
· Quote §1/6.7.4. · Attacks: (1) both sides satisfy L16-(iv) for `D` with exponent
`(N/d′)(d′/d) = N/d` — uniqueness (L18) closes it, PROVIDED the generator bookkeeping
`(N/d′)•P₀` generates `D_{d′}` (pin) and `(d′/d)•((N/d′)•P₀) = (N/d)•P₀` (smul arithmetic);
(2) instance plumbing `NeZero d/d′` explicit — instance search cannot read `hdd'`;
(3) KM proves it by (iii)+(iv) instead — our route through L18 is shorter and equivalent
(recorded deviation: same statement, proof by uniqueness rather than by locus).
· Provability: L16+L18 assembly (+[KM-FMT-FLAT] transitively). LOC 100–160.

**[L20] `orderDivisor_ideal_eq_prod_primeOrderDivisor` — KM 6.7.5 (pp. 169–170),
generator-local form**
· Quote §1/6.7.5. · Match: KM's fppf-local check "the assertion is obvious" IS this
identity; the global Cartier-divisor statement follows by fppf descent of ideal equality
(part of [T-D10-FPPF], recorded).
· Attacks: (1) the content is the multiset partition `ℤ/N = ⊔_{d∣N} {b·(N/d) : (b,d)=1}`
(Gauss `Σ_{d∣N} φ(d) = N`, mathlib `Nat.sum_totient`) + commutativity/reindexing of the
`Finset.prod` of section ideals — no moduli input; (2) `hkill` is REQUIRED (representative
sets `{1..N}` vs `{b(N/d) ∈ [0,N)}` differ at `N ≡ 0`) — cyclicity is NOT needed (stronger
lemma than KM's, deliberately); (3) `attach`+`letI` supplies per-divisor `NeZero`
(`Nat.pos_of_mem_divisors`); (4) may need a small `sectionsDivisor` reindexing lemma in
CartierDivisor.lean — if so, that addition goes through its own cleanup-scale ticket, NOT
this file (file discipline).
· Provability: **dischargeable NOW** (ZMod arithmetic + sectionsDivisor ideal product).
· LOC: KM 10 lines ⇒ Lean 200–300 (Finset/ZMod bookkeeping).

### Block F — the N-isogeny E → E/C ([T-G3D-INFRA]-gated; DS block)

**[L21] `quotientCurve` (DS-NISOG-1), `quotientHom` (DS-NISOG-2) + pins `quotientHom_over`,
`quotientHom_isInvariant`, `quotientCurve_compat`, `pointMap_zero/add`,
`pointMap_eq_zero_iff`, `quotientHom_finite/flat/finrank`; `pointMap`/`pointMap_coe`
(REAL) — KM 6.7.6 (p. 170)**
· Quote §1/6.7.6. · Match: `E′ = E mod G_d` as an ELLIPTIC CURVE + `π` with `Ker π = G` —
KM uses both silently; the scheme-level half is [T-G3D-INFRA] (`quotient`/`quotientπ` +
universal property, already DS-registered in p0's file); these two defs are the curve
upgrade, tied to the gate by `quotientCurve_compat` (iso under the two quotient maps — NOT a
scheme equality; the construction may realise it as `rfl` but consumers must not assume so).
· Attacks: (1) the curve structure (zero section, group law, `LocallyWeierstrass`) is
genuinely extra data over the gate's coequalizer scheme — pretending `quotient` is a curve
would be a soundness hole; hence separate DS with its own construction ticket
[T-G3D-INFRA-CURVE] (owner: the T-G3d-infra stream, post-Piece-3); (2) NOT gated on the
`E[N]`-finite-étale linchpin — inputs are `G`'s own finite/flat/lfp fields (same as the
scheme gate); (3) `pointMap` is REAL (composition; over-ness from the `_over` pin) so all
Ch.-6 statements can be written now; its group pins + the kernel pin `pointMap_eq_zero_iff`
(`Ker π = G`) are exactly what 6.7.4/6.7.11 consume; (4) **base-change pin gap (DS rule
iii)**: a `quotientCurve_baseChange` compatibility pin is REQUIRED by the register rule and
is deliberately deferred to the construction ticket (the `(E.baseChange g).E` spelling swamp
— T-SG1b's blocker); recorded as an obligation, and no skeleton statement depends on it
(6.7.4's generator clause is stated in raw global form for exactly this reason).
· Provability: **GATE [T-G3D-INFRA] (+ [T-G3D-INFRA-CURVE])**.
· LOC: interface done here; construction = the gate's stream.

### Block G — standard factorization theory (KM 6.7.4, 6.7.8, 6.7.11)

**[L22] `exists_imageDivisor` — KM 6.7.4 (p. 169), first two clauses**
· Quote §1/6.7.4. · Match: `G′ = G mod G_d` cyclic of order `N/d` + "its image `P′`
generates `G′`" ↦ ∃ divisor on `quotientCurve` with cyclicity + the generator-image clause
along ANY raw global generator (`pointMap P₀`).
· Attacks: (1) the image subgroup has no constructive definition without pushforward-of-
divisor API — the ∃ packages KM's own characterisation (KM constructs it fppf-locally as
the divisor of `π(aP)`s and glues); (2) the raw global-generator clause avoids the
quotientCurve-baseChange pin (L21 attack 4) — the fppf-parametric form follows downstream
by applying the theorem after base change ONCE the base-change pin exists (Phase-2, recorded);
(3) hypothesis `NeZero (N/d)` explicit (instance search can't see `hd`); (4) degree
bookkeeping: cyclic-of-order-`N/d` already forces degree `N/d` via `IsGammaZeroFppf`'s
`degree` conjunct — no separate rank clause needed.
· Provability: **GATES [T-G3D-INFRA] + [KM-FMT-FLAT]** (KM's (ii)–(iv) pipeline).
· LOC: KM ~18 lines ⇒ Lean 250–400 post-gates.

**[L23] `imageDivisor` (def, REAL) + 2 pins (PROVED from `choose_spec`)** — **compiled**.
(6.7.4's transitivity-in-the-quotient clause `G_{d′}/G_d = (G/G_d)_{d′/d}` needs
divisor-image vocabulary on the quotient curve — Phase-2 leaf [NISOG-P2-QTRANS], documented,
not stated.)

**[L24] `generator_iff_pointMap_generator` — KM 6.7.11(2) Backing-up (pp. 173–175)**
· Quote §1/6.7.11. · Match: `P` generates `Ker π` ⟺ `π_d P` generates `Ker π′` under
same-prime-factors, at the raw generator register (order + ideal identities on both sides).
6.7.11(1) is NOT a separate leaf: its two clauses are literally the pins
`standardCyclicDivisor_generator_spec` (the `(N/d)P` half) and `imageDivisor_generator_spec`
(the `π_d P` half) — the correspondence is recorded here.
· Attacks: (1) the ⟸ is the content (KM's cartesian-diagram claim); KM's own proof is
(ii) `[Γ₀(N)]` flat over ℤ, (iii) obvious over `ℤ[1/N]`, (iv) Useful Lemma on `Ker π`,
`(Ker π)^×`, and the fibre product — in-project (iv) = `exists_incidenceLocusEQ` +
finiteness of the fibre product (`π_d` finite flat pin × generator scheme finite flat, L7);
(2) same-prime-factors is sharp (KM 5.5.8's standing hypothesis; `N = pq`, `d = p`
counterexample shape — `0` generates order-`q` quotient never forces `0` to generate `G`);
(3) `hPD` (P lies on D) mirrors KM's `P ∈ (Ker π)(S)` and is needed — exact order `N` alone
admits points on OTHER cyclic subgroups.
· Provability: **GATES [T-G3D-INFRA] + [KM-FMT-FLAT]** (+L7 for the finite-flatness of
`(Ker π′)^×`). LOC: KM ~30 lines ⇒ Lean 350–500 post-gates.

**[L25] `isGammaZeroFppf_subdivisor_of_invertible` — KM 6.7.8 (pp. 171–172), `d₂`-invertible
case**
· Quote §1/6.7.8. · Match: kernel-level form of (1)⟹(2),(3): `D` cyclic of order `d₁d₂`,
`D₁ ≤ D` any rank-`d₁` subgroup subdivisor (= `Ker π₁` of a factorization), `d₂` invertible
(KM's "automatic" étale case) ⟹ `D₁` cyclic AND standard. The image-cyclicity half of (2)
then follows from L22 applied to the standard subgroup.
· Attacks: (1) KM's pivot is (1.11.2) — surjectivity of the induced generator map against
`0 → Ker π₁ → G → Ker π₂ → 0` — a Ch. 1 gate with no project analogue ([KM-1.11.2]);
(2) invertibility cannot be dropped on this route: uniqueness of the order-`d₁` subgroup of
a cyclic `d₁d₂`-group fails in char `p ∣ d₁` (e.g. `E[p] ⊇ Ker F, μ_p` split-ordinary) —
KM's étale-general form (π₂ étale) is the BB-DIFF-adjacent Phase-2 leaf [NISOG-P2-ETALE]
(gate in-flight, deliberately deferred); (3) `NeZero (d₁*d₂)` instance explicit — mul
instances don't fire on variables.
· Provability: **GATES [KM-1.11.2] + [T-D10-FPPF]**. LOC: KM ~35 lines ⇒ Lean 300–450.

### Block H — headline assemblies (KM 6.8.7, 6.6.1-core)

**[L26] `isGammaZeroFppf_of_squarefree` — KM 6.8.7 (p. 183)**
· Quote §1/6.8.7. · Match: "every N-isogeny is cyclic" ↦ any rank-`N` subgroup divisor is
`IsGammaZeroFppf`.
· Attacks: (1) KM's route: (ii) `[N-Isog]` flat/ℤ [KM-FMT-FLAT], (iii) over `ℤ[1/N]` "an
abelian group of square-free order is cyclic" (mathlib group theory — the fibrewise input;
exact lemma name to be hunted at discharge: the `IsCyclic`-from-squarefree-order family),
(iv) the cyclicity locus = **L13**; (2) squarefree is sharp — KM 6.8.8 ([pⁿ-Isog] not
normal, `n ≥ 2`) forbids drift to general `N`; (3) char `p ∣ N` honesty: `Ker F` IS cyclic
with Drinfeld generator `0` — consistent with the fppf record (the surrogate's char-`p`
defect was the T-D10 adversarial fix).
· Provability: **GATE [KM-FMT-FLAT]** + L13. LOC: KM ~12 lines ⇒ Lean 150–250.

**[L27] `exists_gammaZeroSpace` — KM 6.6.1 RR-core (p. 166)**
· Quote §1/6.6. · Match: "[Γ₀(N)] relatively represented by the closed subscheme of
[N-Isog]_{E/S} over which the universal N-isogeny is cyclic" ↦ finite classifier of
`GammaZeroStructure` (T-SG2 record — the GATE demands exactly this target).
· Attacks: (1) assembly = L15's space + L13's locus applied to the universal datum over it —
inherits BOTH gates; (2) same per-`t`-equivalence caveat as L15; (3) the closed-immersion
relation between the two spaces (`W_{Γ₀} ↪ W_{NIsog}`) is part of the construction, recorded
for the ticket. · Provability: assembly (L15 ∘ L13). LOC 150–250 post-gates.

---

## 3. DATA-SORRY candidates (prominent, per the plan.md register rule)

| ID | Declaration | File | Construction ticket | Pinned down by (shipped in skeleton) |
|----|-------------|------|---------------------|--------------------------------------|
| **DS-NISOG-1** | `FiniteLocallyFreeSubgroup.quotientCurve` | GroupScheme/NIsogeny.lean | **[T-G3D-INFRA-CURVE]** (extension of p0's [T-G3d-infra]; build only when its Piece 3 lands; never built by this stream) | `quotientCurve_compat` (total space ≅ the gate's `G.quotient` under both quotient maps), `quotientHom_over` (its `π` receives the isogeny), `pointMap_zero`/`pointMap_add` (group structure pinned at point level); **base-change pin deliberately deferred to the construction ticket** (obligation recorded, L21 attack 4; no skeleton statement depends on it) |
| **DS-NISOG-2** | `FiniteLocallyFreeSubgroup.quotientHom` | GroupScheme/NIsogeny.lean | [T-G3D-INFRA-CURVE] (same) | `quotientHom_over`, `quotientHom_isInvariant` (ties to the gate's `IsInvariant` vocabulary), `quotientCurve_compat` (equals `quotientπ` up to the pinned iso), `pointMap_eq_zero_iff` (**Ker π = G**, the kernel spec), `quotientHom_finite`/`_flat`/`_finrank` (isogeny of degree rank `G`) |

**DS-adjacent (NOT register entries — theorem-level sorries with real `choose` data, T-W8
precedent)**: `generatorSpace(ι/π)` ⇐ `exists_generatorLocus` [L3];
`standardCyclicDivisor`/`standardCyclicSubgroup` ⇐ `exists_standardCyclicDivisor` [L16]
(clause (iv) is the base-change spec); `imageDivisor` ⇐ `exists_imageDivisor` [L22]. Each
def's pins are its `choose_spec` projections, all compiled sorry-free.

## 4. Gate ledger

| Gate | What | Status/owner |
|------|------|--------------|
| [T-G3D-INFRA] (+`-CURVE`) | quotient `E/G` scheme + curve structure + kernel spec | p0's active stream (v10.35: reduced to the coequalizer scheme, Piece 3); curve half = new sub-ticket this artifact names |
| [KM-FMT-FLAT] | `[Γ₁(N)]`/`[Γ₀(N)]`/`[N-Isog]` flat over ℤ (KM 5.1.1/6.6.1/6.8.1) — powers every universal-case reduction | representability stream (T-E9/T-H9 lineage); the single most-shared gate (L9, L16, L19, L22, L24, L26) |
| [KM-62-63-HOMOG] | Axiomatic Isomorphism Thm 6.2.1 + formal-group determinant 6.3 | unowned; needs KM Ch. 5 deformation infrastructure (5.1.1/5.3/5.4) |
| [T-D10-FPPF] | fppf descent of divisor identities/cyclicity; descent-glue of divisors | T-D10's proof layer (⧗-lifted, dispatchable) |
| [NISOG-GRASS] | relative Grassmannian of quotients (scheme) | mathlib gap (only `RingTheory/Grassmannian`); ForMathlib-scale |
| [KM-1.11.2] | generator surjectivity across exact sequences (KM Ch. 1) | unowned; small, self-contained Ch. 1 leaf |
| BB-DIFF (in-flight) | étale-general 6.7.8 / `Gᶜᵒⁿⁿ × Gᵉᵗ` in 6.5.1's fibre count | P3b3's MASTER stream; Phase-2 leaves only — nothing in the skeleton waits on it |

## 5. Milestones / dispatch order

1. **M1 (dischargeable NOW, no gates)**: L3 `exists_generatorLocus` (first act) → L5 →
   L6 (+ mathlib `one_le_finrank_iff_surjective`) → L20 (partition identity) → L1
   (flattening, ForMathlib-flavoured). Outcome: `G^×` fully live, 6.1.1(⟸) proven,
   6.7.5-local proven — the generator-scheme layer stands on proven project machinery.
2. **M2 (gated on [T-D10-FPPF] alone)**: L18, L12; then L16's glue half.
3. **M3 (gated on [KM-FMT-FLAT])**: L9, L16-complete, L19, L26 (with L13), L22, L24.
4. **M4 (gated on [KM-62-63-HOMOG])**: L7, L10, L11 → completes 6.1.1 and L13 → T-SG3 done.
5. **M5 (gated on [T-G3D-INFRA-CURVE])**: DS-NISOG-1/2 constructed, L21 pins discharged;
   then Block G fully provable (with M3).
6. **M6 (gated on [NISOG-GRASS])**: L15 → L27 (Γ₀ classifier).
7. **Phase-2 board-only leaves**: [NISOG-P2-DUAL] (6.7.9, needs dual isogenies),
   [NISOG-P2-COPRIME] (6.7.10), [NISOG-P2-CRIT] (6.7.12/13), [NISOG-P2-CHAIN] (6.7.14/15),
   [NISOG-P2-ETALE] (6.7.8 étale-general, BB-DIFF), [NISOG-P2-QTRANS] (6.7.4 third clause in
   the quotient), [L1-gen] (6.4.3 general `≤ n` form, ForMathlib).

## 6. Report-milestone

The stream's headline reportable result: **T-SG3 discharged** (`exists_cyclicityLocus`
sorry-free) together with **6.1.1(⟸) + the generator-scheme layer** — "cyclicity of a
rank-N subgroup divisor is a closed condition on the base, witnessed by the finite
locally-free-of-rank-φ(N) locus of its scheme of generators". Everything through M1 is
claimable without ANY external gate.
