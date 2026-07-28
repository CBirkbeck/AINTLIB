# WP campaign Phase 0 — paper §6 extraction (Step-1 prose proofs with locators)

Source: `refs/AdicSpaces/uniform_sheafy_domains_with_reduced_example.tex` ("Uniform sheafy
Tate domains that are not stably uniform", anonymous preprint). All line numbers below refer
to that file. §6 = `sec:rationally-reduced`, lines 655–1318. The first example (§1–§5) is the
FJP development already formalized on this branch (see `.mathlib-quality/fjp-cdvf/`); §5's
Lemma 5.1 (`lem:koszul`, lines 382–444) is delivered as `FiniteJet.GraphKoszul.*`.

Base conventions: `k` = complete discretely valued nonarchimedean field, valuation ring `k°`,
uniformizer `ϖ`, residue field `k̃` (lines 51). Lean: `[NontriviallyNormedField K]
[IsUltrametricDist K] [CompleteSpace K]` + `FiniteJetOver.Uniformizer K` (+ the `_of_dvr`
layer via `[IsDiscreteValuationRing 𝒪[K]]`), exactly as the FJP-CDVF campaign.

---

## The headline: Theorem `thm:rationally-reduced-example` (lines 668–683)

> "There is a complete Tate $k$-algebra $\mathcal A$ with the following properties.
> (1) $\mathcal A$ is a uniform, nonnoetherian integral domain and
> $\mathcal A^\circ=\mathcal A_0$ for the ring of definition displayed below.
> (2) The Huber pair $(\mathcal A,\mathcal A^\circ)$ is strongly sheafy.
> (3) The ring $\mathcal A$ is rationally stably reduced.
> (4) The genuine rational localization $\mathcal B=\mathcal A\langle W/\varpi\rangle$
> is an integral domain but is not uniform.
> In particular, failure of stable uniformity need not be caused by a nilpotent in the bad
> rational localization."

"Rationally stably reduced" (def, lines 662–666): every finite iterated rational
localization is reduced.

Assembly proof (lines 1299–1306): (1) = prop:parity-uniform-domain + prop:parity-nonnoetherian;
(2) = thm:parity-strongly-sheafy; (3) = thm:parity-rationally-reduced; (4) =
prop:weighted-chart-identification + prop:weighted-chart-domain-nonuniform.

Per the one-conclusion rule the Lean endpoints are separate declarations (uniform / domain /
nonnoetherian / 𝒜°=𝒜₀ / sheafy / strongly sheafy / reduced localizations / chart domain /
chart nonuniform / not stably uniform).

---

## §6.1 The construction (lines 685–737)

**ω and S** (lines 687–703). For finite-support ν ∈ ℕ^(I), I = ℕ_{>0}:

> "ω(ν)=∑_{n≥1, ν_n odd} n"                                     (eq:parity-weight, 689–691)
> "S={(a,ν)∈𝐍×𝐍^{(I)}: a≥ω(ν)}"                                  (eq:parity-monoid, 693–696)
> "The inequality ω(ν+μ)≤ω(ν)+ω(μ) shows that S is closed under addition. It is locally
> finite: a fixed element of S has only finitely many decompositions as a sum of two
> elements of S."                                                (697–703)

Prose proof of subadditivity (paper leaves it one-line; expansion): (ν+μ)_n is odd iff
exactly one of ν_n, μ_n is odd; hence {n : (ν+μ)_n odd} ⊆ {n : ν_n odd} ∪ {n : μ_n odd},
and ω(ν+μ) = ∑_{exactly one odd} n ≤ ω(ν)+ω(μ). Note the sharper *disjoint-support
additivity*: if ν and μ have disjoint supports then ω(ν+μ) = ω(ν)+ω(μ) — used silently at
eq:parity-factorization (777–781) and eq:tail-multiplication (1026–1029).

**The algebra** (lines 705–730):

> "Let k[S] be the monoid algebra with basis W^aU^ν ... Give it the Gauss norm
> ‖∑ c_{a,ν}W^aU^ν‖_G = sup|c_{a,ν}|. Its completion is
> 𝒜 = {∑_{(a,ν)∈S} c_{a,ν}W^aU^ν : c_{a,ν}∈k, c_{a,ν}→0}         (eq:parity-algebra, 711–718)
> where convergence to zero is over the discrete index set S. Local finiteness makes the
> coefficientwise convolution finite ... Put
> 𝒜₀ = {∑ c_{a,ν}W^aU^ν ∈ 𝒜 : c_{a,ν} ∈ k°}                       (eq:parity-ring-of-definition)
> Then 𝒜₀ is the closed unit ball ... ϖ-adically complete, and 𝒜 = 𝒜₀[1/ϖ]."

Lean model (support-subring convention of rem:formalization, lines 101–103): the ambient is
the restricted multivariate power-series ring over σ-many variables (σ = one W-variable plus
U_n, n ≥ 1; realized as σ = ℕ with 0 ↦ W, n ↦ U_n for n ≥ 1), radius 1:
`MvPowerSeries.Restricted K (fun _ : ℕ => 1)`. 𝒜 is its closed subalgebra of series whose
monomial support satisfies `ω(tail t) ≤ t 0`. The restricted condition "c → 0 over the
discrete index" is the vendored `IsRestrictedGauss` (cofinite-filter tendsto), which for
radius 1 says exactly `‖coeff t f‖ → 0` cofinitely.

**Finite heads** (lines 732–737):

> "𝒜_N = k⟨W,Y₁,Z₁,…,Y_N,Z_N⟩ / (Y_n² − W^{2n}Z_n)_{1≤n≤N}"    (eq:finite-head-presentation)

**Lemma `lem:finite-stage-normal-form`** (739–759), proof (761–787):

> "There is an isometric decomposition 𝒜_N ≅ ⊕^max_{ε∈{0,1}^N} k⟨W,Z₁,…,Z_N⟩ Y^ε.
> Under the substitution Y_n ↦ W^nU_n, Z_n ↦ U_n², this identifies 𝒜_N isometrically with
> the closed subalgebra of k⟨W,U₁,…,U_N⟩ supported on the monomials in (eq:parity-monoid)
> involving only U₁,…,U_N. The transition maps 𝒜_N → 𝒜_{N+1} are isometric, and
> 𝒜 = closure(⋃_N 𝒜_N)."                                          (eq:A-completion-of-heads)

Prose proof: monic division by Y_n²−W^{2n}Z_n gives unique normal forms
∑_ε f_ε(W,Z)Y^ε without raising Gauss norm; under the substitution the parity classes have
disjoint monomial supports (U_n-exponent ≡ ε_n mod 2), so norms add up as a max and the map
is isometric onto the support subalgebra; the factorization

> "W^aU^ν = W^{a−ω(ν)} ∏_{n=1}^N Y_n^{ε_n} Z_n^{q_n}   (ν_n = 2q_n+ε_n)"
>                                                       (eq:parity-factorization, 776–781)

shows the image is exactly the support algebra; every finite set of allowed monomials lies
in one stage and finite-support series are dense, giving eq:A-completion-of-heads.

**Lean route change (documented, in the spirit of rem:formalization).** We DEFINE 𝒜_N as the
support subalgebra (monomials with tail support ⊆ {1..N}) and never form the quotient
presentation. The mathematical content of lem:finite-stage-normal-form that downstream
proofs use is (i) the *unique factorization* eq:parity-factorization, i.e. 𝒜_N is a FREE
module over T_N := k⟨W,Z₁,…,Z_N⟩ (Z_n := U_n², a support subalgebra of 𝒜_N) with basis
{Y^ε := ∏(W^nU_n)^{ε_n}}_{ε∈{0,1}^N}, the decomposition being coefficientwise-isometric
because parity classes have disjoint supports; and (ii) the consequences: 𝒜_N noetherian
(finite module over noetherian T_N), strongly noetherian (same argument after adjoining
Tate variables), Banach-space structure. All are stated directly on the support side.
This mirrors the FJP campaign's divergence policy (final-report §8: same theorem, different
but equivalent route, documented).

**Prop `prop:parity-uniform-domain`** (789–794), proof (796–811):

> "The Gauss norm on the countable restricted Tate algebra k⟨W,U₁,U₂,…⟩ is multiplicative.
> Indeed, every nonzero restricted series attains its norm. After scaling two nonzero series
> to norm one, reduction modulo ϖ leaves two nonzero polynomials in k̃[W,U₁,U₂,…], and their
> product is nonzero. Scaling back proves multiplicativity. The support algebra 𝒜 embeds
> isometrically into this Tate algebra ... so its Gauss norm is also multiplicative and it
> is a domain. If x∈𝒜₀, all powers of x remain in 𝒜₀. If x∉𝒜₀, multiplicativity gives
> ‖x^m‖_G = ‖x‖_G^m, which is unbounded. Hence 𝒜° = 𝒜₀. Completeness and the Tate property
> follow from (eq:parity-algebra) and the topologically nilpotent unit ϖ."

Note: "attains its norm" uses discreteness of the value group of k (k is a CDVF) — the sup
of |c_{a,ν}| over a null family in a discretely-valued field is attained. The scaling step
likewise uses the uniformizer. The vendored `isAbsoluteValue` (CoramMvRestrictedNorm ~271)
proves Gauss multiplicativity for `MvPowerSeries.Restricted R c` under `[LinearOrder σ]`-type
hypotheses — to be checked against its exact signature; if it applies at σ = ℕ, c = 1 over K,
the paper's attain-the-norm argument is discharged wholesale.

Uniformity in the project's vocabulary: `TopologicalRing.IsUniform 𝒜` = boundedness of
`powerBoundedSubring 𝒜`; the proof shows powerBounded = unit ball 𝒜₀ (⊆ by norm
multiplicativity: ‖x‖>1 ⇒ ‖x^m‖=‖x‖^m unbounded; ⊇ since 𝒜₀ is a subring, submultiplicative).

**Prop `prop:parity-nonnoetherian`** (813–816), proof (817–834):

> "For m≥1, let I_m = (Z₁,…,Z_m) ⊂ 𝒜. There is a compatible family of norm-nonincreasing
> maps on the finite stages, and hence a bounded homomorphism ψ_m : 𝒜 → k⟨T⟩, which sends W
> and every Y_j to zero, sends Z_{m+1} to T, and sends every other Z_j to zero. The
> relations ... are preserved. The map ψ_m kills I_m but not Z_{m+1}. Therefore
> I₁ ⊊ I₂ ⊊ I₃ ⊊ ⋯, so 𝒜 is not noetherian."

Lean route (support model): define ψ_m coefficientwise on the support algebra: the monomial
W^aU^ν ↦ T^q if (a,ν) = (0, 2q·δ_{m+1}) (pure even powers of U_{m+1}), else 0.
Multiplicativity holds at the monoid level: the complement of {(0, 2q·δ_{m+1})} ∩ S is a
monoid ideal within S — if a summand has a>0, or a U-variable other than U_{m+1}, or an odd
U_{m+1}-exponent (odd forces a ≥ m+1 > 0 in S), then so does any sum containing it.
Boundedness: coefficientwise, ‖ψ_m f‖ ≤ ‖f‖. ψ_m(Z_j) = ψ_m(U_j²) = δ_{j,m+1}·T,
ψ_m(Z_{m+1}) = T ≠ 0. Since Z_j ∈ I_m for j ≤ m have ψ_m-image 0 and ideals map into ideals,
Z_{m+1} ∉ I_m. (Ideal-membership detail for the Lean proof: if Z_{m+1} = ∑ x_j Z_j then
applying ψ_m gives T = ∑ ψ_m(x_j)·0 = 0, contradiction — the paper's argument verbatim.)
A strictly increasing chain of ideals contradicts `IsNoetherianRing` via mathlib's
well-founded/fg characterization; alternatively the ideal (Z₁, Z₂, …) is not finitely
generated. Route note: the paper says "the relations are preserved" because its ψ_m is
defined through the presentation; in the support model ψ_m is defined directly and that
step disappears.

---

## §6.2 The bad chart (lines 836–943)

**The datum.** (line 838):
> "The datum (W;ϖ) is a genuine rational datum: the ideal (W,ϖ) is open because ϖ is a
> unit of 𝒜."

**ℬ₀ and ℬ** (eq:weighted-chart-lattice 839–848, eq:weighted-chart-norm 850–853):

> "ℬ₀ = {∑_{ν, d≥ω(ν)} b_{d,ν}X^dU^ν : b_{d,ν} ∈ ϖ^{ω(ν)}k°, ϖ^{−ω(ν)}b_{d,ν} → 0},
> with norm ‖∑ b_{d,ν}X^dU^ν‖_in = sup |ϖ|^{−ω(ν)}|b_{d,ν}|. The subadditivity
> (eq:omega-subadditive) shows that ℬ₀ is a ring. Put ℬ = ℬ₀[1/ϖ]."

**Prop `prop:weighted-chart-identification`** (857–866), proof (868–910):

> "There is a canonical isometric isomorphism 𝒜⟨W/ϖ⟩ ≅ ℬ, W ↦ ϖX. The graph ideal
> (W−ϖX) in 𝒜⟨X⟩ is closed, so no additional separated quotient is required."

Prose proof: On rings of definition define q₀ : 𝒜₀⟨X⟩ → ℬ₀ by q₀(W^aX^cU^ν) = ϖ^a X^{a+c}U^ν
(monomial-wise, extended coefficientwise). A k°-linear isometric section s (eq:weighted-section,
876–880): s(b X^dU^ν) = ϖ^{−ω(ν)}b · W^{ω(ν)}X^{d−ω(ν)}U^ν — well-defined by the divisibility
and support conditions in ℬ₀; q₀s = id. Kernel: for a monomial M = W^aX^cU^ν with
r = a−ω(ν) ≥ 0, the explicit division operator

> "D(M) = W^{ω(ν)}X^cU^ν ∑_{j=0}^{r−1} W^{r−1−j}(ϖX)^j  (r>0),  D(M)=0 (r=0), giving
> M − sq₀(M) = (W−ϖX)·D(M)"                     (eq:weighted-division-identity, 885–894)

with D norm-nonincreasing (all monomials still allowed, scalar coefficients of norm ≤ 1),
extending continuously to the c₀-completion; hence ker q₀ = (W−ϖX)𝒜₀⟨X⟩
(eq:weighted-kernel, 903–905) — closed since q₀ is a split surjection onto the complete ℬ₀;
the quotient norm equals ‖·‖_in (boundedness of q₀ one way, isometric section the other);
invert ϖ.

Lean shape: ℬ is defined as a WEIGHTED support subalgebra — better: as the space of
coefficient families {b : (allowed X,U-monomials) → K} with the weighted norm. Equivalent
concrete model: rescale coordinates b_{d,ν} = ϖ^{ω(ν)}·b'_{d,ν} identifies (ℬ, ‖·‖_in)
isometrically with the PLAIN support algebra {∑ b' X^dU^ν : d ≥ ω(ν), b' → 0} = the SAME
kind of algebra as 𝒜 with W renamed X — i.e. ℬ ≅ 𝒜 as normed rings (!), with a DIFFERENT
structure map from 𝒜 (W ↦ ϖX = ϖ·(image of W)). This is worth exploiting: ℬ-as-normed-ring
can literally be 𝒜 again (so domain-ness of ℬ = domain-ness of 𝒜, no new proof), with the
chart map 𝒜 → ℬ being the ϖ-rescaling W^aU^ν ↦ ϖ^a·W^{a... — CAREFUL: the rescaling
X^dU^ν ↦ (d,ν)-support is support-preserving; the ϖ^{ω(ν)}-divisibility exactly cancels.
Check: under b = ϖ^{ω(ν)}b', ‖·‖_in = sup|b'| = plain Gauss norm ✓; multiplication:
(ϖ^{ω(ν)}b')(ϖ^{ω(μ)}c') contributes to b'' at ν+μ with ϖ^{ω(ν)+ω(μ)} = ϖ^{ω(ν+μ)}·ϖ^{excess},
excess = ω(ν)+ω(μ)−ω(ν+μ) ≥ 0 — so under the rescaling, multiplication on ℬ is NOT the plain
support-algebra multiplication; it acquires ϖ^{excess} twist factors. So ℬ ≇ 𝒜 as rings via
this rescaling (only as Banach spaces). KEEP the paper's honest model: ℬ = weighted
coefficient space with untwisted (X,U)-monomial multiplication, weighted norm. The
nonuniformity witness needs the weighted norm anyway.
The identification with the project's presheafValue of the datum (W;ϖ) goes through the
project's rational-localization universal property / completion model, following the FJP
`Over/Chart.lean` pattern (rescaleRestricted / chartDatum) — the FJP case is the SAME datum
(W;ϖ) on a support subalgebra of a restricted series ring, so the pattern transfers.

**Prop `prop:weighted-chart-domain-nonuniform`** (912–914), proof (916–943):

> "The weighted convergence condition implies ordinary restricted convergence ... Hence
> coefficientwise inclusion gives an injective homomorphism ℬ ↪ k⟨X,U₁,U₂,…⟩. The target
> is a domain by the Gauss-norm argument used in prop:parity-uniform-domain; therefore ℬ
> is a domain."                                                     (917–926)
> "Inside 𝒜 write Y_n = W^nU_n ... and put T_n = ϖ^{−n}Y_n = X^nU_n ∈ ℬ. For r≥0,
> ‖T_n^{2r}‖_in = 1, ‖T_n^{2r+1}‖_in = |ϖ|^{−n}      (eq:Tn-power-norms, 933–938)
> Thus every T_n is power-bounded. The family (T_n)_{n≥1} is not bounded: if ϖ^N T_n ∈ ℬ₀,
> then the coefficient of X^nU_n must be divisible by ϖ^n, which forces N ≥ n. No fixed N
> works for all n. Hence ℬ° is unbounded and ℬ is not uniform."     (939–943)

Note T_n = X^nU_n as an element of ℬ: coefficient b_{n,δ_n} = ϖ^{... wait: T_n = ϖ^{−n}·(image
of Y_n) — in the weighted model, T_n is the monomial X^nU_n with coefficient 1; its ‖·‖_in is
|ϖ|^{−ω(δ_n)}·|1| = |ϖ|^{−n}. Powers: T_n^{2r} = X^{2rn}U_n^{2r}: ω(2r·δ_n)=0 (even), norm
|1| = 1 ✓; T_n^{2r+1} = X^{(2r+1)n}U_n^{2r+1}: ω = n, norm |ϖ|^{−n} ✓. Power-bounded: the
set of powers has norm ≤ |ϖ|^{−n}, bounded ✓. Unboundedness of the family {T_n}: no ϖ^N·(all
T_n) ⊆ ℬ₀-lattice, since T_n needs ϖ^n. For the project's `IsUniform` refutation: exhibit
{T_n} ⊆ powerBoundedSubring ℬ and show it is not bounded (for every candidate bound/lattice
ϖ^{-r}ℬ₀' some T_n escapes) — mirrors FJP `not_isUniform_chart`'s structure (there: the
nilpotent line kQ; here: the family (T_n); both refute boundedness of ℬ°).

**Not stably uniform** (assembly): the datum (W;ϖ) is `IsRational` (span{W,ϖ} = ⊤ as ϖ is a
unit); presheafValue(𝒜,(W;ϖ)) ≅ ℬ nonuniform refutes `TopologicalRing.IsStablyUniform 𝒜`
exactly as FJP `not_isStablyUniform_JetA`.

---

## §6.3 Lemma `lem:small-perturbation` (949–966), proof (968–1010)

> "Let (E,E⁺) be a complete Tate Huber pair and choose a closed ring of definition
> E₀ ⊆ E⁺. Let α=(f₁,…,f_m;g) be a rational datum whose entries lie in E₀. Write d₀=g,
> d_i=f_i. Suppose that for some ℓ≥0 there are a₀,…,a_m ∈ E₀ with ϖ^ℓ = ∑ a_j d_j
> (eq:integral-bezout). Let d_j' ∈ E₀ satisfy d_j' − d_j ∈ ϖ^{ℓ+1}E₀, and write
> α'=(f₁',…,f_m';g'). Then α' is a rational datum, α and α' define the same rational
> subset of Spa(E,E⁺), and their completed rational localizations are canonically
> isomorphic."

Prose proof (paper's, 968–1010): (i) ∑a_j d_j' = ϖ^ℓ(1+ϖH), H ∈ E₀; 1+ϖH is a unit of E₀
(geometric series converges ϖ-adically), so the primed datum has an integral Bezout relation
⇒ open/rational. (ii) Same rational subset: at a point x of the α-subset, |ϖ|^ℓ ≤ |g(x)|
(valuation ≤1 on E₀ + Bezout + ultrametric), and |d_j'−d_j|(x) ≤ |ϖ|^{ℓ+1} < |g(x)| forces
|g'(x)|=|g(x)| and |f_i'(x)| ≤ max(|f_i(x)|, |ϖ|^{ℓ+1}) ≤ |g(x)| = |g'(x)|; symmetric
argument for the converse. (iii) Isomorphic localizations: q := ϖ^ℓ/g = a₀+∑a_i(f_i/g) ∈
E_α°; g'/g = 1+ϖh₀q is a 1-unit with power-bounded inverse (geometric series in a bounded
subring after adjoining finitely many power-bounded elements); f_i'/g' =
(f_i/g+ϖh_i q)/(1+ϖh₀q) is power-bounded; universal property of E_{α'} gives E_{α'} → E_α;
symmetrically E_α → E_{α'}; composites fix E, so by universal-property uniqueness they are
mutually inverse.

Lean interface: statement over the project's `RationalLocData` + `presheafValue` + its
universal property (recon: exact form of the UP in Presheaf.lean). Two conclusions split:
(a) same rational subset (`rationalOpen α = rationalOpen α'`), (b) a canonical
`presheafValue α ≃ presheafValue α'` (continuous ring iso compatible with the canonical
maps). This lemma is stated for a general complete Tate ring E with a topologically
nilpotent unit ϖ — general infrastructure, not WP-specific.

---

## §6.4 Finite-head rational localization (1012–1127)

**Tail basis and decomposition** (1014–1034):

> "For a tail multi-index μ=(μ_n)_{n>N}, write μ_n = 2q_n+ε_n and put
> e_μ = ∏_{n>N} Y_n^{ε_n}Z_n^{q_n}                                (eq:tail-basis, 1017–1019)
> The finite-stage normal forms give an isometric Banach-module decomposition
> 𝒜 ≅ ⊕̂^{c₀}_μ 𝒜_N e_μ                                    (eq:tail-decomposition, 1021–1024)
> Multiplication is determined by
> e_μ e_λ = W^{ω(μ)+ω(λ)−ω(μ+λ)} e_{μ+λ}                  (eq:tail-multiplication, 1026–1029)
> Projection to the coefficient of e₀ is a norm-nonincreasing algebra retraction
> ρ_N : 𝒜 → 𝒜_N."                                          (eq:head-retraction, 1031–1034)

Support-model prose: e_μ is the monomial W^{ω(μ)}U^μ (μ supported in {n>N}); each (a,ν) ∈ S
splits uniquely as head monomial (a−ω(ν_{>N}), ν_{≤N}) ∈ S_N plus tail μ = ν_{>N} — using
DISJOINT-SUPPORT ADDITIVITY ω(ν) = ω(ν_{≤N})+ω(ν_{>N}); this is a norm-preserving bijection
of monomial bases S ≅ S_N × Tails_N, whence the isometric c₀-decomposition (an element's
μ-coefficient x_μ ∈ 𝒜_N reads off c_{(a'+ω(μ), ν'+μ)} at head monomial (a',ν')).
Multiplication rule: (W^{ω(μ)}U^μ)(W^{ω(λ)}U^λ) = W^{ω(μ)+ω(λ)}U^{μ+λ} =
W^{ω(μ)+ω(λ)−ω(μ+λ)}·e_{μ+λ} ✓ with excess exponent ≥ 0 by subadditivity. ρ_N = the
μ=0-coefficient map = "kill all monomials with tail content" — an algebra hom because the
tail-content monomials form a monoid ideal in S (sum of anything with a tail-supported
variable still has one), and norm-nonincreasing coefficientwise. (Same argument shape as
ψ_m.)

**Prop `prop:coefficientwise-localization`** (1036–1052), proof (1054–1095):

> "Let α be a rational datum in 𝒜_N, and put P = (𝒜_N)_α. There is a canonical topological
> algebra isomorphism 𝒜_α ≅ ⊕̂^{c₀}_μ P e_μ. It is natural for rational refinements
> represented in a finite head ... The same statement holds after increasing N."

Prose proof (1054–1095): R := 𝒜_N⟨T₁…T_m⟩, I := (gT_i−f_i) ⊂ R. Since 𝒜_N is affinoid
[strongly noetherian], the graph ideal I is closed and d₁ : R^m → I is strict — "the
degree-zero conclusion of lem:koszul" — so there is C with: every y ∈ I has a lift x ∈ R^m,
‖x‖ ≤ C‖y‖. [= FJP `exists_d1_lift_pow` over E = 𝒜_N.] Then 𝒜⟨T₁…T_m⟩ ≅ ⊕̂^{c₀}_μ R e_μ
(tail decomposition with head 𝒜_N⟨T⟩); the graph differential acts coefficientwise (the
relations lie in the head); its image is exactly ⊕̂^{c₀}_μ I e_μ — inclusion ⊆ clear; ⊇: for
a null family (y_μ) in I choose bounded lifts x_μ (‖x_μ‖ ≤ C‖y_μ‖), again null. Hence the
graph ideal over 𝒜 is closed and the quotient is computed coefficientwise:
⊕̂^{c₀}R e_μ / ⊕̂^{c₀}I e_μ ≅ ⊕̂^{c₀}(R/I) e_μ (eq:c0-quotient) as complete topological
modules and algebras; R/I = P. Naturality: all maps induced by the canonical graph
quotients; head-represented refinements act coefficientwise; presentation independence and
transitivity extend to iterated refinements and larger heads.

Lean note: "P = (𝒜_N)_α" and "𝒜_α" must each be identified with the PROJECT's
presheafValue (a completion). The paper's model E_α = P_E/J̄_E is the graph model
(eq:graph-model, §2 lines 172–175); for noetherian heads the 828b campaign's machinery
should already identify presheafValue(𝒜_N, α) with the closed-graph-ideal quotient (recon).
For 𝒜 itself, the SAME closedness-of-graph-ideal statement (proved here via the c₀
argument) feeds the identification presheafValue(𝒜,α) ≅ ⊕̂^{c₀}P e_μ through the project's
completion model: the c₀-sum is complete, receives 𝒜⟨T⟩/(closed ideal), and satisfies the
localization universal property.

**Cor `cor:finite-head-presentation`** (1097–1105), proof (1107–1127):

> "Every rational localization of 𝒜 is canonically isomorphic to a ring of the form
> ⊕̂^{c₀}_μ P e_μ, where P is a rational localization of some affinoid head 𝒜_N. Under this
> identification the inclusions obtained by enlarging the head have norm-nonincreasing
> algebra retractions, and their union is dense."

Prose proof: scale the datum into 𝒜₀; pick an integral Bezout relation ϖ^ℓ = ∑a_j d_j
(exists: the datum is rational and ϖ is a unit — a_j found in 𝒜₀ after scaling); by density
of ⋃𝒜_N (eq:A-completion-of-heads) approximate d_j by d_j' ∈ 𝒜_N ∩ 𝒜₀ with error in
ϖ^{ℓ+1}𝒜₀; small-perturbation lemma: same subset, isomorphic localization; applying ρ_N to
the primed Bezout relation shows the primed datum is rational already in 𝒜_N; apply
prop:coefficientwise-localization. Retractions/density: coefficient projection at head M ≥ N
+ finite tail truncation.

---

## §6.5 Theorem `thm:parity-strongly-sheafy` (1131–1133), proof (1135–1237)

> "The Huber pair (𝒜,𝒜°) is strongly sheafy."

Prose proof, in stages:

(1) *Rational-basis sheaf condition* (1136–1218). Let U ⊂ X = Spa(𝒜,𝒜°) be rational; by
cor:finite-head-presentation choose E = 𝒪_X(U) ≅ ⊕̂^{c₀}_μ P_M e_μ, P_M = (𝒜_M)_α. Let
E_U⁺ be the plus ring of the rational subspace (need not be E°); E₀ := ⊕̂^{c₀} P_{M,0} e_μ
is a closed ring of definition inside E_U⁺. Given a finite rational cover U = ⋃ U_i, choose
rational data for the U_i in (E,E_U⁺), scale into E₀, choose integral Bezout relations;
enlarge the head and use density + small-perturbation to replace all data by data in one
head lattice P_{M,0} without changing the U_i or their section rings; coefficient projection
of the Bezout relations shows the data are rational in P_M. Let V_i ⊂ Spa(P_M,P_M°) be the
corresponding rational domains.

(2) *The V_i cover Spa(P_M,P_M°)* (1169–1180): the inclusion P_M → E and coefficient
projection E → P_M are norm-nonincreasing and split each other; they induce a split
surjection Spa(E,E°) → Spa(P_M,P_M°); the maximal-pair spectrum Spa(E,E°) is a subspace of
Spa(E,E_U⁺) = U; the given cover restricts to a cover of Spa(E,E°), whose pieces are the
inverse images of the V_i; surjectivity transfers the covering property. [Careful point the
paper flags: avoid identifying U with the maximal-pair spectrum — wrong at higher-rank
points.]

(3) *Coefficientwise Čech gluing* (1182–1218): with P_{M,i} = 𝒪(V_i), P_{M,ij} = 𝒪(V_i∩V_j),
naturality of coefficientwise localization identifies 𝒪_X(U_i) ≅ ⊕̂^{c₀}P_{M,i}e_μ and
𝒪_X(U_i∩U_j) ≅ ⊕̂^{c₀}P_{M,ij}e_μ with coefficientwise restrictions. The affinoid P_M is
sheafy, so the equalizer map P_M → Eq(∏P_{M,i} ⇉ ∏P_{M,ij}) is a Banach-space isomorphism
(eq:head-cech, 1200–1205); ITS INVERSE IS BOUNDED — fix a bound C. A matching family
(x_i) with x_i = ∑_μ x_{i,μ}e_μ glues coefficientwise: for each μ, (x_{i,μ})_i is matching,
glues to x_μ ∈ P_M with ‖x_μ‖ ≤ C·max_i‖x_{i,μ}‖ (eq:coefficientwise-gluing-bound);
finiteness of the cover + null coefficient families ⇒ (x_μ) null ⇒ ∑x_μe_μ ∈ E is the
unique glued section; the same bound makes restriction a topological embedding.

(4) *Arbitrary opens* (1220–1226): the projective-limit argument from the last paragraph of
lem:sheaf-transfer's proof (§5, lines 629–633): rational subdomains of an open are
quasi-compact, finite subordinate rational covers glue by the basis result; the defining
projective-limit topology on arbitrary-open sections makes the inverse gluing map
continuous. [In the project this is expected to be packaged: IsLimitSheaf from
rational-basis sheafiness — recon: `isLimitSheaf_of_isSheafy` exists from the 828b
campaign.]

(5) *Strong sheafiness* (1228–1236): for auxiliary Tate variables V₁,…,V_s, isometrically
𝒜⟨V₁…V_s⟩ ≅ ⊕̂^{c₀}_μ 𝒜_N⟨V₁…V_s⟩e_μ (eq:strong-sheafy-decomposition); the heads remain
affinoid, retractions and perturbation unchanged, "the preceding proof applies verbatim";
hence every finite Tate extension is sheafy.

Lean design for (5): parametrize the whole §6.1/§6.4/§6.5 development by an auxiliary
finite free-variable count s (support condition ignores the s extra exponents): 𝒜^{(s)} :=
support algebra over σ = ℕ ⊕ Fin s; 𝒜 = 𝒜^{(0)}; heads 𝒜_N^{(s)}; the sheafiness proof is
stated once over (s, N). Then "strongly sheafy" = sheafiness of 𝒜^{(s)}-models for all s +
the identification of 𝒜^{(s)} with the project's Tate-extension of 𝒜 (nested-vs-flat
plumbing — its own leaf).

Bound-C provenance (the one analytic input): boundedness of the inverse of the head-Čech
equalizer iso. Route: the equalizer restriction map is a continuous bijection onto a closed
subspace of a finite product of Banach spaces (from head sheafiness = separation +
gluing + embedding, all in the 828b package at the head); open mapping /
`isStrictLinearMap_of_lift` (project BanachOMT — no-Baire bridge) upgrades to a bounded
inverse. Alternatively extract the bound directly from the strictness content of the 828b
proof at the head (recon which form is available).

---

## §6.6 Reducedness (1239–1297)

**Lemma `lem:formal-series-reduced`** (1241–1248), proof (1250–1261):

> "Let P be a reduced ring and let J be any index set. Define ℱ_J(P) = ∏_{μ∈𝐍^{(J)}} P U^μ
> with multiplication by coefficientwise finite convolution. Then ℱ_J(P) is reduced."

[ℱ_J(P) is exactly `MvPowerSeries J P`.] Prose proof: for finite J₀ ⊂ J, setting the
variables outside J₀ to zero gives τ_{J₀} : ℱ_J(P) → P[[U_j : j∈J₀]]; these jointly detect
all coefficients (any single μ has finite support). A finite-variable formal power-series
ring over reduced P is reduced: inject P → ∏_{𝔭∈Spec P} P/𝔭 (reduced ⇒ nilradical 0 ⇒
injective into product of domains), inducing an injection of power-series rings into a
product of P/𝔭[[U]]-domains [power series over a domain is a domain]. A nilpotent of
ℱ_J(P) dies under every τ_{J₀}, hence has all coefficients zero.
[Pure commutative algebra over arbitrary σ — absent from mathlib; elementary. Note the
finite case can also be done by induction on variables via `MvPowerSeries` ≅ iterated
`PowerSeries` + "PowerSeries over reduced is reduced" (coefficient induction), avoiding
Spec: for f with f² = 0 over reduced R, induct on the least nonzero coefficient — standard.
Choose whichever composes best in mathlib; the τ_{J₀} finite-detection layer is needed for
arbitrary J either way.]

**Theorem `thm:parity-rationally-reduced`** (1263–1265), proof (1267–1297):

> "Every finite iterated rational localization of 𝒜 is reduced."

Prose proof: "By transitivity of rational localization, it is enough to treat one rational
localization." [Iterated = single via transitivity of rational subsets/localizations —
needs a project notion; see design note below.] Write it as E ≅ ⊕̂^{c₀}_μ P e_μ, P = (𝒜_N)_α
(cor:finite-head-presentation). 𝒜_N is a domain (normal form / Gauss). "A rational
localization of a reduced affinoid algebra is reduced [BGR 7.3.2/10]; see also
[KedlayaAWS Remark 1.2.16]. Thus P is reduced." [THE WALL — classical input, its own
sub-project.] W is a non-zero-divisor in 𝒜_N; "Affinoid rational localization is
algebraically flat [BGR 7.3.2/6]; see also [ConradL15 Prop 15.1.1 proof]" — tensoring
0 → 𝒜_N →^W 𝒜_N with P shows W injective on P. [Lean: project `prop_8_30_flat_clean_proof`
= Wedhorn 8.30 flatness for strongly noetherian Tate rings, applied with V = whole space;
plus flatness preserves injectivity of ·W.] If P = 0 the conclusion is immediate. Define

> "Φ : E → ℱ_J(P), Φ(∑_μ x_μ e_μ) = ∑_μ W^{ω(μ)} x_μ U^μ    (eq:formal-embedding, 1286–1291)
> The multiplication rule (eq:tail-multiplication) makes Φ multiplicative. If Φ(∑x_μe_μ)=0,
> coefficient comparison gives W^{ω(μ)}x_μ = 0 for every μ. The W-regularity of P then
> gives x_μ = 0 ... so Φ is injective. By lem:formal-series-reduced the target is reduced;
> hence E is reduced."

[Φ additive+multiplicative: Φ(xy)_τ = ∑_{μ+λ=τ} W^{ω(μ)+ω(λ)−ω(τ)}x_μy_λ·W^{ω(τ)} =
W^{ω(τ)}·(xy)_τ ✓ — the excess powers of W absorb the twist; this is where the W-twisted
multiplication rule is exactly compensated. Ring hom into a ϖ-less FORMAL product — no
topology on the target, algebra-level map only; convergence is irrelevant since ℱ is a full
product.]

**Iterated-localization design note.** The paper reduces "finite iterated" to "single" by
transitivity. Project options (recon pending): (i) if the project has "a rational
localization of a rational localization is canonically a rational localization of the
base" (Huber transitivity), use it; (ii) otherwise define the iterated notion as a chain
of presheafValues and prove reducedness by INDUCTION: the induction step being
prop:coefficientwise-localization applied to E itself (E's rational data perturb into ITS
heads P_M — cor:finite-head-presentation's "same statement holds after increasing N" /
"union dense" clauses are exactly what makes E again a finite-head c₀-algebra with heads
P_M = localizations of 𝒜_M, and localizations-of-localizations of heads are again
localizations of heads by affinoid transitivity at the HEAD level, where the strongly
noetherian machinery lives). Route (ii) suggests the strongest design: prove the single-step
theorem in the form "presheafValue(E, β) is again of finite-head form with head a
localization of a head of E" for E of finite-head form — making the CLASS of finite-head
algebras the induction invariant. Decide after recon of what transitivity infrastructure
exists.

---

## External classical inputs cited by §6 (each must be formalized or routed around)

1. **BGR 7.3.2/10** (rational localization of reduced affinoid is reduced) — used for the
   heads at 1276–1277. NO formalization exists (project or mathlib). Sub-project; see
   decomposition. Candidate routes: (a) Serre-type argument via flat + CI structure of the
   specific heads; (b) char ≠ 2 generic étaleness of the quadratic tower; (c) uniformity
   route (reduced classical affinoid ⇒ stably uniform, BGR 6.2.4/1 + 7.3.2) — heavy.
2. **BGR 7.3.2/6 / Wedhorn 8.30** (affinoid rational localization flat) — DELIVERED:
   `prop_8_30_flat_clean_proof` (AuditCleanWrappers.lean) for strongly noetherian Tate.
3. **Huber 1994 Lem 2.3/2.4 via lem:koszul degree-0** (closed graph ideal + strict d₁ with
   bounded lifts over noetherian heads) — DELIVERED: `FiniteJet.GraphKoszul`
   (`koszulGraph_exact_strict_closed`, `exists_d1_lift_pow`).
4. **Huber sheafiness of strongly noetherian Tate rings (Wedhorn 8.28(b))** for the heads —
   DELIVERED: `isSheafyFor_of_stronglyNoetherianTate` (SheafyRing.lean).
5. **Stacks 009O sheaf-on-basis + projective-limit topology packaging** — expected
   DELIVERED in the project's IsLimitSheaf layer (`isLimitSheaf_of_isSheafy`); recon.
