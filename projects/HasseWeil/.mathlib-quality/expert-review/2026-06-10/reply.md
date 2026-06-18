# Reviewer reply — round 24 (2026-06-10)

## Verdict
Route W is the right next proof target. Cleanest proof of the Wall = generic-fibre route via
"separable finite extension of Dedekind domains is unramified outside finitely many primes";
cheapest implementation = the DIFFERENT IDEAL (already in the library). Do NOT try Galois
normality/surjectivity first (circular without the count, as T4/T7 already identify).

## Q1 — Route W + cheapest a.e.-unramifiedness
Use route W; use the different. Proof shape:
1. Choose an affine open U₂ ⊂ E₂ excluding a finite bad set (O, poles/denominators of the
   coordinate witness, places where the integral model isn't the right finite Dedekind
   extension). A = O(U₂); B = integral closure of A in K(E₁). DO NOT require a global
   affine CoordHom — only a witness on a good affine open (avoids the old CoordHom problem).
2. Frac(B)/Frac(A) finite separable ⟹ the different 𝔇_{B/A} is a NONZERO ideal of B.
3. 𝔮 ⊂ A outside the contractions of primes dividing 𝔇_{B/A} ⟹ every 𝔓 | 𝔮 unramified (e = 1).
4. Over K̄ all residue degrees are 1 ⟹ deg φ = Σ_{𝔓|𝔮} e·f = #{𝔓 : 𝔓 | 𝔮}.
5. Point–place dictionary: primes over 𝔮_Q ↔ fibre φ⁻¹(Q) ⟹ #φ⁻¹(Q) = deg φ off the bad set.
6. T2 (fibre torsors) transports to the fibre over O ⟹ #ker φ = deg φ.
Different vs discriminant vs derivative: use the DIFFERENT (designed for exactly this:
ramified ⟹ divides 𝔇; support finite since 𝔇 ≠ 0 in a Dedekind domain). Discriminant =
primitive-element + denominator bookkeeping; derivative = same proof, local form, fallback only.
Pitfalls (all bookkeeping): no global CoordHom (localize!); make good-set nonemptiness explicit
(infinite torsion over K̄ suffices); exclude O (route W needs one FINITE good fibre); the
different lives in B — bad primes of A are CONTRACTIONS of primes dividing it, plus
localization exclusions.

## Q2 — shortcut? NO.
Galois/translation route circular before the count (surjectivity of ker→Aut, normality, or
fixed-field equality each ≡ the count unless quotient curves are built). Duality/degree-pairing
bootstrap doesn't help: φ̂φ = [deg φ] is what the dual construction is trying to OBTAIN.
The clean chain: separable finite ⟹ unramified a.e. ⟹ one good fibre has deg points ⟹
torsor transport ⟹ #ker = deg. That is route W.

## Q3 — ker(d) = K^p
General theorem: F perfect, L/F a one-variable function field ⟹ ker(d : L → Ω¹_{L/F}) = L^p.
(Nonperfect base: ker(d) = F·L^p instead.) Prove via p-basis / separating-parameter theory:
(1) separating transcendence element u, L/F(u) finite separable; (2) F perfect ⟹ u is a
p-basis of F(u); separable algebraic extensions preserve p-bases; (3) L = ⊕_{i=0}^{p-1} L^p uⁱ;
(4) z = Σ aᵢ^p uⁱ ⟹ dz = (Σ_{i≥1} i aᵢ^p u^{i-1}) du; independence of 1,…,u^{p-2} over L^p +
i ≠ 0 in F_p forces aᵢ = 0 (i > 0) ⟹ z ∈ L^p. If p-basis machinery is missing, the direct
F(x)[y] Weierstrass computation is the elliptic-curve-specific fallback (less reusable,
char-specific splits); x is a separating parameter in ALL characteristics. State the general
one-variable lemma if possible. Im(φ*) ⊆ K^p for inseparable φ: exactly via dφ* = 0 ⟹
Im ⊆ ker d = K^p. No shorter reusable route.

## Q4 — the twist: routine but REAL; do not dodge.
For deg_i = p^k with k not a multiple of [F_q:F_p], the factorization passes through E^(p^k),
not E. Build: E^(p^k) by raising coefficients to p^k; ellipticity/Δ ≠ 0 preserved; relative
Frobenius comorphism f ↦ f^(p^k); source/target tracking under composition;
(E^(p^a))^(p^b) ≅ E^(p^{a+b}); identification E^(p^k) ≅ E over F_q when p^k = q^m.
Special-case [n] and π, but not arbitrary inseparable isogenies. Do NOT hide the twist in
same-curve notation (that has repeatedly produced confusion in this project).

## Q5 — priorities + architecture
Order: (1) Route W NOW (a.e. unramified via the different; close #ker = deg separable);
(2) G1 (ker d = K^p) and G2 (the twist/factorization) so arbitrary inseparable isogenies
reduce cleanly; (3) canonicalise the dual package — long-term the library should expose
∃! φ̂, BOTH compositions φ̂φ = [deg φ] AND φφ̂ = [deg φ], deg φ̂ = deg φ, functoriality;
(4) only then the III.6.2 layer (φ̂̂ = φ, additivity). G3: witness-parametric duals are a
sound engineering pattern AS LONG AS witness inputs are named; not the final public shape —
the LMFDB-style catalogue wants a canonical `dual φ` with uniqueness (or an all-witnesses-
agree theorem). Fine for building; canonicalise at the end.
