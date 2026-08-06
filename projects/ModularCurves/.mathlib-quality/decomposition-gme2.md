# Worker decomposition — GME Chapter 2 chains (proofs read 2026-07-05)

*Source: Hida, GME (full text in `refs/`). Sections read WITH PROOFS: 2.2.1–2.2.6
(pp. 107–119), 2.3.1 start, 2.6.1(end)–2.6.4 (pp. 143–154). Cited-not-yet-read
infrastructure (in hand, read at ticket-cut): 1.6–1.8 (group schemes, Cartier duality,
quotients), 1.9.12, 1.10 (cohomology), 1.11 (descent), 2.1 (duality/RR = the RR box),
2.3.2 (coarse), 2.5 (Tate curves), 2.9.3 (irreducibility). KM locators given for
reconciliation when the full KM text arrives; GME is proof-sufficient on its own.*

**Convention pin (GME 2.2.1).** Hida's (E1–E3) definition: proper smooth curve, section,
fibre-by-fibre connected, `f_*Ω_{E/S} ≅ O_S` fibrewise (⟺ genus 1). (E3) is the
ω-form of the genus condition — once mathlib has relative `Ω¹` this is a THIRD
equivalent fibre condition to record next to ours (ticket T-A9 gains a second target).

**The RR box, precisely (owner: Riemann–Roch is the only box).**
BB-RR := GME 2.1.2 (Grothendieck–Serre duality for relative curves), 2.1.3 (RR),
2.1.6 (relative RR: `rank f_*L − rank f_*(L⁻¹⊗Ω) = 1 − g + deg L`). Nothing else may
be silently absorbed into the box; the cohomology facts below are the COH stream.

**COH stream targets, pinned by Hida's own uses:**
- COH-1 = GME Lemma 1.10.4 (cohomology-and-base-change exactness criterion for
  `T_i(F) = R^i f_*(L ⊗ f*F)`: `T₁` exact ⟹ `T₀` exact; `f_*L` locally free with
  `(f_*L)⊗k(s) ≅ f_*(L(s))`). [Grothendieck's Ch. III.12-style theory.]
- COH-2 = GME Cor 1.9.12: `Γ(E, O_E) = Γ(S, O_S)` for proper + fibre-connected
  (+reduced?) — check exact hypotheses at cut time (p. 69ff).
- COH-3 = `R^i f_*` existence + affine vanishing + LES (mathlib PRs #36345/#36218 —
  coordinate, do not build).

---

## Chain A6 — Abel & the group law (GME 2.2.1–2.2.2, Cor 2.2.5; discharges the
`abelEnrichment` canonicity project)

### A6.α = (2.15): `R¹f_*O_E ≅ O_S` (proof p. 107, transcribed)
Steps: `L := I([0])⁻¹`; SES `0 → O_E → L → O_S(≅L/O) → 0` [uses: `[0]` is an ECD —
D-curve.1 — and `L/O ≅ O_S` via degree-1 properness]; push forward: exactness of
`0 → f_*O → f_*L → O_S → R¹f_*O → 0`; kill `R¹f_*L`: fibrewise
`H¹(E_s, L(s)) ≅ H⁰(E_s, L(s)⁻¹⊗Ω)^∨ = 0` [RR-box: Serre duality; `deg Ω = 2g−2 = 0`
so `deg < 0` ⟹ no sections]; COH-1 twice (T₁ exact ⟹ T₀ exact; `f_*L` locally free,
rank 1 by relative RR [RR-box 2.1.6]); Nakayama on
`0 → (f_*O)⊗k → (f_*L)⊗k → k → (R¹f_*O)⊗k → 0` (all terms `k(s)`) ⟹ `f_*O → f_*L`
surjective ⟹ `f_*L ≅ f_*O_E ≅ O_S`. **Also yields: any fibre-degree-1 invertible L
has `f_*L ≅ O_S` locally and `R¹f_*L = 0`** (p. 108 remark — used by A6.γ).
- Lean shape: statement against mathlib's coming `R^i f_*` (COH-3); until then the
  chain is stated with the COH-1/2/3 statements as explicit hypotheses-in-file
  (sorried stream targets), never inlined assumptions.

### A6.β = Pic functors + locality (proof (2.17), p. 109)
`Pic_{E/S}(T) := Pic(E_T)/f_T^*Pic(T)`; `Pic^ν` by fibre degree. Locality of `Pic¹`:
the 0-section splits `Pic(E) = Ker(0^*) ⊕ Im(f^*)` ⟹ `Pic_{E/S}` is a subfunctor of
`Pic(E)` ⟹ Zariski-local. Lean: needs Pic of a SCHEME — mathlib gap (survey: only
Pic(ring); Raph-DG lane is Weil-divisor-side). Route: define `Pic(X)` as invertible
`O_X`-modules via mathlib `SheafOfModules` + locally-free-rank-1 (`LocallyFree.lean`
merged ✓) — ticket T-PIC0 (new, COH-adjacent stream; coordinate on Zulip: unclaimed
per survey). Fibre degree of an invertible sheaf: via pullback to fibres + degree on
curves-over-fields (HasseWeil divisor theory anchor).

### A6.γ = `ι : E(S) ≅ Pic¹(S)`, `P ↦ I(P)⁻¹` (proof p. 109, transcribed)
Surjectivity: `L ∈ Pic¹(S)`; by A6.α-remark `f_*L` loc. free rank 1; shrink: `f_*L ≅
O_S` with generator ℓ; SES pushforward pins `f_*(L/O) ≅ R¹f_*O ≅ O_S` fibrewise
(`0 → k ≅ k → k ≅ k → 0` count); so `(L,ℓ)` is a relative ECD of degree 1 = a section
[D-curve: KM 1.2.7]. Injectivity: reduce to `k̄`: `I(P) ≅ I(Q)` ⟹ meromorphic φ,
`div φ = P − Q` ⟹ `φ : E ≅ ℙ¹` contradiction [fibre anchor: HasseWeil function-field/
divisor theory has exactly this: degree-1 map ⟹ genus 0 — check
`HasseWeil.Foundation.Curves` for the ℙ¹-recognition lemma; else RR-box fibrewise].
Group transport: `Pic⁰` is a group functor; `E ≅ Pic¹ ≅ Pic⁰` (`⊗I(0)`).

### A6.δ = uniqueness + commutativity (Cor 2.2.5, proof pp. 118–119, transcribed)
Any group structure `a` with identity 0: `f_P(Q) := a(P,Q) − P` (minus = Abel group!)
is an automorphism fixing 0 ⟹ [Cor 2.2.2] a group hom ⟹ `f_P^*ω = λ(P)ω`;
`λ : E → 𝔾_m` morphism-of-functors ⟹ [key-lemma = Yoneda] scheme morphism; E proper
+ fibre-connected ⟹ λ constant on fibres; `Γ(E,O) = Γ(S,O)` [COH-2] ⟹ λ constant;
`λ(0)=1` ⟹ `λ ≡ 1` ⟹ `f_P` fixes `(E,ω)` ⟹ `f_P = id` [rigidity Cor 2.2.4 = E13
below] ⟹ `a(P,Q) = P + Q`.
- Cor 2.2.2 (endo `g` with `g(0)=0`, locally free ⟹ group hom; proof p. 109–110):
  `J(P) := ∧^r(g_*I(P))`, `J(P)⁻¹⊗I(0) ≅ g_*(I(P)⁻¹⊗I(0))`, faithfully-flat splitting
  of `g^*[g(P)]` into degree-1 divisors. HARD BIT HB-NORM: **norm/determinant of
  pushforward line bundles along a finite locally free morphism** (`∧^r g_*`) —
  ticket T-NORM0 (new; also the engine for the pairing chain C below and for
  full-sections↔charpoly). Mathlib: absent; buildable module-theoretically
  (`Module.Free` + `exteriorPower` ✓ exists).

## Chain A7 — Weierstrass embedding (GME 2.2.4–2.2.5, proofs pp. 111–115; discharges
T-A7 locally-Weierstrass + supplies T-A2/T-A3's smoothness content)

- A7.a formal parameter: smooth ⟹ étale `g : U → 𝔸¹` at 0 [mathlib standard-smooth
  presentations ✓]; `I([0])/I([0])² ≅ (T)/(T²)`; Nakayama ⟹ `Ô ≅ A[[T]]`; formal
  group `Φ(T₁,T₂)` [+HasseWeil FormalGroup REUSE — their `FormalGroupCorrespondence`];
  ω = (unit + h.o.t.)dT, normalise to `1 + O(T)`; "T mod T² adapted to ω" unique.
- A7.b ranks: `f_*I([0])^{−n}` locally free rank n (n ≥ 1): SES + fibrewise
  `deg(I([0])ⁿ⊗Ω) < 0` vanishing [RR-box] + COH-1; the surjection
  `f_*(L^n/O) ↠ R¹f_*O ≅ O_S`.
- A7.c coordinates: shrink S: `Γ(I⁻²) = A·1 + A·x`, `x = T⁻²(1+…)` unique up to
  `x ↦ x+a`; `Γ(I⁻³) ∋ y = −2T⁻³(1+…)` unique up to `y ↦ y+ax+b`; the SEVEN elements
  `1,x,y,x²,xy,y²,x³` in rank-6 `Γ(I⁻⁶)` give (2.18):
  `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` (pole-order bookkeeping in `A[[T]]`).
- A7.d embedding: `t ↦ (x(t),y(t),1)`: `E ↪ ℙ²_S = Proj(ℤ[X,Y,Z]) ×_ℤ S`, image =
  V(2.18) in `D₊(Z)`... plus the point at infinity; over ℤ[1/6] normalise to
  `y² = 4x³ − g₂x − g₃` (2.19) via the two variable changes (EQ1)/(EQ2).
- A7.e = T-A2/T-A3 content (converse, pp. 114–115): for `Δ ∈ A^×`,
  `E = Proj(A[X,Y,Z]/(Y²Z − 4X³ − g₂XZ² − g₃Z³))` is an elliptic curve, `0 = (0,1,0)`,
  `ω = dX/Y`; smoothness via the EIGHT equivalent conditions (p. 114 — the exact
  chartwise Jacobian recipe: `Ω_{B/A}` computed from `2YdY = F′dX`; chart
  `D₊(Y)`: `C = A[S,U]/(U − 4S³ + g₂SU² + g₃U³)`, `dU = 0` at 0, `dS` spans).
  **This replaces the glue-two-charts plan of T-A2 with Proj-of-one-graded-ring +
  chart analysis — adopt Hida's route** (mathlib has `Proj` ✓; Kenny Lau's staging
  repo has Proj base change / functorial ℙ² per survey — coordinate).
  General-(2.18) version (no 1/6) for the definition of record: same display before
  the (EQ1)/(EQ2) normalisations.

## Chain E12–E15 — M₁, rigidity, Legendre, ℰ₃ (GME 2.2.6–Thm 2.2.3, Ex. 2.2.1/2.2.2;
feeds KM-4.7/T-E5's bootstrap and T-E9's ℤ-glue)

- E12 (Thm 2.2.3): `P₁ : S ↦ [(E,ω)]` represented over ℤ[1/6] by
  `M₁ = Spec ℤ[1/6, g₂, g₃, Δ⁻¹]` — proof = A7 uniqueness of (g₂,g₃) given ω;
  universal curve `y² = 4x³ − g₂x − g₃`.
- E13 (Cor 2.2.4): `Aut_S(E,ω) = {1}` — one-liner from representability ("two
  distinct identifications φ^*(𝐄,ω) ≅ (E,ω)"). **The rigidity engine.**
- E14 (Ex. 2.2.1 Legendre, p. 117, proof transcribed): over ℤ[1/2]:
  normalise `y² = x³+a₂x²+a₄x+a₆`, `i(x,y)=(x,−y)` gives `[−1]`; `E[2]−{0} ≅
  Spec(A[X]/(F))` free rank 3; E[2] étale (distinct roots by smoothness);
  P'₂ (pairs P,Q ∈ E[2]−0 with x(P)=0, x(Q)=1) represented by
  `M'₂ = Spec ℤ[1/2, λ, (λ(λ−1))⁻¹]`, universal
  `Proj(ℤ[1/2][X,Y,Z]/(Y²Z³?…))` display, `P=(0,0,1)`, `Q=(1,0,1)`, `ω = dX/Y`.
- E15 (Ex. 2.2.2 naive level 3, pp. 117–118, transcribed): `[N]^*ω = λω, λ = N` at
  flex points ⟹ `[3]` étale over ℤ[1/3] (the `[N]*ω = Nω` trick — ALSO the proof
  core of T-B5!); ℰ₃ represented over ℤ[1/3] by
  `Spec ℤ[1/3, β, γ][((a₁³−27a₃)a₃)⁻¹]/(β³ − (β+γ)³)` with
  `a₁ = 3γ−1, a₃ = −3γ²−β−3βγ`, `P=(0,0)`, `Q=(γ, β+γ)` [AME 2.2.10 lengthy
  computation — a T-E1-style VariableChange gymnastics ticket, fully explicit].

## Chain B8–B9 — dual isogeny & Hasse over S (GME 2.6.3, Thm 2.6.9/2.6.10, proofs
pp. 149–151, transcribed)

- B8: `f^t : E′ → E` from `f^* : Pic⁰_{E′} → Pic⁰_{E}` + Abel + key-lemma.
  `f^t∘f = [deg f]` etc.: **PROOF TECHNIQUE (formalization-critical): prove the
  morphism identity for the UNIVERSAL curves over M₁/M'₂/M₃ — reduced bases! — where
  it suffices to check on geometric fibres; then pull back to arbitrary S.** Fibre
  case = I(P)-tensor gymnastics (p. 150: `f^*I(f(P)) = I(f⁻¹(f(P)))`,
  translation `T_{−P}`, Abel products) — HasseWeil's field-level dual-isogeny work is
  the anchor (reuse; their `Isogeny/Dual/Canonical`).
  Sub-ticket: "reduced-universal-base transfer principle" (T-RED0): morphism
  identities between f.l.f. schemes over a reduced base hold iff they hold on
  geometric fibres (det/matrix argument as in KM 1.4.4(5)) + every (E,level) is
  pulled back from a universal family. NEW GENERAL TOOL — plan it once, use
  everywhere (also for pairing properties T-C2).
- B9 (Hasse 2.6.10): `Tr f = f + f^t ∈ ℤ`, `f² − (Tr f)f + deg f = 0`, negative
  discriminant via `P(m,n) = deg(nf+m) > 0`. Feeds the RIGIDITY computation:
- **Aut computation (2.6.4 start, p. 151, transcribed — the engine of T-G3/T-H5):**
  `ε ∈ Aut(E,φ)`, n ≥ 3 invertible: `ε = 1 + ng`; `1 = deg ε = 1 + nTr(g) + n²deg g`
  ⟹ `Tr ε ≡ 2 mod n` and `Tr(ε)² < 4` [B9(iii)] ⟹ n ≥ 3 forces `deg g = 0 ⟹ g = 0`.
  3|N or 4|N ⟹ Aut trivial over ℤ[1/6]-schemes; coprime m,n ≥ 3 ⟹ over ℤ
  (`S = S[1/m] ∪ S[1/n]`!).

## Chain C — the Weil pairing over S (GME 2.6.4 pp. 152–153, proofs transcribed —
**T-C1's construction of record; KM-gate LIFTED**)

- C.1 splitting: `Pic(E′) = Pic(E′/S) ⊕ Pic(S)` via `0^*`; choose L in each class
  with `0^*L = O_S`.
- C.2 the pairing: for isogeny `π : E → E′` of degree N, `L ∈ Ker(π^*)`: `π^*L`
  trivialised by `(π⁻¹Uᵢ, fᵢ∘π)`; ratios `hᵢ = (fᵢ∘π)/(fⱼ∘π)`-corrected units glue:
  for `P ∈ Ker(π)`, `hᵢ∘P` glue to `h(P) ∈ 𝔾_m(S)` (computation with
  `(fᵢ∘0)/(fⱼ∘0) = 1` normalisation); `⟨P, L⟩ := h(P)` bilinear; lands in μ_N;
  key-lemma ⟹ morphism `Ker(π) × Ker(^tπ) → μ_N`.
- C.3 classical formula over k̄ (the NORMALISATION ANCHOR = T-C4): `div f = N([0]−[P])`,
  `div g = Σ([Qᵢ] − [P′+Qᵢ])`, `f∘^tπ = g^N`, `g(x+Q) = ⟨P,Q⟩g(x)` — LITERALLY
  Silverman III.8's function-theoretic pairing ⟹ fibrewise comparison with
  HasseWeil's `weilPairing` is the definitional match, Silverman convention ✓ (D7).
- C.4 nondegeneracy (p. 153): `⟨P,Q⟩ = 1 ∀Q ⟹ g` descends ⟹ `NP′ = 0` ⟹ `P = 0`.
- C.5 (PR1) antisymmetry; **(PR2) ⟨,⟩ identifies `Ker(^tπ)` with the Cartier dual of
  `Ker(π)`** [duality API — needs AG-CD vocabulary from toric/#40500 + GME 1.7];
  (PR3) adjointness `⟨x, f y⟩_N = ⟨^t f x, y⟩_N`; Tate-module self-duality; (2.50)
  additivity of transpose. Exercise: PR1–3 proofs "left to reader" — expand via C.3
  fibrewise + T-RED0 transfer.
- Lean mapping: `weilPairing` (DS4) := C.2 applied to `π = [N]` (`^t[N] = [N]` by
  B8); specs T-C2a/b/c via T-RED0 + C.3; `E[N]`-self-duality statement = the AG-CD
  upgrade of `weilPairing_perfect`.

## Chain Y — Thm 2.6.8: Y(N) fine over ℤ[1/p] and over ℤ (GME 2.6.2–2.6.4,
pp. 143–154; T-E9/T-H8's proof plan)

Y.1 `S_{E/S} ≅ E[N] ×_S E[N]` (2.48; kernel-pullback square) ✓ already REAL in
skeleton. Y.2 KM-Lemma 2.6.5/2.6.6: `P_{E/S}` = EQ-locus (`deg D = deg D′ ⟹ ≤ is =`)
— our T-D18 route confirmed verbatim; open Isom-subfunctor when N invertible ⟹ finite
étale. Y.3 Thm 2.6.4: `M_N := P_{𝐄/M₁}` over ℤ[1/6]; étale over ℤ[1/6N]; GL₂-action;
`GL₂\M_N ≅ M₁` geometric quotient [GME 1.8.4 = stream Q source]; grading (2.49) by
𝔾_m-action. Y.4 Remark 2.6.1: `Proj(R_N)` = 𝔾_m-quotient; coarse for ℰ_N [Lemma
2.3.1 = stream M source]; = fine when representable. Y.5 Lemma 2.6.7 (proof p. 148,
transcribed): the **G-torsor descent engine**: `Aut(E,φ_N) = 1` + `E[M]` étale ⟹
`T := M_{MN} → S := Spec(A^G)` is a G-torsor (`G×T ≅ T×_S T`); Example 1.11.1 descent
datum from the cocycle `θ(g)`; descend the universal `(𝐄, φ_N)`; `ι′∘ι = id` by
faithful flatness. [Streams Q (invariants) + DESC (Example 1.11.1: descent along a
torsor = Galois-type descent — AINTLIB reuse: HasseWeil `Descent.lean` engines].
Y.6 Thm 2.6.8 proof (pp. 153–154): Aut-triviality (chain B9); p = 3 via ℰ₃ (E15);
p = 4 via Legendre (E14) over ℤ[1/2]; glue `M_{N/ℤ[1/2]}` and `M_{N/ℤ[1/3]}` over
ℤ[1/6] ("definition of elliptic curves is local") → `M_N/ℤ` affine; p ≥ 5: pick
q ≥ 3 coprime, `M_{Nq}/H_q` geometric quotient represents over ℤ[1/qp], second q′,
glue over ℤ[1/pqq′]. → worker plan for T-H8 with every step sourced.
Y.7 Katz-components note for stream IRR: GME 2.9.3 (irreducibility of p-ordinary
moduli) + 2.5.3 (étale coverings of Tate curves) = the algebraic connectedness route's
in-hand source; read at T-IRR0 cut.

---

# CORRECTIONS (2026-08-06, adversarial pass rounds 17–18 — read before cutting any ticket from chain A6)

Hida pp. 106–110 re-read verbatim (pdf = book + 10). **Three of the four defects found by review are in
the SOURCE itself; the July transcription was faithful.** The header's "GME is proof-sufficient on its
own" is refuted — GME needs KM's repairs at three points.

1. **(2.15) is false as Hida states it.** Hida p. 107, verbatim: *"R¹f_*𝒪_E ≅ 𝒪_S for an elliptic curve
   E/S"*, proved from *"the exact sequence `0 → 𝒪_E → L → 𝒪_S → 0`"* — but the third term is
   `e_*e^*L = e_*N_{0/E} ≅ e_*ω^∨`, not `𝒪_S`, and Hida's (E3) is genuinely fibrewise
   (*"`f_*Ω_{E_s/s} ≅ k(s)` for all geometric points"*), so ω need not be trivial. Counterexample: the
   quadratic-twist family (μ₂-torsor via `[-1]`, nontrivial `M ∈ Pic⁰(C)[2]`) has `R¹f_*𝒪_E ≅ M^∨`.
   Correct statement: `R¹f_*𝒪_E ≅ ω^∨`, invertible, base-change compatible; trivial **Zariski-locally**.
   Hida's own downstream uses (p. 109 after "by further shrinking S"; p. 110 "ω is invertible") need only
   the local/invertible form, so the chain survives. The in-tree witness is `Picard/SelfAdjointN.lean:236`.
2. **A6.α's "corollary" is a method-repetition, and Hida says so**: p. 108 verbatim — *"The above argument
   can be applied to any invertible sheaf ℒ which is fiber by fiber of degree 1 and show that
   `f_*ℒ ≅ 𝒪_S` **locally** and `R¹f_*ℒ = 0`."* Faithfully recorded in July. Globally false without
   "locally" (`S = ℙ¹`, `L = 𝒪([0]) ⊗ f^*𝒪(1)` has `f_*L ≅ 𝒪(1)`).
3. **A6.β's locality is elided in the source.** Hida p. 109: *"Since the formation of invertible sheaf is
   local, Pic_{E/S} is local"* — a non-sequitur (iso classes are not a Zariski sheaf: `𝒪_{ℙ¹}(1)` vs `𝒪`).
   The missing input is **universal `f_*𝒪 = 𝒪`** making zero-rigidified bundles automorphism-free, so
   rigidified descent is effective — exactly KM p. 65, and exactly the tree's `UniversallyOConnected` +
   `eq_one_of_pullback_eq_one`.
4. **A6.γ's injectivity inference is invalid in the source.** Hida p. 109: *"Thus ι is fiber by fiber
   injective and hence is injective."* False inference over a non-reduced base (`Spec k[ε]/(ε²)`: the
   ε-tangent section agrees with 0 on the only geometric fibre). The *statement* is true; the proof must be
   KM's mutually-inverse maps — the evaluation-divisor inverse `D(L)` (`V = f_*L`, `f^*V → L` universally
   injective, flat cokernel, `D(L)` a degree-one relative ECD, `D(L ⊗ f^*M) = D(L)`, `D(I(P)⁻¹) = P`).

**Simplification found in the same pass: (2.15) is OFF the critical path.** Neither KM pp. 64–67 nor the
`D(L)`-inverse route uses `R¹f_*𝒪_E` at all. The load-bearing statement is only the **degree-one package**
(item 2), which both sources state identically (KM p. 66 = Hida pp. 107–108) — double-attested, and the
correct target of group A.
