# T-W7 verbatim source quotes (quote-or-delete discipline)

PDFs are LOCAL ONLY (`refs/ModularCurves/`, gitignored): `mumford-GIT.{djvu,pdf}`,
`bosma-lenstra-addition-laws.pdf`, `lange-ruppert-addition-laws.pdf`, `mumford-abelian-varieties.pdf`
(image-only scan, backup for the field case). Text layers regenerate with:
`djvutxt mumford-GIT.djvu /tmp/git.txt` · B–L: `pdftoppm -r 200 -png bosma-lenstra-addition-laws.pdf
blp && for f in blp-*.png; do tesseract "$f" -; done > /tmp/bl.txt`. Locators below are into those
text layers (+ printed page numbers). OCR typos left as-is inside quotes; [bracketed] letters are
OCR fixes.

## Mumford GIT, Ch. 6 §1 (pp. 115–117)

**Chapter convention** (git.txt:4875): "For the sake of simp[l]icity, all pre-schemes in this
chapter will be assumed to be locally noetherian and to be schemes."

**Definition 6.1** (git.txt:4878): "Let S be a noetherian scheme. A group scheme π: X → S is called
an abelian scheme if π is smooth and proper, and the geometric fibres of π are connected."

**Proposition 6.1 [Rigidity lemma]** (git.txt:4885–4895, p. 115): "Given a diagram: X —f→ Y [over]
S, suppose S is connected, p is flat and H⁰(X_s, o_{X_s}) = κ(s), [f]or a[ll] points s ∈ S (X_s
denoting the fibre of p over s). Assume that one of the following is true:
1) X has a section e over S, and S consists of one point,
2) X has a section e over S, and p is a closed map,
3) p is proper.
If, for one point s ∈ S, f(X_s) is set-theoretically a single poin[t], then there is a section
η: S → Y o[f] q such that f = η ∘ p."

**Proof, case 1** (git.txt:4896–4909): "First define a continuous map η: S → Y as f ∘ e. Then
f = η ∘ p as continuous maps. One checks that p_*(o_X) ≅ o_S. [Now] f is defined by its underlying
map, plus a homomorphism: o_Y → f_*(o_X) ≅ η_*(p_*(o_X)) ≅ η_*(o_S). But such a homomorphism is
precisely the extra structure required to make η into a morphism of ringed spaces. It follows
immediately that this is, in fact, a morphism of local ringed spaces, hence by EGA 1, §1.8, a
morphism of schemes."

**Proof, case 2 — THE GLOBALIZATION MECHANISM** (git.txt:4910–4926): "Now suppose 2) holds, and set
η = f ∘ e. To compare f and η ∘ p, let Z be the biggest closed subscheme of X where f = η ∘ p, i.e.
if Δ ⊂ Y ×_S Y is the diagonal, then Z = (f, η ∘ p)⁻¹(Δ). We must show that Z = X. But the first
part of the proof has already shown that if Z contains p⁻¹(t) set-theoretically, for any t ∈ S,
then for a[ll] artin subschemes T ⊂ S, concentrated at t, Z contains p⁻¹(T) as a subscheme. But
this implies that Z actually contains some open neighborhood U of p⁻¹(t). Since p is a closed map,
this implies that Z contains an open neighborhood of the form p⁻¹(U₀), for some open neighborhood
U₀ of t. In particular, Z contains some open set p⁻¹(U₀) [f]or some open neighborhood U₀ of s. Let
U₁ be the maximal open subset of S such that Z ⊇ p⁻¹(U₁). But now t ∈ U₁ ⟺ p⁻¹(t) ⊂ Z ⟺ p⁻¹(t) is
disjoint from X − Z ⟺ t ∉ p(X − Z). But p is flat, hence open, and Z is closed, hence p(X − Z) is
open, hence [S] − U₁ is open. Since S is connected, [S] = U₁."
  *(Reading of the "this implies" step: Z ⊇ p⁻¹(T) for every artinian thickening T at t means the
  ideal of Z lies in ⋂_n m_t^n·O_X along p⁻¹(t), which vanishes by Krull intersection — noetherian
  local rings — so the coherent ideal I_Z is 0 on a neighbourhood of the fibre; this is where
  locally-noetherian is genuinely used.)*

**Proof, case 3** (git.txt:4927–4932): "Then, after a faithfully flat base extension S′/S (e.g. by
S′ = X itself), we can assume that X′/S′ has a section. Then by case 2) we know that f′: X′ → Y′ is
of the form η′ ∘ p′. Since this property determines η′ uniquely, and since f′ descends to a
morphism f, it follows immediately that η′ must also descend to η: S → Y ([cf]. SGA 8, Th. 5.2)."
  *(NOT NEEDED for T-W7: our X = E has the zero section, so case 2 suffices.)*

**Corollary 6.2** (git.txt:4933–4944, p. 116): "Given a diagram: X [⇉ f,g] G [over] S, assume that
G is a group scheme over S, S is connected, p is flat and proper, and H⁰(X_s, O_{X_s}) ≅ κ(s), for
all points s ∈ S. If, for some point s ∈ S, the morphisms f_s and g_s from X_s to G_s are equal,
then there is a section η: S → G such that f = (η ∘ p) · g. Proof. This reduces to Proposition 6.1
for f · g⁻¹."

**Corollary 6.3** (git.txt:4945–4951): "[X over S with] e₁ a section for q₁, assume that q₁ is
proper and flat, Y is connected, and H⁰(X_s, O_{X_s}) ≅ κ(s), for all s ∈ S. Suppose that G is a
group scheme over S, and that f: X × Y → G is an S-morphism. Then there exist S-morphisms
g: X → G and h: Y → G such that [f(x,y) = g(x)·h(y)]. Proof. This reduces to Corollary 6.2, for
the Y-morphisms (f, p₂) and [f ∘ (1_X, e₂ ∘ q₁)] × 1_Y [f]rom X × Y to G × Y."

**Corollary 6.4 (pointed ⟹ homomorphism)** (git.txt:4952–4956): "Let X be an abelian scheme and G
any group scheme over a scheme S. If f: X → G is an S-morphism taking the identity for X to the
identity for G, then f is a homomorphism. Proof. Apply Corollary 6.3 to f ∘ μ: X × X → G, where μ
is the group law for X."

**Corollary 6.5** (git.txt:4957–4959): "If X is an abelian scheme over a scheme S, then X is a
commutative group scheme. Proof. Apply Corollary 6.4 to the inverse morphism from X to X."

**Corollary 6.6 (UNIQUENESS OF THE GROUP LAW = `abelEnrichment_unique`)** (git.txt:4960–4964): "If
X is an abelian scheme over a scheme S, then X has only one structure of group scheme over S with
the given identity e: S → [X] as the identity. Proof. Apply Corollary 6.4 to 1_X, with 2 different
group laws considered on domain and image."

## Bosma–Lenstra, JNT 53 (1995) 229–240 (author copy from Lenstra's Leiden archive)

**Theorem 1** (bl.txt:81–83, p. 230): "The smallest cardinality of a complete system of addition
laws on E equals two, and if two addition laws form a complete system then each of them has
bidegree (2, 2)."

**Theorem 2** (bl.txt:91–97, p. 230): "There is a bijection between P²(k) and the set of
equivalence classes of non-zero addition laws of bidegree (2,2) on E that has the following
property. If (a:b:c) ∈ P²(k) and P₁, P₂ are points in E(K) for some extension field K of k, then
the pair P₁, P₂ is exceptional for the addition law corresponding to (a:b:c) if and only if the
difference P₁ − P₂ of P₁ and P₂ in the group E(K) lies on the intersection of E(K) and the line
ax + by + cz = 0 in P²(K)."

**The canonical two-law system** (bl.txt:100–103, p. 230–231): "We see from this theorem that any
two distinct lines in P²(k) that intersect outside E(k) give rise to a complete system of two
addition laws on E. This occurs for instance for the lines y = 0, z = 0…"
  *(For T-W7.0c: take the laws of the lines Z = 0 and Y = 0. Exceptional loci: law_{Z=0} fails ⟺
  P₁ − P₂ ∈ E ∩ {Z=0} = {O} ⟺ P₁ = P₂ (the diagonal); law_{Y=0} fails ⟺ P₁ − P₂ ∈ E ∩ {Y=0}.
  Disjoint over every field since O = (0:1:0) ∉ {Y=0}; their intersection point (1:0:0) is never on
  the curve: F(1,0,0) = −1.)*

**Universality over rings** (bl.txt:110–117, p. 231): "It will be seen that the coefficients of the
Weierstrass equation for E enter polynomially into all formulae in Section 5. This implies that the
same formulae can be used to perform the addition on elliptic curves over com[m]utative rings. …
For this application to rings, it is essential that each of the addition formulae in the system is
valid on an open subset of E × E; thus, the traditional formulae as in [5, Chapter III, Section 2]
cannot be used."

**Explicit formulas**: §5 of the paper (pp. 236–240). **Resolved 2026-07-07 (lane P1): the §5
polynomials were re-DERIVED exactly** from the paper's own anchor ("Multiplying the addition law
just given by s*(Y/Z) we obtain the addition law corresponding to (0:1:0)", p. 237) rather than
trusted from OCR/eyeball — see `scripts/tw7-p1-bosma-lenstra/` (polynomials + certificates +
regenerating script). Findings of record: (i) law (1) as printed (p. 236–237) equals
`−(Projective.addX, addY, addZ)` of mathlib, exactly; (ii) the diagonal of law (2) equals
mathlib's `dblXYZ` exactly mod the curve relation, sign `+1`; (iii) one printed line of `X₃⁽²⁾`
is `− a₃a₄(2X₁Z₂ + X₂Z₁)X₂Z₁` (an earlier reading as `+ a₃a₄(X₁Z₂ − 2X₂Z₁)X₂Z₁` was wrong —
the derived polynomials are authoritative, being overdetermined by the anchor identity and
independent numeric group-law validation).

## Lange–Ruppert, Invent. Math. 79 (1985) 603–610 (GDZ scan, `LOG_0040`)

Predecessor: complete system of THREE (2,2)-laws for Weierstrass curves (cited by B–L at
bl.txt:75–77: "a complete system of three addition laws, each consisting of bihomogeneous
polynomials of bidegree (2,2), was exhibited explicitly by Lange and Ruppert"). Backup/cross-check
for §5 formulas; image-only scan, OCR on demand.

## Faltings–Chai (for context; conversion `/tmp/fc.txt`)

FC I, Def. 1.1 + Rem. 1.2(a),(b) (fc.txt:358–368): abelian scheme defined as smooth proper group
scheme with connected fibres; finite presentation ⟹ "the technique of reduction to the noetherian
case of EGA IV §8 can be applied"; commutativity "[b]y the rigidity lemma of GIT prop. 6.1."
  *(The EGA IV §8 remark is the intended vehicle for extending canonicity from locally-noetherian
  to arbitrary S — tracked as T-W7.8.)*
