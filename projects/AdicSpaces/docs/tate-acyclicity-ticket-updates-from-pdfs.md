# Tate acyclicity: ticket updates from Wedhorn + Zavyalov

This note updates the existing ticket plan against the actual proofs in:

- Torsten Wedhorn, *Adic Spaces*, §8.1–8.2 and Appendix A (esp. pp. 81–84, 105–106).
- Bogdan Zavyalov, *Sheafiness of Strongy Rigid-Noetherian Huber Pairs*, §§2–3 and Appendix A.

The goal of the current ticket stack should remain:

> Formalize Wedhorn Theorem 8.28(b): strongly noetherian Tate rings are sheafy.

Zavyalov should be treated as:

1. a source of **corrections** to the current ticket plan (especially the topological/sheaf aspect and the correct notion of strong noetherianity), and
2. a blueprint for a **future phase** proving sheafiness for strongly rigid-noetherian Huber pairs.

The current plan conflates these two proofs in a few places. The first job is to separate them.

---

## 0. High-level corrections to the current plan

### Correction A: TICKET-4 is **not** a completion-preserves-exactness argument

Wedhorn Lemma 8.33 is proved directly in **completed** Tate algebras:

- `O_X(U₁) = A⟨ζ⟩/(f-ζ)`
- `O_X(U₂) = A⟨η⟩/(1-fη)`
- `O_X(U₁ ∩ U₂) = A⟨ζ,ζ⁻¹⟩/(f-ζ)`

and then a 3×3 diagram chase is performed entirely at that level. There is **no separate uncompleted row whose completion gives the target row**. So:

- remove “decompleted exactness” from TICKET-4,
- remove “completion preserves exactness” from TICKET-4,
- and remove TICKET-6 as a dependency of TICKET-4 for that reason.

The old “completed vs decompleted” language belongs to Zavyalov’s different proof strategy, not to Wedhorn 8.33.

### Correction B: the topological sheaf condition must be tracked explicitly

Wedhorn’s theorem is about a **sheaf of complete topological rings**, not only a sheaf of rings. Zavyalov makes this explicit by introducing:

- **strict** morphisms of topological groups,
- and a definition of sheaf of topological rings in which the map
  `F(U) → ∏ F(U_i)`
  must be a **topological embedding**.

The current tickets mostly track ring-exactness. The plan should either:

1. strengthen key exactness statements to **strict exactness**, or
2. add a separate topological-embedding checkpoint in TICKET-5.

For a mathlib-quality development, it is better to expose a reusable notion like:

- `IsStrict` for continuous linear maps/open-onto-image,
- `IsStrictExact` for short exact sequences in topological modules/groups.

### Correction C: the current class `IsStronglyNoetherianTate` is mathematically wrong

It is **not** enough to ask for “there exists a noetherian ring of definition”.

For the Wedhorn theorem, the relevant notion is Wedhorn 6.36:

- `A` strongly noetherian Tate iff `Â⟨X₁,…,X_n⟩` is noetherian for all `n`;
- equivalently, every Tate ring topologically of finite type over `A` is noetherian.

Zavyalov’s stronger notion is:

- a pair of definition `(A₀,I)` is **topologically universally rigid-noetherian** if `Spec Â₀⟨X₁,…,X_n⟩` is noetherian outside `I` for all `n`;
- a Huber ring is **strongly rigid-noetherian** if it admits such a pair.

For analytic/Tate rings, Zavyalov proves the bridge between these notions. The ticket plan should use either:

- a precise `IsStronglyNoetherianTate`, or
- layered predicates `IsTopologicallyUniversallyRigidNoetherianPair`, `IsStronglyRigidNoetherian`, and a bridge theorem for the Tate case.

### Correction D: TICKET-6 should shrink and move earlier

The current TICKET-6 bundles together:

- Artin–Rees,
- open mapping for finitely generated modules,
- completion preserves exactness.

Only the **module topology / open mapping** part is on the critical path for Wedhorn 8.29. The completion-exactness part is not needed for Wedhorn 8.33.

So TICKET-6 should become:

> “Noetherian Tate module topology API (Prop 6.18 + Remark 6.19)”

and it should feed **TICKET-2B**, not TICKET-4.

### Correction E: TICKET-1B should not block on full Cartan/Godement comparison

Wedhorn’s Proposition A.4 states more than the current theorem needs. For Theorem 8.28(b), we need:

- the **sheaf-on-a-basis** consequence,
- and the refinement/product-cover acyclicity lemmas actually used in Lemma 8.34.

We do **not** need the full statement “Čech cohomology equals derived functor cohomology on all opens”. That should be optional / later.

---

## 1. Updated dependency graph

A more faithful dependency graph is:

```text
TICKET-0   mathlib/project audit
    |
    +--> TICKET-1A  finite-cover Čech API
    |
    +--> TICKET-2A  Tate/Laurent algebra models + universal properties
    |
    +--> TICKET-6   noetherian Tate module topology API (Prop 6.18)
                    |
                    +--> TICKET-2B  Remark 8.29 + Lemma 8.31
                                   |
                                   +--> TICKET-3  Prop 8.30 + Cor 8.32

TICKET-1A --> TICKET-1B  refinement/product-cover lemmas + minimal basis-sheaf criterion

TICKET-2B + TICKET-3 + (small algebra lemmas from 2A) --> TICKET-4  Lemma 8.33

TICKET-1B + TICKET-4 + TICKET-3 --> TICKET-5  Lemma 8.34 + Theorem 8.28(b)
```

If the team later wants Zavyalov’s theorem, make that a **Phase II** after this stack lands.

---

## 2. Ticket-by-ticket updates

## TICKET-0 — audit and kill false dependencies

### New purpose
Produce a report that does two things:

1. identifies existing mathlib/project APIs;
2. explicitly records that **completion exactness is not on the critical path** for Wedhorn 8.33.

### Add these audit items

- existing project API for rational subsets / presheaf values / completed rational localizations;
- existing project API for restricted power series / Laurent series;
- `RingHom.Flat` / `RingHom.FaithfullyFlat` and useful lemmas for contraction of primes / faithful flatness criteria;
- finite-product flatness and finite-product faithful-flatness criteria;
- snake lemma / 3×3-lemma support for module diagrams;
- adic/module-topology APIs already in mathlib;
- Artin–Rees and cofinality lemmas for filtrations;
- whether the project already has a theorem matching Wedhorn Remark 7.55 (decomposing a rational subset into basic `R(f/1)` and `R(1/f)` steps).

### Deliverable update
The report should end with a “**critical path**” section listing exactly which lemmas are needed for Wedhorn 8.33 and which ones are future/generalization only.

---

## TICKET-1A — finite-cover Čech foundations

### Keep
Build a finite-cover Čech complex API.

### Change
Do **not** use order-homs `Fin (q+1) →o Fin n` as the primary indexing type. Use all functions
`Fin (q+1) → Fin n` for the public complex.

That choice is better for:

- refinement maps,
- product covers,
- restriction of covers,
- and later reuse beyond the current theorem.

### Recommended public definitions

- `FiniteCover X ι` with finite index type `ι`
- `FiniteCover.inter : (Fin (q+1) → ι) → Set X`
- `Cech q := ∏ σ : Fin (q+1) → ι, F (U.inter σ)`
- `cechDiff`
- `cechAug`
- `FiniteCover.restrictTo`
- `FiniteCover.prod`

### Strong recommendation
Avoid exposing alternating cochains in the first public API. If needed later, add them as an internal comparison layer. The current theorem only needs the finite-cover complex and its exactness properties.

### API outputs workers should leave behind

- extensionality lemmas for cochains;
- `d ∘ d = 0`;
- cover restriction and product-cover constructions;
- chain maps induced by cover maps/refinements.

---

## TICKET-1B — only formalize the Čech theorems actually used

### Current ticket problem
The present plan asks for full Wedhorn A.4, including the Čech-to-sheaf-cohomology comparison. That is overkill.

### Revised target
Formalize exactly the infrastructure used in Lemma 8.34:

1. the relevant refinement/product-cover invariance facts;
2. a **minimal basis-sheaf criterion**.

### Correct statements to use

#### A.3(1) (actual master lemma)
If `V|_{U_{i₀...i_q}}` is acyclic for all finite intersections of members of `U`, and symmetrically `U|_{V_{j₀...j_q}}` is acyclic for all finite intersections of members of `V`, then `U` is acyclic iff `V` is acyclic.

This is the real engine behind A.3(2) and A.3(3).

#### A.3(2)
If `V` refines `U`, then `U` is acyclic iff `V` is acyclic **because** on each finite intersection of members of `V`, the restricted cover from `U` is equivalent to the trivial cover.

#### A.3(3)
If every restriction `V|_{U_{i₀...i_q}}` is acyclic, then `U × V` is acyclic iff `U` is acyclic.

This is the exact form used in Lemma 8.34(i).

### Minimal A.4 replacement
Prove only:

> If `B` is a basis stable under finite intersections, and every finite `B`-cover of every `U ∈ B` from the chosen coverage family is acyclic, then the associated presheaf satisfies the sheaf condition on `B`, hence extends to a sheaf on all opens.

Make the higher cohomology comparison a separate optional theorem / later ticket.

### Note to workers
If you *do* formalize the full A.4, keep it in a separate namespace/file section so the current theorem does not depend on Cartan/Godement.

---

## TICKET-2A — Tate and Laurent algebra models

### Current ticket problem
The proposed definition

> `instance : IsTateRing (tateAlgebra A) -- X is a topologically nilpotent unit`

is wrong. `X` is not a unit.

### Revised goal
Provide clean models for the completed algebras appearing in Wedhorn 8.29–8.33.

### Needed objects

1. `TateAlgebra A := A⟨X⟩`
2. `TateAlgebra2 A := A⟨X,Y⟩`
3. `LaurentTateAlgebra A := A⟨ζ,ζ⁻¹⟩`

### Recommended design
Use **two models** for the Laurent algebra:

- a quotient model `A⟨X,Y⟩ / (XY - 1)` for universal properties and comparison with presheaf values;
- a bilateral restricted Laurent-series model for explicit coefficient calculations.

Then prove a comparison isomorphism between them.

This will make TICKET-4 much cleaner.

### Required basic API

- constants/variables and evaluation maps;
- quotient identifications `A⟨X⟩/(X) ≃ A`, `A⟨X,Y⟩/(XY-1) ≃ LaurentTateAlgebra A`;
- extensionality by coefficients on each model;
- embeddings `A⟨ζ⟩ → LaurentTateAlgebra A`, `A⟨ζ⁻¹⟩ → LaurentTateAlgebra A`.

### Tate-ring instance
The Tate structure on `A⟨X⟩` should be inherited from a chosen topologically nilpotent unit of `A`, exactly as in Wedhorn §6, not from `X`.

### Optional but good
Also package the basic rational-localization algebras `A⟨f/s⟩` and `A⟨F₁/s₁;…;F_n/s_n⟩` in the style of Zavyalov Def. 2.1 / 2.5 if the project does not already expose them cleanly.

---

## TICKET-6 — rename and move earlier

### Rename
`OpenMapping.lean` should become something like

- `NoetherianTateModules.lean`, or
- `CompleteTateModuleTopology.lean`.

### Revised mathematical target
Formalize the API around Wedhorn Prop. 6.18 and Remark 6.19:

- finitely generated modules over a complete noetherian Tate ring carry a canonical topology;
- linear maps are continuous;
- maps onto image are open / strict.

### What this ticket should prove

1. existence of the canonical topology on finitely generated modules;
2. independence of the chosen ring of definition / lattice;
3. every A-linear map between finitely generated modules is continuous;
4. every A-linear map is open onto its image (or at least every surjection is open);
5. reusable “strict map” lemmas for later tickets.

### What should move out of this ticket
- completion exactness of strict sequences;
- any projective-scheme/Čech arguments.

Those belong only to the future Zavyalov phase.

---

## TICKET-2B — Remark 8.29 and Lemma 8.31

### Current ticket problem
The flatness proof outline in the current plan is too weak and partly incorrect.

### Revised target
Follow Wedhorn 8.29 / 8.31 exactly.

### Sub-ticket structure

#### 2B.1 — `M⟨X⟩` as a functor on finitely generated complete modules
Define `M⟨X⟩` and prove that a strict short exact sequence of finitely generated modules remains exact after `⟨X⟩`.

This is the reusable API that the proof of Remark 8.29 is really using.

#### 2B.2 — Remark 8.29 (`μ_M`)
For finitely generated `M`, prove
`μ_M : M ⊗[A] A⟨X⟩ → M⟨X⟩`
is an isomorphism.

Use a finite presentation of `M`, the free case, and exactness of `⟨X⟩` on strict maps.

#### 2B.3 — Lemma 8.31(1)
Prove `A⟨X⟩` is flat over `A` by showing tensor with `A⟨X⟩` preserves injections of finitely generated modules, exactly as Wedhorn does.

Then prove faithful flatness via either:

- the prime-lifting argument on the constant term prime, or
- a quotient criterion using `(X)` **if** the algebra API makes that cleaner.

#### 2B.4 — Lemma 8.31(2)
Package Wedhorn’s claim as a reusable lemma:

> If multiplication by `g` is injective on `M⟨X⟩` for every finitely generated `M`, then `A⟨X⟩/(g)` is flat over `A`.

Then specialize to:

- `g = 1 - fX`
- `g = f - X`

For `g = f - X`, formalize the finitely generated-submodule argument from the recurrence
`f m₀ = 0`, `f m_n = m_{n-1}`.

This ticket should leave behind reusable lemmas about quotient-flatness from injectivity of multiplication.

---

## TICKET-3 — Prop 8.30 and Cor 8.32

### Current ticket problem
The present proof sketch of Cor. 8.32 is not the one in Wedhorn and is not robust enough for formalization.

### Revised target
Follow Wedhorn 7.55, 8.30, 8.32.

### Required prerequisites

1. rational localizations of strongly noetherian Tate rings remain strongly noetherian Tate;
2. a theorem implementing Wedhorn Remark 7.55: every rational subset can be built by a chain of basic steps of type
   - `R(f/1)` and
   - `R(1/f)`.

### Prop 8.30 proof plan

- reduce to `V = X` and `A` complete;
- use Remark 7.55 to reduce to the two basic cases;
- identify
  - `O_X(R(f/1)) = A⟨X⟩/(f-X)`
  - `O_X(R(1/f)) = A⟨X⟩/(1-fX)`;
- apply TICKET-2B flatness.

### Cor 8.32 proof plan
Prove the map
`A → ∏ O_X(U_i)`
for a finite rational cover is faithfully flat by:

- flatness: finite products of flat algebras are flat;
- faithfulness: the induced map on spectra is surjective because the `U_i` cover `Spa A`.

Do **not** describe this as factoring through `A⟨X⟩`; that is not the right proof here.

### Good reusable API
This ticket should leave behind a general lemma of the form:

> For a finite family of flat `A`-algebras whose affinoid spectra cover `Spa A`, the map to the finite product is faithfully flat.

---

## TICKET-4 — Lemma 8.33 only, in completed Tate algebras

### Current ticket problem
It mixes Wedhorn’s proof with Zavyalov’s different “decomplete then complete” proof.

### Revised target
Formalize exactly Wedhorn Lemma 8.33 on p.83–84.

### Exact objects to identify first

- `B₁ := O_X(U₁) = A⟨ζ⟩/(f-ζ)`
- `B₂ := O_X(U₂) = A⟨η⟩/(1-fη)`
- `B₁₂ := O_X(U₁∩U₂) = A⟨ζ,ζ⁻¹⟩/(f-ζ)`

### Row 1 / Row 2 algebra lemmas to isolate

#### 4.1 Decomposition lemmas in Laurent algebra
Prove:

- `A⟨ζ,ζ⁻¹⟩ = A⟨ζ⟩ + ζ⁻¹ A⟨ζ⁻¹⟩`
- `(f-ζ)A⟨ζ,ζ⁻¹⟩ = (f-ζ)A⟨ζ⟩ + (1-fζ⁻¹)A⟨ζ⁻¹⟩`

These give surjectivity of `λ` and `λ'`.

#### 4.2 Kernel lemma
For
`λ(g(ζ), h(η)) = g(ζ) - h(ζ⁻¹)`
prove
`ker λ = im ι`
by explicit coefficient comparison.

This is the key computational lemma of the ticket.

#### 4.3 Diagram chase
Use a reusable 3×3 lemma / snake-style lemma if available; otherwise write one specialized diagram-chase theorem for module diagrams.

### Topological upgrade
If the project target is a sheaf of **topological** rings, strengthen the row-3 exactness statement to a strict-exact statement, or add a theorem that the resulting equalizer map is a topological embedding.

### Remove from the ticket
Delete all tasks saying:

- “decompleted exactness”
- “row 3 is the completion of row 2”
- “prove completion preserves exactness”

Those are not part of Wedhorn 8.33.

---

## TICKET-5 — Lemma 8.34 and Theorem 8.28(b)

### Current ticket problem
It uses a wrong class definition and it does not clearly separate ring-sheafness from topological sheafness.

### Revised class layer
Use one of these two designs.

#### Design A (minimal/current phase)
A predicate `IsStronglyNoetherianTate A` meaning exactly Wedhorn 6.36.

#### Design B (preferred if Phase II is planned)
Layered predicates:

- `IsTopologicallyUniversallyRigidNoetherianPair (A₀,I)`
- `IsStronglyRigidNoetherian A`
- bridge theorem: in the analytic/Tate case, strong noetherianity is equivalent to strong rigid-noetherianity.

If Design B is used, TICKET-5 only consumes the Tate-side bridge.

### Lemma 8.34 updates
Follow Wedhorn literally:

1. **Basic 2-element covers** `U_f = {R(f/1), R(1/f)}` are acyclic by TICKET-4.
2. Restricting `U_f` to any rational subset remains acyclic because rational localizations stay strongly noetherian Tate.
3. By A.3(3), finite products of such 2-element covers (Laurent covers) are acyclic.
4. For a standard cover generated by `T = (f₀,…,f_n)`, use Cor. 7.32 to choose a unit `s` so that the Laurent cover generated by `s⁻¹ f₁,…,s⁻¹ f_n` has the property that every restriction `U|_{V_j}` is generated by units.
5. Any rational cover generated by units is refined by the Laurent cover generated by `f_i f_j⁻¹`.
6. Use A.3(2)/(3) to conclude acyclicity of the standard cover.

### Theorem 8.28(b) updates
Split the final ticket into two explicit outputs.

#### 5.1 Ring-sheaf theorem
Use the basis-sheaf criterion on rational subsets.

#### 5.2 Topological sheaf theorem
Either:

- inherit it from strict-exactness statements proved earlier, or
- separately prove the equalizer map into the product of sections is a topological embedding.

Zavyalov Def. 3.4 is the right formal target here.

---

## 3. Phase II (separate from the current theorem): Zavyalov’s generalization

Do **not** mix these into the Wedhorn(b) tickets. Put them in a later phase.

### Z-TICKET-1 — rational localization API for general Huber pairs
Use Zavyalov Def. 2.1 / 2.5 and Remarks 2.4 / 2.7 to build a clean universal-property layer for

- `A(f₁/s,…,f_n/s)`,
- `A(F₁/s₁;…;F_n/s_n)`,
- and their completions.

### Z-TICKET-2 — strong rigid-noetherianity
Formalize:

- Def. 2.8,
- Lemma 2.11 (bridge to strongly noetherian analytic/Tate),
- Lemma 2.13 (preservation under rational localization),
- Theorem 2.16 (if you already have the external `FK18` API in scope; otherwise leave as an imported assumption/theorem wrapper only when the library contains it).

### Z-TICKET-3 — projective/decompleted Čech proof skeleton
Formalize Zavyalov Theorem 3.5 Step 2–4:

- the projective scheme `P = Proj ⊕ J^m`,
- the affine morphism `s : U → P`,
- exactness of the decompleted Čech complex via scheme cohomology,
- and the identification of its completion with the analytic Čech complex.

### Z-TICKET-4 — FP-approximated sheaves appendix
Formalize the exact subset of Appendix A needed for the projective-scheme proof:

- Lemma A.3,
- Theorem A.5,
- Lemma A.9 / Cor. A.10 / Cor. A.11,
- Lemma A.12,
- Theorem A.13.

This is the real cost center of the generalization.

---

## 4. What to tell workers explicitly

1. **Do not implement Cartan/Godement unless you are explicitly on an optional follow-up ticket.**
2. **Do not implement completion-exactness for TICKET-4.** That belongs to the other proof.
3. **Track topological strictness early.** Otherwise the final theorem will only be a sheaf of rings.
4. **Model the Laurent algebra cleanly.** It is the central reusable object in the proof.
5. **Fix the class design before any downstream ticket starts.** The current `IsStronglyNoetherianTate` stub is not stable enough.

