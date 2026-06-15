# Reviewer reply — round 5 (2026-05-28)

## Executive verdict

The counterexample is correct. The attempted `CoordHom : R_{\bar K} → R_{\bar K}`
for (1-\pi) cannot exist. This is not a Lean artefact; it is the geometric
fact that (1-\pi) sends every (F_q)-rational point to (O), so the affine (x)
coordinate of the image has poles at those points. Your divisibility residual
is false for exactly the reason the affine open (E\setminus{O}) is not
stable under (1-\pi). The brief’s diagnosis that the project conflated
“projective morphism” with “endomorphism of the affine coordinate ring”
is right.

For Step 3, I recommend **Option I, but with one refinement**:

> Work at the function-field / projective-curve level, and replace the
> `CoordHom` requirement by a weaker “compatible rational/projective
> morphism” witness sufficient for the alg-closed fibre-count theorem.

Do not use a global affine coordinate-ring map. Do not make localisation
the main route. Projective coordinates are morally clean but probably
too large a refactor.

---

## Q1 — Counterexample sanity check

Yes, the counterexample is mathematically correct.

For

$$E/\mathbb F_5:\quad y^2=x^3-x$$

and $P=(2,1)$, we have $P\in E(\mathbb F_5)$, since

$$2^3-2=8-2=6\equiv1\pmod5,$$

and $1^2=1$. It is non-2-torsion because in the short Weierstrass case
$a_1=a_3=0$, 2-torsion affine points have $y=0$, and here $y=1$.

At $P$,

$$x^5=x,\qquad y^5=y,$$

so

$$x-x^5=0.$$

With $a_4=-1$ and all other $a_i=0$, your numerator calculation gives

$$\mathcal N(P)
= -1(2+2)-2(1)(-1)+2^2\cdot2+2\cdot2^2$$

where $y_\pi^-=-y^5=-1\equiv4$. In the integer expansion you wrote:

$$-4-8+8+8=4\not\equiv0\pmod5.$$

So if

$$\mathcal N=(x-x^q)^2p$$

held in $R$, evaluation at $P$ would force $4=0$, contradiction. This
is decisive.

The more conceptual version is even stronger: at an $F_q$-rational
non-2-torsion point $P$,

$$(1-\pi)(P)=O,$$

so

$$x\circ(1-\pi)$$

has a pole at $P$. Therefore it cannot be a regular function on the
affine curve $E\setminus\{O\}$. Thus it cannot lie in the affine
coordinate ring $R$. This is exactly what your brief states: the
projective morphism exists, but its pullback of the affine coordinate
$x$ is meromorphic on the source affine curve, not regular.

There is no reading under which the global divisibility residual in
$R$ remains true. The only salvage is to change the ring/open subset,
or to work projectively/function-field-level.

---

## Q2 — Best Step-3 reformulation

Choose **Option I**, with a stronger and more explicit compatibility
interface.

The correct mathematical object is not

$$R_{\bar K}\to R_{\bar K}.$$

It is a morphism of smooth projective curves, equivalently a function
field embedding in the opposite direction, together with enough
compatibility to identify its geometric point map.

The pullback

$$(1-\pi)^*: \bar K(E)\to\bar K(E)$$

is perfectly well-defined by the chord/addition formula as a
homomorphism of function fields. The failure is only that
$x\circ(1-\pi)$ is not regular on the whole affine source.

So replace the Step-3 target with something like:

```lean
structure ProjectiveCurveMapCompat where
  pullback : KbarE →ₐ[Kbar] KbarE
  pointMap : E_Kbar.Point → E_Kbar.Point
  pullback_x_eq : pullback x_gen = addPullback_x   -- in function field
  pullback_y_eq : pullback y_gen = addPullback_y   -- in function field
  pointMap_eq : ∀ P, pointMap P = P - frobenius_q P
  compatible_on_regular_domain :
    -- local/evaluation compatibility where pullbacks are regular,
    -- or a projective/local statement sufficient for fibres
```

Then rework the Step-4 consumer to require only:

1. a function-field pullback, for degree/sepDegree;
2. a point-map/fibre witness, for identifying the kernel;
3. compatibility between the two at the projective-fibre level, not
   a global affine `CoordHom`.

The exact compatibility needed for V.1.3 is much weaker than a full
coordinate-ring map. It is enough to know:

$$P\in \ker(1-\pi)
\quad\Longleftrightarrow\quad
\text{the place }P\text{ lies over }O\text{ under the function-field map}.$$

Equivalently, if $u$ is a uniformizer at $O$, then

$$\operatorname{ord}_P((1-\pi)^*u)>0
\quad\Longleftrightarrow\quad
P-\pi(P)=O.$$

This is the projective/local form of the fibre-over-$O$ statement and
avoids $R\to R$.

### Why not Option II?

Localising at

$$D=x-x^q$$

does make the chord expression regular where $D\ne0$, but the kernel
points are precisely among the points where $D=0$. Those are the
points you need to count. So the localisation removes the critical
fibre and then requires stitching it back by separate
projective/local data. That is possible, but it is not simpler than
Option I.

Also, $D=0$ may include more than just $F_q$-rational kernel points:
points with $x^q=x$ but non-fixed $y$ can occur. So the localisation’s
omitted locus is not exactly the kernel. It is a technical open-cover
argument, not the clean main route.

### Why not Option III?

Projective coordinates are morally the correct geometry. If
Mathlib/project already has a strong projective morphism API for
Weierstrass curves, this would be clean. But your existing
infrastructure is function-field and affine-valuation oriented. A
full projective-coordinate refactor would be expensive and unnecessary
for V.1.3.

### My recommended “Option IV”

Call it:

> **Option I′: function-field plus projective-fibre compatibility.**

Do not try to build a `CoordHom`. Instead, prove a fibre-count theorem
whose input is a function-field map plus a theorem identifying the
fibre over $O$.

For your concrete map, prove:

```lean
theorem oneSubFrobenius_fiber_over_infinity :
  ∀ P : E_Kbar.Point,
    liesOverInfinity (oneSubPullbackFunctionField) P
      ↔ P = frobenius_q P
```

or equivalently:

```lean
theorem oneSubFrobenius_kernel_eq_primes_over_infinity :
  primesOver O oneSubFunctionFieldPullback ≃
    {P : E_Kbar.Point // P = frobenius_q P}
```

Then Step 2 identifies the right side with $E(F_q)$.

This is the smallest reformulation that matches the actual geometry.

---

## Q3 — Existing Lean / Mathlib analogue

I would not expect Mathlib to already have the full elliptic-isogeny
theorem in the form you need.

Mathlib likely has pieces of the general algebraic geometry /
function-field story, but not a ready theorem:

$$\deg_s(\phi)=\#\ker\phi$$

for elliptic-curve isogenies represented only by a function-field
pullback.

Earlier project notes already suggest this theorem is project-provided
rather than Mathlib-provided: your current Step 4 “alg-closed fibre
count” was proved in your own library via inertia-degree-one and
height-one-prime analysis over $\bar K$.

The theorem you want should be project-internal and should probably
be stated one level more generally than elliptic isogenies:

```lean
theorem card_fiber_eq_sepDegree_of_functionFieldMap
    (φstar : K(C₂) →ₐ[k] K(C₁))
    (hsep : IsSeparableExtension ...)
    (Q : C₂.ProjectivePoint)
    (hfiber : FiberDescription φstar Q fiberSet)
    (hunramified : ... maybe automatic for generic or separable isogeny ...)
    :
    Fintype.card fiberSet = sepDegree φstar
```

But for your immediate use, a specialised theorem is better:

```lean
theorem oneSubFrobenius_sepDegree_eq_card_fixedPoints_Kbar
    (φstar := oneSubFrobeniusPullback_Kbar) :
    sepDegree φstar =
      Fintype.card {P : E_Kbar.Point // P = frobenius_q P}
```

Then combine with Step 2.

If you already have alg-closed fibre count with a `CoordHom` input,
refactor its dependency boundary. It should not fundamentally need a
global $R\to R$ map. It needs:

* function-field extension degree / sepDegree;
* a way to identify the relevant fibre over $O$;
* local ramification/inertia facts.

So look for your own theorem that consumes
`smoothPoint_fiber_eq_primesOver`, `primesOver`, `sepDegree`, or
`HeightOneSpectrum`, and weaken the “morphism from CoordHom”
assumption to a “function-field map plus fibre identification”
assumption.

I would not spend time searching for a hidden Mathlib
elliptic-isogeny lemma; the project is already ahead of Mathlib here.

---

## Q4 — Salvage assessment

Most of the round-4 infrastructure survives, but anything that used
the false `CoordHom` must be quarantined.

### Safe to keep

The following are still sound:

* Step 1: $a^q=a\iff a\in K$ inside $\bar K$.
* Step 2: Frobenius fixed locus on $E(\bar K)$ equals $E(F_q)$.
* Step 4: alg-closed fibre count, **provided it can be fed a correct
  projective/function-field morphism interface rather than the false
  affine `CoordHom`**.
* Degree base-change, if it only refers to the function-field
  extension and not to the false affine map.
* Polynomial identities A/B/C. They are true identities in $R$; they
  just prove a weaker statement:
  $$(x-x^q)^2\mid (y^q-y)^2\mathcal N,$$
  not $(x-x^q)^2\mid\mathcal N$. They may still help analyse the
  meromorphic function or local fibres.

### Must retract or isolate

Retract or mark as impossible:

* `CoordHom : R_Kbar → R_Kbar` for $1-\pi$.
* `addPullback_x_in_coordRing_range`.
* y-side analogue.
* Any lemma claiming global regularity of $x\circ(1-\pi)$ on
  $E\setminus\{O\}$.
* Any point-map construction that depends on evaluating
  `addPullback_x` as a regular affine coordinate at every affine point.

### Hidden trap: evaluation at kernel points

At kernel points, $x\circ(1-\pi)$ is not finite. So any theorem that
says the target point’s affine coordinates are obtained by evaluating
`addPullback_x` and `addPullback_y` at $P$ must exclude the kernel or
be projective/local.

This is likely the main place the old infrastructure will silently
fail.

### Hidden trap: preimage of the affine open

For a projective morphism $g:E\to E$, the pullback of the affine
coordinate ring $O(E\setminus\{O\})$ lands in

$$O(g^{-1}(E\setminus\{O\})).$$

For $g=1-\pi$,

$$g^{-1}(E\setminus\{O\}) = E\setminus\ker(1-\pi).$$

So the correct regular-function target is not $R$, but the coordinate
ring of $E\setminus\ker(1-\pi)$, or a suitable
localisation/intersection of local rings. This is the geometric reason
Option II is a detour and Option I′ is preferable.

---

## Recommended implementation plan

### Step A: Preserve the function-field pullback

Keep the chord formula as a function-field map:

```lean
oneSubFrobeniusPullback_Kbar : KbarE →ₐ[Kbar] KbarE
```

with:

```lean
map_x = addPullback_x
map_y = addPullback_y
```

in the fraction field.

Do not try to prove `map_x` or `map_y` comes from the affine
coordinate ring.

### Step B: Define fibre-over-$O$ by local/projective condition

Choose a uniformizer $u$ at $O$, for example $t=-x/y$ if available,
or use the valuation/local ring at $O$. Define:

$$P\text{ lies over }O
\quad\Longleftrightarrow\quad
\operatorname{ord}_P(\phi^*u)>0.$$

Then prove for $\phi=1-\pi$:

$$P\text{ lies over }O
\quad\Longleftrightarrow\quad
P-\pi(P)=O
\quad\Longleftrightarrow\quad P=\pi(P).$$

The first equivalence is the compatibility between function-field
pullback and point map, but only at the projective fibre level.

### Step C: Refactor Step 4 consumer

Change it from:

```lean
CoordHom → card fiber = sepDegree
```

to:

```lean
FunctionFieldMap + fiberOverPoint identification → card fiber = sepDegree
```

This should use the same height-one-prime/inertia machinery already
proved over $\bar K$.

### Step D: Compose with fixed-locus descent

Use Step 2:

$$\{P\in E(\bar K):P=\pi(P)\}\cong E(F_q).$$

Then V.1.3 closes.

---

## Final answers to Q1–Q4

**Q1.** The counterexample is correct. The sharp residual is false.
There is no interpretation in which a global
`CoordHom : R_{\bar K} → R_{\bar K}` for $1-\pi$ exists, because
$x\circ(1-\pi)$ has poles at $F_q$-rational affine points.

**Q2.** Use Option I′: function-field map plus projective/local fibre
compatibility. Option I as written is closest. Option II is an
open-cover detour; Option III is clean but too heavy.

**Q3.** I would not expect Mathlib to already have the exact
elliptic-isogeny theorem at function-field-map level. Refactor the
project’s alg-closed fibre-count theorem to accept a function-field
map and a fibre-identification witness instead of a `CoordHom`.

**Q4.** Steps 1, 2, 4 survive, but Step 4 must not secretly depend on
the false affine `CoordHom`. Identities A/B/C survive as true
function-field/coordinate identities. Retract only the global
coordinate-ring range/divisibility lemmas and any affine evaluation
lemmas at kernel points.
