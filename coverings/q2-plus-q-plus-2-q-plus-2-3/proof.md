# Lower bounds for C(q²+q+2,q+2,3), odd q≥3

Mathematical account and formalisation: Rob Gardiner, with AI assistance.
The elementary deletion proof is due to Sane, following Füredi's earlier
theorem. Attribution is detailed in [sources.md](sources.md).
The formalisation status is recorded in [README](README.md).

## Abstract and conventions

We prove

\[
\boxed{C(32,7,3)\ge149,\qquad C(58,9,3)\ge375,\qquad C(92,11,3)\ge774.}
\]

These are the cases q=5,7,9 of a general lower bound for
C(q²+q+2,q+2,3), proved below for every odd q≥3. Section 6 gives the
explicit substitutions and integer ceilings for the three stated bounds.

An outside-point parity count bounds the collinear triples in every
(q+2)-set of an arbitrary projective plane. A completion count and the established Füredi–Sane deletion theorem
then handle every low-degree point link; degree summation handles the rest.
All prerequisites needed for the result are proved below. The indexed
formalisation keeps repeated blocks and repeated coverage throughout.

For a finite point set V and finite index set I, a covering is a map
\(B:I\to\binom V k\) such that every t-subset lies in at least one B(i).
Its size is \(b=|I|\). Blocks are sets of distinct points; different indices
may have equal blocks. Degrees and multiplicities count indices. An ordinary
family has distinct blocks; C(v,k,t) is its minimum possible size. It is a
special case, so every universal indexed lower bound bounds C(v,k,t).
No upper bound or attainment is asserted.

Let q be an odd integer at least 3 and put

\[
n=q^2+q+1,\quad
h=\left\lceil\frac{q^2-1}{4q-2}\right\rceil=\lceil q/4\rceil,
\quad N=\frac{nq^3(q+1)}6,\quad M=\binom{q+2}3-h.
\]

**Theorem 1.** Every indexed (n+1,q+2,3) covering satisfies

\[
b\ge n+\left\lceil\frac NM\right\rceil.                 \tag{1}
\]

For odd q≥5 it also satisfies the independently obtainable bound

\[
b\ge\left\lceil\frac{(n+1)^2}{q+2}\right\rceil.             \tag{2}
\]

Formula (1) includes q=3. We retain q≥5 for (2).
There is no assumption that any plane exists. The proof first treats an
exact subfamily inside a point link, then shows that every link of degree
n or n+1 contains such a subfamily.

## 1. Exact pair designs and parity

Suppose L is an indexed 2-(n,q+1,1) design on W: every pair is contained in
exactly one line occurrence. For each point p, counting its other points gives
\(r(p)q=n-1=q(q+1)\), hence r(p)=q+1. Counting incidences gives |L|=n.
Two distinct line occurrences intersect in at most one point. In particular,
equal line blocks cannot have different indices, and a collinear triple has
exactly one supporting line. The q further lines through each point of a
fixed line account for all n−1 other lines, so every two lines meet.
Two points of a line and a point outside it form a noncollinear triangle;
its three side lines leave
n−3q=(q−1)²>0 points outside them, giving a quadrangle. Thus this is an
abstract projective plane in the usual sense. These facts use q≥2 and no
coordinates.

Fix A⊆W with |A|=q+2, and let a_i count lines with |L∩A|=i, for 0≤i≤q+1.
Counting lines, point-line incidences and ordered pairs of A gives

\[
\sum_i a_i=n,\qquad
\sum_i ia_i=(q+2)(q+1),\qquad
\sum_i i(i-1)a_i=(q+2)(q+1).
\]

Subtracting the last two identities yields

\[
a_1=\sum_{i=3}^{q+1}i(i-2)a_i.                              \tag{3}
\]

For every y∈W\A, the q+1 lines through y partition A into their
intersections with A. Since |A|=q+2 is odd, at least one intersection is odd.
Here **odd secant includes a tangent**, whose intersection size is 1.
Count pairs (y,L) with y outside A and |L∩A| odd. Each outside point contributes
at least one; an i-secant contributes q+1−i such points. Consequently

\[
q^2-1=|W\setminus A|
\le qa_1+\sum_{\substack{i\ge3\\i\text{ odd}}}(q+1-i)a_i.  \tag{4}
\]

The inequality is in this direction even when an outside point lies on several
odd secants. For 3≤i≤q+1,

\[
qi(i-2)+\mathbf1_{i\text{ odd}}(q+1-i)
\le qi(i-2)+q+1-i
\le(4q-2)\binom i3.                                      \tag{5}
\]

The first step uses q+1−i≥0. For the second, three times the difference
between the right side and the middle expression is

\[
(i-1)(i-3)\big((2q-1)i-q-1\big)\ge0.
\]

All three factors are nonnegative for q≥3 and i≥3; equality holds at i=3.
Because no triple belongs to two lines,
\(T(A)=\sum_i\binom i3a_i\). Substitution of (3) into (4), followed by (5), proves

\[
(4q-2)T(A)\ge q^2-1,\qquad T(A)\ge h.                     \tag{6}
\]

For completeness, write q=4a+1 (a≥1) or q=4a+3 (a≥0).
The differences between q²−1 and a(4q−2) are respectively 6a and 14a+8;
the differences between (a+1)(4q−2) and q²−1 are 10a+2 and 2a+2.
Thus the ratio lies strictly between a and a+1 in both cases, proving the
stated ceiling identity. In particular 4h≥q+1 and h≤q.

Oddness is essential to the outside-point step. We assert no even-order
extension. At q=1 the displayed ceiling identity fails, so it is excluded.
At q=3 the proof gives h=1 and is valid. The argument uses only exact pair
incidence, never a finite field, prime-power hypothesis or Desarguesianity.

## 2. Completion of an actual plane inside a point link

In an indexed (n+1,q+2,3) cover, fix x and write W=V\{x}.
Suppose an **actual subset J of occurrence indices** through x has |J|=n
and traces B(j)\{x} forming the exact design of §1. Other occurrences through
x are allowed. Let D be the set of triples of W that are not on its lines.
Uniqueness of a triple's line gives

\[
|D|=\binom n3-n\binom{q+1}3
=\frac{nq^3(q+1)}6=N.                                    \tag{7}
\]

An occurrence in J covers no member of D. For i∉J there are two cases:

* If x∉B(i), then B(i)⊆W has q+2 points. By (6), at most
  \(\binom{q+2}3-h=M\) of its triples belong to D.
* If x∈B(i), its trace has q+1 points and covers at most
  \(F=\binom{q+1}3\) members of D. This also is at most M, since
  \(M-F=\binom{q+1}2-h\ge0\), using h≤q.

In particular M≥F>0. Every T∈D must be covered by an index outside J.
Counting the incidence pairs (T,i), rather than assuming disjoint coverage,
therefore gives

\[
N\le\sum_{i\notin J}|\{T\in D:T\subseteq B(i)\}|
\le(b-n)M.
\]

Division by M and integrality give

\[
b\ge n+\lceil N/M\rceil.                                 \tag{8}
\]

This handles repeated blocks, repeated coverage of a demand triple, and
additional x-containing occurrences. Replacing index deletion by set
deduplication here would lose the stated contract.

## 3. The Füredi–Sane deletion theorem, including repetitions

**Lemma 2.** For q≥2, any indexed pair cover on n=q²+q+1 points by n+1
blocks of size q+1 contains n of its actual occurrences forming a
2-(n,q+1,1) design.

Füredi (1989), Theorem 2.1, establishes this conclusion. The following
elementary reconstruction follows Sane (1991), Theorem 3.1 and the five
assertions on printed pp.210–212. His final page credits Füredi's earlier proof.

First, any pair cover with n such blocks is exact: each block contains
\(\binom{q+1}2\) pairs and
\(n\binom{q+1}2=\binom n2\), so coverage leaves no pair multiplicity excess.
If two of the n+1 indexed blocks coincide, delete one occurrence. Coverage
remains and this equality proves the claim. Hence assume the blocks distinct.

Each point p has r(p)≥q+1, by covering its n−1 other points. Call p regular
if r(p)=q+1 and irregular otherwise; let the two point sets be R and H.
Every pair through a regular point occurs exactly once. Moreover

\[
\sum_p(r(p)-q-1)=(n+1)(q+1)-n(q+1)=q+1,
\]

so |H|≤q+1 and R is nonempty.

**A regular block exists.** Otherwise every block meets H. Through a fixed
regular point, its q+1 blocks meet H in disjoint nonempty sets. Thus |H|=q+1,
and every block through any regular point contains exactly one irregular point.
There are q² regular points. Pairs in R×H occur exactly once, and each block
meeting R accounts for q of these pairs. Hence exactly q(q+1)=n−1 blocks
meet R. The remaining two blocks both equal H, contradicting distinctness.

Choose a block C all of whose points are regular. Each other block meets C
in at most one point. There are q further blocks through each of its q+1
points, so exactly n−1 other blocks meet C. There is exactly one remaining
block E disjoint from C.

Every regular point outside C has q+1 incident blocks, all of which must
meet C to cover its q+1 pairs with C. Hence E has only irregular points.
Since |E|=q+1 and |H|≤q+1, E=H. The excess sum then makes every irregular
point's degree exactly q+2.

Fix x∈H. Some block X≠H through x has no other irregular point. Otherwise
each of its q+1 blocks other than H has at most q−1 regular points, covering
at most (q+1)(q−1)=q²−1 of the q² regular points, a contradiction.
Thus X consists of x and q regular points.

Any other block meets X in at most one point, since a pair within X includes
a regular point. The number of other blocks meeting X is
\((r(x)-1)+q\cdot q=(q+1)+q^2=n\), so every other block meets X.
For y∈H\{x}, all q+2 blocks through y meet X once. Its pairs with the q
regular points of X contribute exactly q of these intersections. Therefore
the pair {x,y} has multiplicity exactly 2. This holds for every pair in H.

Delete the occurrence H. Pairs inside H remain covered once; all other
pairs are unaffected. The remaining n occurrences form an exact design by
the opening equality. This completes Lemma 2 without a coordinatisation or
classification theorem.

## 4. Exhaustive degree split and assembly

For every x in a triple cover, its occurrence-preserving point link is a
pair cover on n points with blocks of size q+1. Consequently

\[
d(x)\binom{q+1}2\ge\binom n2=n\binom{q+1}2,
\quad d(x)\ge n.
\]

There are three exhaustive cases, taken in order.

1. Some point has degree n. Pair-incidence equality makes its entire link
   exact, so §2 proves (8).
2. No point has degree n, but some point has degree n+1. Lemma 2 selects
   n actual link occurrences forming a plane. Section 2 again proves (8),
   including the extra occurrence through the point.
3. All degrees are at least n+2. Summing point degrees gives
   \((q+2)b\ge(n+1)(n+2)\).

To finish, the bound in the third case is at least the completion bound (1).
Write M₀=binom(q+2,3), D=nq²+2n+2,
A=(n+1)(n+2)/(q+2), and B=n+N/M. We have 3h≤q+1: check q=3 directly;
for odd q≥5, combine 4h≤q+3 and 3(q+3)≤4(q+1). Also

\[
q(q+2)(n+1)-D=2n(q-1)+q^2+2q-2>0.
\]

Consequently hD≤(q+1)D/3<2M₀(n+1). Clearing the positive denominators,

\[
(A-B)M(q+2)=2M_0(n+1)-hD>0.
\]

Thus ⌈A⌉≥⌈B⌉=n+⌈N/M⌉, which proves (1) in the third case as well.
Only a weak inequality of ceilings is asserted. Equivalently, the minimum
of the two rounded branch bounds always equals the completion branch.
If no plane of order q exists, the first two cases are impossible;
the degree-sum argument still proves (1). Plane existence is never a premise.

## 5. The weaker theorem without deletion

Retain only the exact degree n case and otherwise use d(x)≥n+1. The latter
case immediately gives (2). For the exact-link case we show, for q≥5,

\[
n+\frac{N}{M}>\frac{(n+1)^2}{q+2}.                        \tag{9}
\]

Put \(M_0=\binom{q+2}3\) and \(D=nq^2+n+1>0\). Expanding with
M=M₀−h gives
\((n+N/M-(n+1)^2/(q+2))M(q+2)=hD-M_0(n+1)\), so (9) is equivalent to
\(hD>M_0(n+1)\). Since h≥(q+1)/4, it suffices that

\[
3D-2q(q+2)(n+1)=q^4-3q^3-2q^2-5q+6>0.
\]

For z=q−4≥1 the polynomial equals
\(z^4+13z^3+58z^2+91z+18\), proving positivity. Because n is integral,
\(n+\lceil N/M\rceil=\lceil n+N/M\rceil\); (9) proves the required
ceiling comparison. Finally polynomial division gives the useful exact form

\[
\left\lceil\frac{(n+1)^2}{q+2}\right\rceil
=q^3+5q-6+\left\lceil\frac{16}{q+2}\right\rceil.
\]

This proof uses neither Lemma 2 nor any classification. At q=3 its displayed
target is 40, but the completion branch is only 39, so this argument does
not prove (2) at q=3. The existing C(14,5,3)≥41 theorem is separate.

## 6. Numerical consequences and boundaries

Applying Theorem 1 with q=5,7,9 gives the three conclusions:

\[
\begin{aligned}
C(32,7,3)&\ge31+\left\lceil\frac{3875}{33}\right\rceil
           =31+118=149,\\
C(58,9,3)&\ge57+\left\lceil\frac{26068}{82}\right\rceil
           =57+318=375,\\
C(92,11,3)&\ge91+\left\lceil\frac{110565}{162}\right\rceil
           =91+683=774.
\end{aligned}
\]

Thus every ordinary (32,7,3), (58,9,3) or (92,11,3) covering has at least
149, 375 or 774 blocks, respectively. The proof also applies to indexed
coverings with repetitions. No additional structural hypothesis is required.

The independent bound (2) gives 147, 374 and 770 for the same parameters.
At q=3, (1) gives C(14,5,3)≥13+⌈234/9⌉=39. Formula (2) is outside its
proved range there; the existing C(14,5,3)≥41 theorem remains separate.

For diagnostic purposes, a link of degree exactly n+1 allows its one extra
root-containing occurrence to be charged at F rather than M, giving
\(n+1+\lceil(N-F)/M\rceil\). Its values are 40,149,376,774 at
q=3,5,7,9, respectively. This does not improve the universal bound because the degree n
case remains. The common capacity M is the shorter sufficient argument.

The argument uses actual occurrence indices throughout. The tangent convention,
positive denominator, integer ceilings and q=3 boundary are explicit above.
No finite-plane enumeration is a premise.

## Appendix: Lean correspondence

The public import is `CoveringDesigns.ProjectiveLinkBounds`; all names below
are in that namespace. The component has seven implementation modules and
one entry module. Both the point type `α` and the occurrence type `ι` are
arbitrary finite types, with decidable equality on points. No decidable
equality or injectivity assumption on occurrences is required by the public
contracts.

| Mathematical statement | Lean declaration | Scope |
|---|---|---|
| Exact ceiling in §1 | `collinearFloor_eq` | Odd q≥3; h=⌈(q²−1)/(4q−2)⌉=⌈q/4⌉ |
| (6) | `parity_bound`, `collinear_lower_bound` | Exact indexed pair design and an actual (q+2)-set; counts distinct triples |
| (7) | `noncollinear_card`, `demand_six` | Exact residual demand N and the identity 6N=nq³(q+1) |
| Positive common capacity | `capacity_ge`, `capacity_pos`, `capacity_balance` | q≥3; M≥binom(q+1,3)>0 and M+h=binom(q+2,3) |
| (8) and its undivided form | `completion_bound`, `completion_count` | Selected actual indices J through x whose traces are exact; cardinality n is derived internally |
| Lemma 2 | `furedi_sane_deletion` | q≥2; an indexed pair cover with n+1 occurrences; returns an n-element subset of its indices |
| Branch comparison in §4 | `familyBound_eq_completion` | Odd q≥3; the original minimum equals n+ceil(N/M) |
| Theorem 1, (1) | `indexed_completion_lower_bound`, `completion_lower_bound` | Odd q≥3; only point count, uniformity and triple coverage |
| Original minimum form | `indexed_lower_bound`, `lower_bound` | Preserved contracts with the same hypotheses |
| Independent (2) | `indexed_weak_lower_bound`, `weak_lower_bound` | Odd q≥5; the same covering hypotheses |
| §6, full bounds | `indexed_lower_bound_32_7_3`, `indexed_lower_bound_58_9_3`, `indexed_lower_bound_92_11_3` | 149, 375, 774 on arbitrary finite point types |
| §6, ordinary adapters | `lower_bound_32_7_3`, `lower_bound_58_9_3`, `lower_bound_92_11_3` | The unchanged ordinary `IsCover` definition |
| §6, weak bounds | `indexed_weak_bound_32_7_3`, `indexed_weak_bound_58_9_3`, `indexed_weak_bound_92_11_3` | 147, 374, 770; ordinary adapters omit the `indexed_` prefix |
| q=3 boundary | `calibration_three` | The full formula equals 39; the separate 41 theorem is unchanged |

The recommended reusable interfaces are the parity pair, the completion
pair, `furedi_sane_deletion`, and the full and weak family theorems with their
ordinary adapters. `Internal` names support cross-module bookkeeping and are
not part of that recommended interface.

`collinearTriples L A` is a finite set of actual triples, filtered by positive
line multiplicity. `pointTrace B x i` takes the trace on the subtype of points
other than x. Completion uses `J : Finset ι` and the family indexed by its
membership subtype, so all remaining occurrences stay distinguishable.
The number of selected occurrences follows from exact pair incidence.
`tripleDemand` and `capacity` are natural-number expressions: `demand_six`
proves exact divisibility by 6, and `capacity_balance` prevents truncated
subtraction. Positive denominators justify every ceiling use.

The reused earlier interfaces include `ExactDesign.Counting`,
`Multicover.Counting`, `Multicover.Family` and `Equality.FiniteSum`, with their
foundational imports. The ordinary-family adapter transitively imports
`HorsleySingh.SubsetLinks`, an ordinary subset-incidence interface, but no
Horsley–Singh matrix bound. There is no specialised covering result,
finite-field construction, classification, search output or external
certificate dependency. The unchanged earlier components cannot depend on
this component.

`Weak` imports `Completion` and the ordinary-family adapter; its transitive
source closure excludes `Deletion`. `Deletion` uses only `Incidence` and
its prerequisites, excluding parity, completion and both family proofs.
These boundaries are checked by the shared source audit.

The implementation follows the paper with three proof adaptations:
it sums intersection sizes directly instead of introducing the histogram aᵢ;
it proves existence of the disjoint irregular block without naming its
uniqueness as a separate lemma; and it proves the arithmetic comparisons after
clearing denominators in the integers. The optional sharper n+1 diagnostic
in §6 and the polynomial-division expression in §5 are paper observations,
not additional public Lean contracts.

The [theorem audit](../../lean/audits/ProjectiveLinkBounds.lean) freezes complete
types for every public theorem, including cross-module helpers, and prints
the definitions that occur in them. Its expanded indexed and ordinary
statements expose uniformity and existential coverage and expand the family
formulas. It checks transitive axioms against `propext`, `Classical.choice`
and `Quot.sound`; the principal theorem and its expanded restatement must
use exactly those three. No admitted lemma, custom mathematical axiom,
native proof assertion or external certificate is used.

The [shared verification guide](../../technical-details.md) explains the
commands and trust policy. `./covering check` checks sources and inputs;
`./covering verify projective-link-bounds` freshly compiles the prerequisite
closure and audit; `./covering audit projective-link-bounds` validates a
completed record against current inputs and outputs without compiling.
The corresponding whole-library commands omit the target. Run histories
are working evidence, not prerequisites of this mathematical account.
