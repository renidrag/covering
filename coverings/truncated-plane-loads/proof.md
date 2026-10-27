# Equal-load extensions of truncated projective planes, q≥4

**Rob Gardiner, with Codex assistance.**

## Abstract

Relative to any supplied truncated projective plane of order q≥4, we classify
all intersecting families of (q+1)-element supports containing the core with
strictly positive real weights and equal coordinate loads. Besides the pure
core, the only possibility adds one whole-group-plus-coordinate support in
each group except the common coordinate's group. Its weights have two positive
parameters. We prove the converse, integer divisibility and the interpretation
as actual pair coverings, retaining distinct points with equal supports.
The proof uses finite incidences and weighted double counting.

## Introduction and contribution

In the dual description of a pair covering, coordinates index block
occurrences, and each actual point gives the support of occurrences containing
it. Distinct points can have the same support; their number is its multiplicity.
Earlier fractional geometric classifications can provide a truncated core in
such a support family. The question here is what can be added to that core
while preserving positive equal loads.

The finite core is an explicit hypothesis. The proof classifies its
extensions directly, without assuming a fractional geometric classification.
[Sources](sources.md) gives the historical context and attribution.

The proof first classifies a single support, then forces a common coordinate
for sufficiently many bases. Two group counts and a count along a core edge
determine the weights. Integer multiplicities and actual coverings follow.

## 1. Incidence conventions and theorem

Fix an integer q≥4. Let V and I be finite sets, with a map g:V→I whose fibres
G_i partition V. A supplied **truncated plane** T is a family of distinct
subsets of V with these incidence properties:

1. |I|=q+1 and |G_i|=q for every i.
2. Every E∈T meets every G_i exactly once.
3. Every coordinate belongs to exactly q members of T.
4. Two distinct coordinates occur together in no core member if they lie in
   the same group, and exactly one if they lie in different groups.
5. Distinct members of T intersect in exactly one coordinate.

These are the incidences obtained by deleting a point and its incident lines
from a projective plane of order q. The groups are the deleted lines with
that point removed. Dually, coordinates are affine lines, groups are parallel
classes, and core members are point pencils. No coordinatising field is used.

Partitioning V gives |V|=q(q+1). Property 2 gives |E|=q+1. Counting incidences
between T and one group gives |T|=q·q=q², by properties 2 and 3.
For q≥2, there is a core member avoiding any prescribed coordinate, since
q²>q. For distinct x,y there is a core member containing x but not y:
q members contain x, and at most one also contains y.

Let H be an ordinary family of distinct (q+1)-subsets of V, containing T.
Assume H is intersecting and w(S)>0 for every S∈H. Here intersecting means
S∩R is nonempty for every S,R∈H, including S=R. Assume the common load is

$$
\sum_{S\in H:\ x\in S}w(S)=K>0\qquad(x\in V).
\tag{1}
$$

Weights outside H have no significance. Put t=K/q.

**Theorem 1 (real classification and converse).** Exactly one of the following
descriptions holds:

* H=T and w(E)=t for every E∈T.
* There are c∈G_h and s with 0<s<t such that
  $$
  H=T\cup\{G_i\cup\{c\}:i\ne h\},
  $$
  every additional support has weight s, and
  $$
  w(E)=\begin{cases}t-s&c\in E,\\t&c\notin E\end{cases}\quad(E\in T).
  $$

Conversely, both descriptions satisfy all the stated hypotheses, with K=qt.
The alternatives are disjoint because the second contains genuine additional
supports. No uniqueness of the supplied core or of its presentation is asserted.

**Theorem 2 (integer form).** If the occupied weights and K are natural
numbers, then K=qt for an integer t≥1. The same descriptions hold with
integer weights; in the second case s is an integer with 1≤s<t. Conversely
every such integer description works. Thus q divides K, and K=q forces
H=T with every multiplicity 1.

## 2. The support and common-coordinate lemmas

**Lemma 3.** A (q+1)-subset S⊆V meeting every member of T is either in T or
is G_i∪{a} for some a∉G_i.

**Proof.** For c∉S, count incidences between S and the q core members through c.
Property 4 gives

$$
\sum_{E\in T:\ c\in E}|E\cap S|=|S\setminus G_{g(c)}|.
\tag{2}
$$

Every term on the left is at least 1, so the right side is at least q.
Every group not wholly contained in S therefore contributes at most one
coordinate to S. If some group is wholly contained, |S|=q+1 gives the
required form with one outside coordinate.

Otherwise S meets each of the q+1 groups exactly once. Equation (2) is then
an equality between q positive terms and q, so every core member through
any c∉S meets S exactly once. Choose two coordinates of S in different
groups and let E be their core member. It cannot contain c∉S, since it
already meets S twice. Thus E⊆S, and their equal cardinalities give E=S. ∎

Write an extra support as G_i∪{a}, with a∉G_i. It cannot be a core member
because a core member meets G_i once and q≥2. For different bases i,j,
two extras G_i∪{a} and G_j∪{b} meet precisely when

$$
g(a)=j,\quad g(b)=i,\quad\hbox{or}\quad a=b.
\tag{3}
$$

**Lemma 4.** If an intersecting collection of extras uses at least four base
groups, there is c∈G_h such that every extra whose base is not h has outside
coordinate c. In particular all extras contain c.

**Proof.** Choose four extras with different bases. If their outside
coordinates were all different, (3) would require each of the six pairs
to be accounted for by one outside coordinate lying in the other base.
Each of the four outside coordinates can account for at most one pair,
since the bases are distinct. Hence two extras on different bases i,j
have the same outside coordinate c; write h=g(c), so h differs from i,j.

Choose an occupied base k outside {i,j,h}; four occupied bases suffice.
An extra on k must have outside coordinate c: otherwise (3), applied to
the extras on i and j, would put its outside coordinate in both G_i and G_j.
We now have three extras on distinct bases i,j,k, all with outside coordinate
c. For any extra whose base is not h, choose two of these three with bases
different from its own. The same argument forces its outside coordinate
to be c. An extra based on h contains c as part of G_h. ∎

## 3. Equal loads determine the whole family

Apply Lemma 3 to H. Write L for the total core weight, A for the total
additional weight, A_i for the weight of extras based on G_i, and T_i
for the weight of extras whose outside coordinate lies in G_i.

**Lemma 5 (load identities).**

$$
L+A=qK,\qquad qA_i+T_i=A.\tag{4}
$$

For every E∈T, if U_E is the total weight of extras whose outside coordinate
lies on E, then

$$
q\,w(E)+U_E=K.\tag{5}
$$

**Proof.** Sum (1) over V. Each support has q+1 coordinates and
|V|=q(q+1), giving the first equality of (4). Sum over G_i instead:
each core contributes its weight once, each extra based on i contributes
q times its weight, and each extra tipped in G_i contributes once. Thus
qK=L+qA_i+T_i, proving the second equality.

Along E, the core contributions total L+qw(E), since every other core
meets E once. An extra G_i∪{a} meets E once in G_i, and a second time
exactly when a∈E. The extra contribution is A+U_E. Therefore
(q+1)K=L+qw(E)+A+U_E, which reduces to (5). ∎

**Proof of the forward direction of Theorem 1.** If there are no extras,
(5) gives w(E)=K/q=t. Otherwise A>0 by strict positivity. Equation (4)
gives A_i≤A/q. Since the occupied base weights sum to A, at least q bases
are occupied. Lemma 4 applies because q≥4, giving c∈G_h.

Every extra outside base h has outside coordinate c, and an extra based
on h has its outside coordinate outside G_h. Consequently T_h=A−A_h.
Equation (4) at h gives (q−1)A_h=0, so A_h=0. Strict positivity excludes
every extra on that base. All remaining extras have outside coordinate c;
thus T_i=0 for i≠h, and (4) gives A_i=A/q>0 for every such i.

There is therefore an extra on each base i≠h. Since H consists of distinct
supports and its outside coordinate is always c, there is exactly one on
each base, with common weight s=A/q>0. Now U_E=A=qs if c∈E, and U_E=0
otherwise. Equation (5) gives the asserted core weights. Some core member
contains c, and its positive weight t−s proves s<t. This assembles the two
alternatives. Their disjointness follows from the observation after Lemma 3. ∎

## 4. Converse and integers

**Proof of the converse in Theorem 1.** In the pure case each coordinate
belongs to q core members, so its load is qt. In the extended case the
extras have size q+1, are distinct, meet every core member and meet each
other at c. Core weights are positive because 0<s<t. Count the load in
three cases:

| Coordinate x | Core contribution | Extra contribution |
|---|---:|---:|
| x=c | q(t−s) | qs |
| x∈G_h, x≠c | qt | 0 |
| x∉G_h | qt−s | s |

For the last row property 4 says exactly one core member contains both x
and c. Every row totals qt. All hypotheses hold. ∎

**Proof of Theorem 2.** Regard natural multiplicities as real weights and
apply Theorem 1. In the pure case t is any core multiplicity. In the
extended case choose a core member avoiding c, which exists by Section 1;
its multiplicity is t. Any extra has multiplicity s. Thus t,s are integers,
K=qt, and positivity gives t≥1 and 1≤s<t. The real converse applies to
these integer descriptions, with natural subtraction t−s equal to the
positive real difference. If K=q, then t=1 and there is no integer s in
the required interval. ∎

## 5. Actual points and block occurrences

**Proposition 6 (expansion).** For either positive integer description, form
the set of distinct points

$$
X=\{(S,j):S\in H,\ 0\le j<m(S)\},\qquad
B_x=\{(S,j)\in X:x\in S\}\quad(x\in V).
$$

Then |X|=qK, every B_x has size K, and the indexed family (B_x) covers
every pair. Its images are distinct, so the ordinary family has exactly
q(q+1) blocks. The construction can be transported to any set of qK points.

**Proof.** Equation (4) gives ∑_S m(S)=qK. Equation (1) counts exactly
the points of B_x. Two distinct points (S,j),(R,l) share a block because
S∩R≠∅; this also covers twins with S=R.

For different coordinates x,y, Section 1 gives a core member E containing
x and not y. The point (E,0) exists because every designated core has
positive multiplicity; it lies in B_x and not B_y. Hence x↦B_x is injective.
Only now may its occurrence count |V|=q(q+1) be read as the cardinality of
the ordinary image family. A bijection of point sets preserves all these
incidences and counts. Reindexing by a bijection of the coordinates preserves
each occurrence separately. ∎

**Proposition 7 (conditional adapter).** Let (B_x)_{x∈V} be indexed
K-element blocks on qK actual points, where K>0, covering every pair.
Suppose the occupied point supports contain every member of a supplied
truncated core T. Then their positive multiplicities have the description
in Theorem 2; in particular q divides K. There is a bijection from the
actual points to their expansion in Proposition 6 preserving incidence
with every original block occurrence.

**Proof.** Put S_p={x:p∈B_x}. If d=|S_p|, the blocks through p cover all
qK−1 other points, so d(K−1)≥qK−1. For q≥2, d≤q would give
d(K−1)≤qK−q<qK−1, a contradiction. Thus every point has degree at least
q+1. The total incidence count is q(q+1)K=|X|(q+1), so every degree is
exactly q+1. This argument does not require K≥q as an extra assumption.

Take the distinct occupied supports H and let m(S) be the cardinality of
the fibre {p:S_p=S}. Each m(S) is positive. Pair coverage makes H
intersecting, with the equal-support case covered by |S|=q+1>0.
Counting the fibres in a block gives coordinate load K. The assumed
containment of T now supplies all hypotheses of Theorem 2. Finally choose
a bijection from each support fibre to {0,…,m(S)−1}; their disjoint union
gives the asserted bijection, without identifying twins. ∎

This adapter requires the occupied truncated core. The
[geometric equality theorem](../pair-equality/proof.md) supplies that core
or a twisted plane for an arbitrary equality covering. The
[C(4k,k,2) proof](../4k-k-2/proof.md) handles both branches.

## 6. Boundary example

The retained order-four plane has coordinates 0,…,19 and groups
G_i={4i,…,4i+3}. Its 16 core supports are checked directly against the
incidence contract. For t=1 the expansion has 16 points and 20 blocks
of size 4, and Theorem 2 excludes any positive integer extension at that load.
For c=0, t=2, s=1 it has 32 points and 20 blocks of size 8.

One core member is {0,4,8,12,16}. The extra G₁∪{0}={0,4,5,6,7} meets
it in {0,4}. Thus the whole support family cannot consist of distinct
projective-plane lines. A core member avoiding 0 has multiplicity 2,
giving two distinct actual points with the same support. The formal checks
also transport the cover to Fin 32 and swap coordinate occurrences 0 and 19.
These are finite boundary checks, not an exhaustive parameter search.

## Appendix A. Lean correspondence and dependencies

All names below are in `CoveringDesigns.TruncatedPlaneLoads`; the sources
are in [the component directory](../../lean/CoveringDesigns/TruncatedPlaneLoads/).

| Mathematical statement | Supported declaration or interface |
|---|---|
| Supplied incidence structure and derived counts | `Plane`; `Plane.coordinates_card`, `core_size`, `core_card` |
| Hypotheses and explicit real alternatives | `Admissible`, `Description` |
| Theorem 1, both directions | `real_classification_iff`; `real_classification`, `description_converse` |
| Explicit constructions | `Plane.pure_converse`, `extension_converse`, `extension`, `extensionWeight` |
| Lemmas 3–4 | `Plane.support_classification`, `common_coordinate` |
| Theorem 2 | `NatAdmissible`, `NatDescription`, `integer_classification`, `integer_converse`, `load_divisible`, `unit_load_pure` |
| Natural constructions | `Plane.natural_pure`, `natural_extension`, `naturalWeight` |
| Proposition 6 | `Point`, `block`, `point_card`, `block_card`, `expanded_cover`, `blocks_injective`, `expanded_family_card`, `expanded_family_cover`, `expanded_on`, `expanded_reindex` |
| Proposition 7 | `support`, `occupied`, `multiplicity`, `actual_classification`, `actualEquiv`, `actualEquiv_incidence` |
| Identity transport | `support_reindex`, `support_relabel` |
| Section 6 | `Examples.pure_counts`, `extended_counts`, `two_coordinate_intersection`, `unit_case`, `relabelled_extended`, `permuted_occurrences`, `twins_exist` |

The real theorem takes arbitrary finite coordinate and group types, q≥4,
a `Plane`, a finite support family H, real weights on subsets, and K>0.
`Admissible` is exactly the six hypotheses in Section 1; it does not assume
the shape of additional supports. `Description` spells out both alternatives,
including exact membership in H and strict inequalities. The internal
`Loads` record is derived using Lemma 3; it is not a caller-supplied geometric
assumption. The integer theorem returns ∃t:ℕ, 0<t ∧ K=q*t ∧ `NatDescription`.
`actual_classification` takes `Multicover.IsCover B K 2 1`, |X|=qK,
K>0, and `P.core ⊆ occupied B`; it returns divisibility and that same description.
Lemma 5 is implemented by `Internal.Loads.total_mass`, `group_equation`
and `core_equation`; `Internal.Loads.classify` assembles the weight argument
before `real_classification` returns the ordinary-family description.

Import `CoveringDesigns.TruncatedPlaneLoads.Converse` for the real theorem,
`.Integer` for multiplicities, `.Covering` for expansion, or `.Actual` for
the conditional adapter. The entry import also includes `.Examples` and the
standard-axiom guards. Within the project, the real branch depends only on
`Foundations.Basic`. The actual-family branch additionally uses
`Multicover.Basic`, `Foundations.Intersecting` (transitively) and
`Foundations.Relabelling`. Mathlib supplies finite sums, arithmetic and
finite-set and equivalence infrastructure. No field-plane construction,
fractional matching, linear programming, search module or other covering
classification is imported. `Internal.Loads` and its counting methods are
implementation details rather than a supported downstream interface.

The [component audit](../../lean/audits/TruncatedPlaneLoads.lean) checks full
types, including fully expanded real and integer contracts, and transitive
axioms. The principal and expanded real contracts have exactly
`propext`, `Classical.choice` and `Quot.sound`; all audited declarations use
at most these foundational axioms. The concrete plane uses ordinary kernel
reduction. The retained-data checker only verifies transcription and input
hashes; it is not a proof premise.

`./covering check` checks source boundaries, hashes and retained data.
`./covering verify truncated-plane-loads` freshly compiles the component and
its prerequisites and runs its theorem audit. `./covering audit
truncated-plane-loads` separately validates the recorded evidence against
current inputs. See the [shared guide](../../technical-details.md).
