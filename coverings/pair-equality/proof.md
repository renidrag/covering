# Geometric equality for pair coverings

**Füredi's equality argument, adapted and formalised by Rob Gardiner, with Codex assistance.**

## 1. Conventions and theorem

Put r=q+1 and N=q(q+1), with q≥4 an integer. The coordinate set I is finite.
A support family H is a finite set of finite subsets of I. Thus equal
subsets are identified, but distinct actual points having equal supports
are not identified: their multiplicities can be used as weights.
Write d_J(x) for the number of supports of J containing x and c_J(x,y)
for the number containing both coordinates. Write χ_E for the real
indicator vector of E in ℝ^I.

**Theorem 1.** Suppose |I|=N, every E∈H has size r, distinct members of H
intersect, and real weights w satisfy

\[
w(E)>0\quad(E\in H),\qquad
\sum_{E\in H:x\in E}w(E)=1\quad(x\in I).                 \tag{1}
\]

Then one of the following holds on the original coordinate set I.

* **Occupied truncated core.** There are J⊆H and a partition of I into
  q+1 groups of size q. Each member of J meets each group once; each
  coordinate has core degree q. Distinct coordinates have core codegree
  zero in the same group and one in different groups. Distinct core
  supports intersect once. Consequently |J|=q². Every core member retains
  its original positive weight w, and all supports in H∖J remain present.
* **Actual twisted family.** H has N supports and every coordinate has
  degree r. There are fixed-point-free involutions μ on H and ν on I.
  For distinct E,F∈H, |E∩F| is two when F=μ(E) and one otherwise.
  For distinct x,y∈I, c_H(x,y) is two when y=ν(x) and one otherwise.

In particular every distinct coordinate pair is covered in the twisted
branch. No field, prime-power, regularity, optimiser or independence
hypothesis is imposed. This is a classification of supplied weighted
support incidences, not an unconditional covering-number theorem.

The proof follows Füredi's equality argument [F90, §7]. Exact coordinate
count and exact unit loads let us use finite support extraction and two
elementary dimension bounds without a general optimisation framework.
The core incidences are exactly the hypotheses of the existing
[truncated-plane load theorem](../truncated-plane-loads/proof.md).

## 2. Feasible independent supports

**Lemma 2.** There are J⊆H and positive real weights a on J satisfying
all the unit-load equations on I, such that {χ_E:E∈J} is linearly
independent. In particular |J|≤N. The weights a may differ from w.

**Proof.** Summing (1) over I gives r∑w=N, hence ∑w=q. The weights
w/q express u=(1/q)·1 as a convex combination of the vectors χ_E, E∈H.
Finite Carathéodory extraction represents u by positive coefficients b
on an affinely independent subfamily of these vectors.

For completeness, the finite reduction behind this extraction is as follows.
Choose a representation of u using the fewest positive coefficients.
An affine dependence gives a nonzero coefficient function c with
∑c=0 and ∑c(E)χ_E=0. Some c(E) is negative. The least of the finitely
many positive ratios b(E)/(−c(E)) with c(E)<0 is attained and positive;
call it ε. The coefficients b+εc are nonnegative, sum to one, still
represent u and vanish at a minimising support. Removing zero coefficients
contradicts minimality. Thus the selected family is affinely independent.

Indicators of distinct finite subsets are distinct: equality of indicators
at every coordinate gives the same membership predicate. Pulling the
selected vectors back therefore gives actual supports J⊆H, without
identifying or changing any coordinate. Put a(E)=qb(E); coordinatewise
the representation of u gives unit loads.

Finally a linear relation ∑c(E)χ_E=0 has coefficient sum zero, because
summing its coordinates gives r∑c=0 and r≠0. Affine independence makes
all coefficients zero. The dimension of ℝ^I is N, proving |J|≤N. ∎

Only feasibility, positivity, containment and linear independence will be
used. No equality between a and w, or minimum-support property of a
particular returned witness, is part of the supported extraction contract.

**Lemma 3 (load equality).** For the reduced family,

\[
\sum_Ea(E)=q,\qquad
1=q\,a(E)+\sum_{F\ne E}a(F)(|E\cap F|-1).              \tag{2}
\]

Consequently a(E)≤1/q, d_J(x)≥q and |J|≥q². If d_J(x)=q,
every support through x has weight 1/q and meets every other support once.

**Proof.** Sum loads over all coordinates for the first equality. Sum
them over E for the second: the diagonal contribution is ra(E), and
subtracting ∑a=q leaves (2). Each off-diagonal summand is nonnegative.
The weight bound follows; summing it at x gives the degree bound and
summing over J gives the support bound. At degree q, all q incident
weights must reach 1/q. In (2) strict positivity of every other weight
then forces each off-diagonal intersection to have size one. ∎

## 3. Groups from minimum degree

Let Q={x:d_J(x)=q}. For x∈Q define

\[
C(x)=I\setminus\bigcup_{E\in J:x\in E}(E\setminus\{x\})
    =\{y:y=x\text{ or }c_J(x,y)=0\}.                   \tag{3}
\]

**Lemma 4.** C(x) contains x, has size q and meets every reduced support
exactly once. For x,y∈Q, the sets C(x),C(y) are equal or disjoint.

**Proof.** The q supports through x intersect pairwise only at x by
Lemma 3. Their punctured supports are disjoint q-sets, removing q²
coordinates and leaving q. A support through x meets C(x) just at x.
A support F avoiding x meets each of the q supports through x once;
these are distinct intersection coordinates. None contributes a second
coordinate, and F has one remaining coordinate, which lies in C(x).

If y∈C(x), every support through y meets C(x) only at y, so C(x)⊆C(y).
Equal cardinalities imply equality. If y∉C(x), the q supports through y
meet C(x) at distinct coordinates, since they meet each other only at y.
They exhaust C(x), so no coordinate of C(x) belongs to C(y). ∎

**Lemma 5 (Füredi's dimension step).** If Q is nonempty, |J|=q² and
d_J(x)=q for every x∈I.

**Proof.** Write M=|J| and d=N−M. Lemmas 2–3 give 0≤d≤q.
Let C₁,…,C_s be the distinct groups of Lemma 4. They are disjoint
q-sets, and their union contains Q. Outside Q every degree is at least r.
Counting incidences gives

\[
r(N-d)=\sum_xd_J(x)\ge rN-|Q|,\qquad rd\le |Q|\le qs. \tag{4}
\]

Thus s≥d+1: for d>0 use qs≥qd+d, and for d=0 use Q≠∅.
Suppose d<q and choose d+1 groups. Their indicators together with the
M independent support indicators are independent. Indeed, in a relation

\[
\sum_{j=1}^{d+1}\alpha_j\chi_{C_j}
   +\sum_{E\in J}\beta_E\chi_E=0,
\qquad B=\sum_E\beta_E,
\]

summing coordinates in C_j gives qα_j+B=0. Summing all coordinates
gives q∑α_j+rB=0. Substitution yields (q−d)B=0, so B=0,
then every α_j=0, then every β_E=0 by Lemma 2. This gives
M+d+1=N+1 independent vectors in dimension N, a contradiction.
Therefore d=q and M=q². The degree sum is now rq²=qN; since each
of the N degrees is at least q, they all equal q. ∎

**Construction of the core.** Now Q=I. The groups of Lemma 4 partition
all N coordinates into q+1 parts of size q. Label these parts by
Fin(q+1); this relabels groups only. Every support is a transversal,
and all degrees are q. Distinct supports intersect once by Lemma 3.
Distinct coordinates in one group cannot occur together. If y∉C(x),
(3) supplies a support through x and y; it is unique because two such
supports would intersect twice. These establish every required truncated
plane incidence, with core exactly J⊆H on I.

## 4. The regular branch and both mate relations

**Lemma 6.** If Q is empty, |J|=N and d_J(x)=r everywhere. The support
and coordinate mate involutions in Theorem 1 exist on J and I.

**Proof.** Every degree is at least r. Hence r|J|=∑d_J≥rN, while
Lemma 2 gives |J|≤N. Both are equalities, proving regularity.
For each E∈J,

\[
\sum_{F\ne E}(|E\cap F|-1)=rq-(N-1)=1.                \tag{5}
\]

These are nonnegative integers. Exactly one support μ(E) meets E twice;
every other distinct support meets it once. Symmetry and uniqueness give
μ(μ(E))=E and μ(E)≠E.

No distinct coordinate pair has codegree more than two: three supports
containing it would give one support two different mates. For each x,

\[
\sum_{y\ne x}c_J(x,y)=q\,d_J(x)=N.                    \tag{6}
\]

If all these codegrees were at most one, the sum would be at most N−1.
Thus x has at least one distinct partner of codegree two.

Put O(E)=E∩μ(E), a two-element set. A doubled coordinate pair lies
in some O(E). Also O(μ(E))=O(E), so every coordinate belongs to at
least two support-indexed overlaps. The total number of coordinate-overlap
incidences is ∑_E|O(E)|=2N. There are N coordinates; hence each belongs
to exactly two overlaps, necessarily those indexed by E and μ(E).
Any doubled partner of x lies in that same two-element overlap. It is
therefore unique; denote it by ν(x). Codegree symmetry gives
ν(ν(x))=x and ν(x)≠x.

In (6) the mate contributes two and the other N−2 coordinates contribute
at most one each. Equality forces all these contributions to be one.
This proves coordinate-pair coverage and the full codegree relation,
rather than assuming self-duality or coverage from the numerical parameters. ∎

## 5. Maximality and restoration of H

**Lemma 7 (twisted maximality).** If J has the incidences of Lemma 6
and q≥4, every (q+1)-set S meeting all members of J belongs to J.

**Proof.** Suppose S∉J, and put f(E)=|S∩E|. Equal support sizes give
1≤f(E)≤q. Counting incidences with S and ordered distinct pairs in S gives

\[
\sum_Ef(E)=r^2,\qquad
\sum_E(f(E)-1)=r,\qquad
\sum_Ef(E)(f(E)-1)\ge rq=N.                           \tag{7}
\]

The last inequality uses the coordinate-pair coverage just proved.
But f(E)(f(E)−1)≤q(f(E)−1), whose sum is qr=N.
Equality holds throughout. Every f(E) is therefore 1 or q. If n counts
the supports with f(E)=q, the middle identity of (7) gives
(q−1)n=q+1. Thus q−1 divides q+1, and hence 2, which is impossible
for q≥4. ∎

**Proof of Theorem 1.** Apply Lemma 2. When Q is nonempty, Lemmas 3–5
construct the occupied truncated core J⊆H. Its incidence structure
does not depend on the auxiliary weights a. The original positive w and
all of H still satisfy (1), so they supply exactly
`TruncatedPlaneLoads.Admissible P H w 1` for the constructed P.

Otherwise Lemma 6 gives a twisted J. Every member of H has size r
and meets every member of J; Lemma 7 gives H⊆J. Together with J⊆H
this is H=J. Both mate maps and all incidences are therefore on the
original family H. This proves the dichotomy. ∎

## 6. Retained controls and scope

The unchanged order-four pure core, with weights 1/4, has unit loads.
The unchanged common-coordinate example has sixteen core supports and
four extras. Its original multiplicities are one on the four core supports
through c, two on the other twelve core supports, and one on each extra.
Dividing by eight gives positive unit loads. The extra {0,4,5,6,7}
meets the occupied core support {0,4,8,12,16} in two coordinates.
Coordinate 0 has unweighted degree eight, coordinate 1 degree four and
coordinate 4 degree five. Thus uniform weighted load is not uniform degree.

Both examples enter the core branch. In the extended case degree eight
rules out the twisted conclusion. The conclusion retains the positive
extras; it neither prescribes the reduced weights nor claims uniqueness
of the extracted core. These checks import the retained examples unchanged.

The mate relations supply the weight equations and determinant arguments
in the [C(4k,k,2) proof](../4k-k-2/proof.md). That account derives the
geometric hypotheses from actual coverings and proves attainment.
[Further applications](../qk-k-2/proof.md) give the general construction
intervals and additional exact values.

## Sources and proof provenance

**[F90]** Zoltán Füredi, *Covering pairs by q²+q+1 sets*, Journal of
Combinatorial Theory, Series A **54** (1990), 248–271. The classification
is Theorem 2.2; the finite support, load, regularity, group and dimension
arguments are in §7, especially pp.258–260, 263–264 and 266–268.
The historical twisted-maximality lemma is on p.259.

**[BMP03]** Jürgen Bierbrauer, Stefano Marcugini and Fernanda Pambianco,
*Projective planes, coverings and a network problem*, author manuscript
(2003). Lemma 7 follows the valid twisted-extension count in the proof
of Corollary 1, pp.8–9. Its stronger whole-family truncated-containment
clause is not used. The dimension argument here follows Füredi explicitly.

**[HHS24]** Hall, Horsley and Stinson, *Bounds on data limits for
all-to-all comparison from combinatorial designs*, Designs, Codes and
Cryptography **92** (2024), 2863–2879. Theorem 4.7 and Lemmas 4.8–4.9
confirm the containment-versus-equality endpoint; they are not substituted
for a proof of the geometric classification.

The published references are [Füredi (1990)](https://doi.org/10.1016/0097-3165(90)90034-T),
[Bierbrauer–Marcugini–Pambianco (2003)](https://doi.org/10.1023/A:1024140122167)
and [Hall–Horsley–Stinson (2024)](https://doi.org/10.1007/s10623-024-01418-6).
For BMP, the inspected text was the 24-page author manuscript; the final
19-page journal version was not obtained. The proof uses its twisted
maximality count only. The distinction between a contained core and the
whole family is explained, with a counterexample to the stronger clause,
in the [load account](../truncated-plane-loads/sources.md).

## Appendix A. Lean contracts and dependencies

All names below are in `CoveringDesigns.PairEquality`.

| Statement | Declaration |
|---|---|
| Exact hypotheses (1) | `PositiveUnitLoads` |
| Lemma 2, on original supports and coordinates | `independent_subfamily`, `indicator_injective` |
| Lemma 3 | `PositiveUnitLoads.total_weight`, `weight_bound`, `degree_lower`, `card_lower`, `saturated_of_degree`, `saturated_intersection` |
| Lemmas 4–5 | `Internal.starGroup_card`, `starGroup_transversal`, `starGroup_equal_or_disjoint`, `degree_q_everywhere` |
| All unchanged Plane fields, core exactly J | `plane_of_degree_q` |
| Lemma 6 regularity | `twisted_of_no_degree_q`, `IsTwistedPlane` |
| Support mates and exact intersections | `IsTwistedPlane.supportMate`, `supportMate_ne`, `supportMate_involutive`, `supportMate_intersection`, `support_intersection`, `support_mate_unique` |
| Coordinate mates, exact codegrees and coverage | `IsTwistedPlane.coordinateMate`, `coordinateMate_ne`, `coordinateMate_involutive`, `coordinateMate_codegree`, `coordinate_codegree`, `coordinate_mate_unique`, `pair_covered` |
| Lemma 7 | `IsTwistedPlane.maximal` |
| Theorem 1 | `geometric_dichotomy` |
| Original w and all of H supplied to existing loads | `admissible_of_core`, `admissible_or_twisted` |
| Section 6 | `Examples.pure_unit_loads`, `extended_unit_loads`, `pure_core_branch`, `extended_core_branch`, `extended_degrees`, `positive_extra_retained`, `double_intersection_allowed` |

`IsTwistedPlane` stores coordinate/support counts, uniformity, degree and
distinct-support intersection. Its mate and coverage conclusions are proved
from those fields. The audit expands them into actual involutions with
exact intersection/codegree formulas and maximality, so the small record
is not being used as an unproved geometric classification.

The extraction imports Mathlib's finite Carathéodory implementation and
uses `minCardFinsetOfMemConvexHull`, its subset and affine-independence
theorems, and `Finset.mem_convexHull'`. It proves the pullback image equality,
coefficient transport, affine-to-linear conversion and dimension bound.
The dimension step uses only finite linear independence and finrank of
ℝ^I. No optimiser, LP duality, search dependency or external certificate
appears in the public proof modules.

The geometric import `.Classification` depends locally only on the new
component, `TruncatedPlaneLoads.Incidence` and `Foundations.Basic`.
`.Compatibility` additionally imports the unchanged load-family interface.
Only `.Examples` imports the existing actual-point control chain. All
previous components remain independent of PairEquality. Detailed finite
sum helpers are private; the supported geometry is listed above.

The component audit checks all 51 explicitly declared public definitions,
structures and theorems, plus two expanded contracts, and their transitive
axioms. The permitted foundational axioms are `propext`, `Classical.choice`
and `Quot.sound`; the main theorem and its expanded restatement are checked
to use exactly those three. There are no admissions, new mathematical
axioms or native proof assertions. Source/data checks, Lean compilation
and later verification-record validation are separate operations. The
[shared guide](../../technical-details.md) gives the verification commands.
