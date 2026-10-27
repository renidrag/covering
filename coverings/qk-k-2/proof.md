# Exact values and construction intervals for C(qk,k,2)

**Rob Gardiner, with Codex assistance.**

## Abstract and introduction

We prove

\[
C(55,11,2)=C(65,13,2)=C(80,16,2)=C(85,17,2)=C(95,19,2)=31,
\]
\[
C(56,8,2)=57,\qquad C(90,10,2)=91,
\]

and C(70,14,2)≥31. We also prove exact construction intervals for general
prime-power orders, describe every 20-block (16t,4t,2) covering, and derive
the [combined table of 151 lower bounds](bounds.md) from the proved pair seeds.
The table includes 78 direct additions and the separate order-six consequences.
The latter use the [proof of C(6k,k,2)≥43](../6k-k-2/proof.md).

The lower bounds combine geometric equality, positive support loads and the
twisted-plane determinant. Affine and weighted projective constructions,
together with two historical block lists, give the matching upper bounds.
Schönheim's recurrence gives the higher-strength consequences.

An ordinary (v,k,t) covering is a set of distinct k-subsets of a v-point
set covering every t-subset. C(v,k,t) is its minimum size. An indexed
covering has a finite occurrence set I and blocks B_i; repeated block
images are allowed. All lower bounds below allow such repetitions.
All exactness statements include an ordinary attaining family on every
finite point set of the required cardinality.

## 1. Included proved prerequisites and main results

The argument uses the following included proofs.

1. [General divisibility and the order-four family](../4k-k-2/proof.md):
   for q≥4 and k≥q, every indexed pair cover on qk points has at least
   n=q(q+1) occurrences. Equality forces q∣k or (q+1)∣k. If q∤k, its
   actual occupied supports form a twisted plane. For every k≥8,
   C(4k,k,2) is 20 if 4∣k and 21 otherwise.
2. [Geometric equality](../pair-equality/proof.md): the normalized original
   supports of an equality cover contain an occupied truncated-plane core,
   or form an actual twisted plane on the original occurrence coordinates.
   Both mate involutions and their exact intersection/codegree formulas
   are proved there. These incidences determine the Gram matrix in §2.
3. [Positive truncated-plane loads](../truncated-plane-loads/proof.md):
   for a supplied order-q core, q≥4, all positive integer equal-load
   extensions are the pure or common-coordinate forms recalled in §5.
   The converse, actual point-fibre expansion and identity transports
   are proved there.
4. [Affine construction](../affine-constructions/proof.md),
   [projective geometry](../projective-hyperplanes/proof.md), and the
   expansion/restriction interfaces detailed in the order-four proof:
   prime-power fields exist; the affine and projective planes have their
   usual incidence parameters; fibre expansion, padding, restriction and
   arbitrary relabelling preserve actual coverage.
5. [Schönheim's recurrence](../schoenheim/proof.md), retaining every
   intermediate ceiling.
6. [Order-six nonexistence and covering bound](../6k-k-2/proof.md):
   C(6k,k,2)≥43 for every k≥6, including repeated occurrences.
   This proof uses the determinant calculation in §2; the order-six
   result is used here only for its numerical consequences in §6.

**Theorem 1.** The seven values in §4 are exact, and C(70,14,2)≥31.
For prime-power q≥2, C(qk,k,2)=q(q+1) whenever k≥q and q∣k.
For k=qu+r and 1≤r≤u, a covering with at most q²+q+1 blocks exists
for every qk≤v≤qk+r. Its size is optimal when v>qk. At v=qk, the same
exact value follows if q≥4, q∤k, and either (q+1)∤k or no twisted plane
of order q exists. There is no restriction r<q in the construction or
the open-interval conclusion.
The complete twenty-block description is Theorem 5. Proposition 5a gives
the corresponding description whenever twisting is excluded; Proposition 5b
gives the primitive quotient and replication. All 151 bounds in
[the combined table](bounds.md) follow from Proposition 6 and its proved seeds.

## 2. Determinants and the remaining lower bounds

**Proposition 2 (historical square obstruction).** If an actual twisted
plane of order q≥1 exists, with a=q(q+1)/2, then

\[
D(q)=(q-1)^a(q+1)^{a+1}
\]

is an integer square. In particular no such plane exists at q=7 or q=9.

**Proof.** Its integer coordinate-by-support incidence matrix A is square
after bijectively reindexing the supports. The proved mate involution pairs
the n=q(q+1) coordinates and gives

\[
AA^{\mathsf T}=qI+J+P,
\]

where J is all ones and P swaps mates. Splitting coordinates into a mate
pairs gives diagonal blocks qI+J and off-diagonal blocks I+J. The rational
change of basis formed from pair sums and differences is invertible. The
two resulting blocks are (q−1)I and (q+1)I+2J. The included paired
determinant theorem computes their product as

\[
(q-1)^a(q+1)^a\left(1+\frac{2a}{q+1}\right)
=(q-1)^a(q+1)^{a+1}.
\]

The left side is det(AAᵀ)=(det A)², an integer square. At q=7 the
right side is 6²⁸8²⁹=2¹¹⁵3²⁸; at q=9 it is 8⁴⁵10⁴⁶=2¹⁸¹5⁴⁶.
Their odd exponents of 2 contradict squareness. ∎

**Proposition 2a (square parity).** For q≥2 and a=q(q+1)/2,

\[
D(q)\text{ is a square}\quad\Longleftrightarrow\quad
\begin{cases}
q+1\text{ is a square},&a\text{ even},\\
q-1\text{ is a square},&a\text{ odd}.
\end{cases}
\]

**Proof.** If a=2h, factor D(q) as
((q−1)ʰ(q+1)ʰ)²(q+1). If a=2h+1, factor it as
((q−1)ʰ(q+1)ʰ⁺¹)²(q−1). The removed factors are positive.
For any nonzero integer c, c²z is an integer square if and only if z is:
a rational square root of an integer is integral, by reducing its denominator.
Cancelling the square factor proves the assertion. ∎

For example D(6)=5²¹7²² is not a square. Corollary 3 therefore gives
C(6k,k,2)≥43 when k≥6 and 6∤k. Removing the divisibility restriction
requires the separate [order-six matrix obstruction](../6k-k-2/proof.md),
which also excludes the truncated-plane branch.

**Corollary 3.** Let q≥4, k≥q and q∤k. Every indexed pair covering on
qk points by k-element blocks has at least q(q+1)+1 occurrences if either
(q+1)∤k or a proved exclusion of twisted planes of order q is available.

**Proof.** The included incidence floor excludes smaller sizes. Equality
would contradict general divisibility in the first case, and would give
an actual twisted plane in the second. ∎

No field-existence hypothesis enters this argument. At q=5 and
k=11,13,14,16,17,19, neither 5 nor 6 divides k, giving lower bound 31
directly. At (q,k)=(7,8),(9,10), q∤k and Proposition 2 applies, giving
57 and 91. No unresolved twisted-plane existence case is used or asserted.

## 3. Actual constructions and exact intervals

**Proposition 4.** The affine and weighted constructions in Theorem 1
give ordinary families on any point set of the required size. Their block
counts are optimal in the stated exact ranges.

**Proof, affine case.** Write k=qu with u≥1. The affine plane has q²
points and q(q+1) lines of size q. Replace each point by u distinct
points. The expanded point set has q²u=qk points and each expanded line
has qu=k points. Different parent points share a line; two points in one
fibre share a line through their common parent. Thus every actual pair
is covered. Taking the ordinary image gives at most q(q+1) blocks. For the
matching lower bound, each point of a pair covering on qk points has degree at least
q+1, since q(k−1)<qk−1 for q≥2. Counting incidences gives at least
q(q+1) blocks, so the constructed ordinary family has exactly that size.

**Proof, weighted case.** Choose a line L in PG(2,q). Give its q+1
points fibres of size r and each of the other q² points fibres of size u.
The full expanded point set has

\[
q^2u+(q+1)r=q(qu+r)+r=qk+r
\]

points. The expanded L has size (q+1)r≤k, since r≤u; every other
expanded line has size r+qu=k. Every pair is covered, whether its two
points have different base points or lie in the same fibre.

Choose any v of the expanded points, where qk≤v≤qk+r. Intersect each
expanded line with this set, then enlarge its trace to a k-subset of the
chosen set. This is possible because each trace has size at most k and
v≥k. Coverage persists. Taking the distinct resulting blocks gives at most
q²+q+1 blocks, on any v-point set after relabelling. This includes the full
qk+r-point construction without first passing through the qk endpoint.

If v>qk, each point's degree d satisfies d(k−1)≥v−1>q(k−1), hence
d≥q+1. Summing incidences gives kb≥v(q+1)>qk(q+1), so
b≥q(q+1)+1. This argument requires no twisted-plane condition.
Combining it with the upper bound gives exactness and exactly that many
distinct ordinary blocks. At v=qk with q≥4 and q∤k, Corollary 3 gives
endpoint exactness under either stated exclusion. When r<q, q∤k is
automatic; otherwise it must be retained explicitly. If q∣k, the affine
construction instead gives the smaller exact value q(q+1). ∎

The condition u≥r is sufficient for this construction. For example,
(q,u,r)=(4,4,4) gives C(v,20,2)=21 for 81≤v≤84, and (4,5,4) gives
C(v,24,2)=21 for 97≤v≤100. At the left endpoints v=80 and v=96,
the corresponding exact values are 20. These examples show why the
open interval and the endpoint need separate statements.

## 4. Seven exact values and the separate bound

| (v,k,2) | q | Lower argument | Upper argument | Value |
|---|---:|---|---|---:|
| (55,11,2) | 5 | Neither divisor divides 11 | u=2,r=1 | 31 |
| (65,13,2) | 5 | Neither divisor divides 13 | Perona witness | 31 |
| (80,16,2) | 5 | Neither divisor divides 16 | u=3,r=1 | 31 |
| (85,17,2) | 5 | Neither divisor divides 17 | u=3,r=2 | 31 |
| (95,19,2) | 5 | Neither divisor divides 19 | de Heer–Muir witness | 31 |
| (56,8,2) | 7 | Proposition 2 and 7∤8 | u=1,r=1 | 57 |
| (90,10,2) | 9 | Proposition 2 and 9∤10 | u=1,r=1 | 91 |

The five geometric constructions apply Proposition 4 at the prime powers
5,7 and 9. Perona's and de Heer–Muir's historical families each have 31
distinct blocks. Lean checks their sizes and every pair, and relabelling
gives them on any point set of the required size. Thus all seven lower
bounds meet constructions, proving the exact values.

For k=13 and 19 at q=5, the decompositions 13=5·2+3 and 19=5·3+4 have
u<r. These two cases use the historical block lists, not Proposition 4's
line-weight construction. [Sources](sources.md) gives provenance and licences.

For (70,14,2), Corollary 3 gives 31 because neither 5 nor 6 divides 14.
No attaining 31-block family is claimed. This completes Theorem 1's
numerical assertions.

## 5. All 20-block (16t,4t,2) coverings

**Theorem 5.** Let t≥1. Every indexed (16t,4t,2) covering with 20
occurrences contains an order-4 truncated-plane core in its support family.
Relative to that core, the positive support multiplicities have one of
these forms:

* All 16 core supports have multiplicity t, with no extras.
* Choose c∈G_h and an integer 1≤s<t. The 4 extra supports G_i∪{c}, i≠h,
  each have multiplicity s. The 4 core supports through c have multiplicity
  t−s; the other 12 have multiplicity t. There are no further supports.

Both forms produce covers with 20 distinct blocks. The presentation retains
every point and block occurrence.

**Proof.** The equality adapter and geometric classification give an
occupied core of order 4 or a twisted plane. The order-four determinant
excludes the twisted case. Apply the [integer load classification,
Theorem 2](../truncated-plane-loads/proof.md#1-incidence-conventions-and-theorem)
to the core and the original multiplicities. Its parameter t′ satisfies
4t′=4t, so t′=t. The core has 16 supports, 4 through c and 12 avoiding c;
the other 4 groups give exactly the stated extras.

Conversely, Theorem 2 gives both weight assignments with common load 4t.
[Proposition 6](../truncated-plane-loads/proof.md#5-actual-points-and-block-occurrences)
expands them into 16t distinct points and 20 distinct blocks covering pairs.
Proposition 7 identifies an existing covering with its expansion, preserving
every point and block incidence. At t=1 no integer s satisfies 1≤s<t. ∎

This asserts existence of a presentation. Neither uniqueness of the chosen
core nor classification of presentations up to isomorphism is asserted.

**Proposition 5a (general equality description).** Let q≥4 and k≥q.
Suppose an indexed (qk,k,2) covering has n=q(q+1) occurrences, and no
twisted plane of order q exists on its occurrence coordinates. It contains
a truncated-plane core, k=qu for an integer u≥1, and its occupied supports
have exactly one of these forms:

- The q² core supports, all of multiplicity u.
- Choose a coordinate c in one group G_h and an integer 1≤s<u.
  The q extra supports G_i∪{c}, i≠h, have multiplicity s. Core supports
  through c have multiplicity u−s, and all other core supports have
  multiplicity u. No other support occurs.

Nonsquareness of D(q) is one sufficient twisted-plane exclusion.
Conversely, either prescription on a supplied order-q core gives a covering
of q²u points by n distinct qu-element blocks.

**Proof.** Geometric equality gives a core or a twisted plane, and the
hypothesis excludes the latter. Apply the included integer load classification
to the original support multiplicities, obtaining k=qu and the two forms.
Its point-fibre expansion identifies each original point with its support
and its position in that support's fibre, preserving all incidences.
The same component's integer converse and expansion prove the converse.
No unique core or classification up to isomorphism is needed. ∎

### Primitive quotient and replication

**Proposition 5b.** Let q≥4, k≥q and n=q(q+1). Suppose an indexed
(qk,k,2) covering has n occurrences and q∤k. Its occupied supports form a
twisted plane H, with |H|=n. On the point set H define

\[
B_i^*=\{E\in H:i\in E\},
\]

using the original occurrence coordinates i. These form an ordinary
(n,q+1,2) covering with n distinct blocks. Every original support has the
same positive multiplicity m=k/(q+1), and the original point set is
bijective to H×{1,…,m}, with x∈B_i exactly when its first coordinate
belongs to B_i*. Thus the original covering is a uniform replication of
this primitive covering, with all original incidences retained.

**Proof.** Divisibility and the equality classification give the twisted
branch. Its coordinate degrees show |B_i*|=q+1. Any two distinct supports
intersect, so every pair of primitive points is covered. If B_i*=B_j* for
i≠j, their coordinate codegree would be q+1, whereas the twisted-plane
codegrees are 1 or 2. Thus the primitive blocks are distinct.
The proved mate-load equations give (q+1)m(E)=k for every occupied support E.
Choose a bijection between each original fibre and {1,…,m}. Combining them
gives the stated incidence-preserving bijection. ∎

Consequently, if it is proved that **every** ordinary (n,q+1,2) covering
on any n-point set has cardinality different from n, then equality is
impossible for all q≥4, k≥q with q∤k. A catalogue entry is not this
universal nonexistence premise.

**Proposition 5c (replication converse).** Let q≥2, n=q(q+1) and m≥1.
Given an ordinary (n,q+1,2) covering with exactly n blocks, replace each
point by m points and each block by the union of its fibres. This proves

\[
C(q(q+1)m,(q+1)m,2)=q(q+1).
\]

**Proof.** Expanded blocks have size (q+1)m. A tested pair projects to
at most two original points; these lie in a parent block. If the two
points project to one point, extend it to a pair first. Positive fibre
size preserves distinct blocks, so the expanded family has n blocks.
The incidence lower bound from Proposition 4, with k=(q+1)m, proves
optimality. Relabelling gives the construction on any point set of that
size. This is conditional on the supplied primitive covering; no general
existence of such a covering is asserted. ∎

## 6. All recorded higher-strength consequences

**Proposition 6 (lifting a universal pair bound).** Let 2≤k₀≤v₀,
and suppose every indexed (v₀,k₀,2) covering has at least b₀ occurrences.
Define

\[
b_{j+1}=\left\lceil\frac{(v_0+j+1)b_j}{k_0+j+1}\right\rceil.
\]

For every j≥0, every indexed (v₀+j,k₀+j,2+j) covering has at least
b_j occurrences. The same assertion holds for ordinary families.

**Proof.** The case j=0 is the universal seed hypothesis. At the next
stage, the link at each point is a covering with the preceding parameters.
Its occurrence indices are precisely the original blocks containing that
point. Induction therefore gives each point degree at least b_j, including
when block images repeat. Counting incidences gives
(k₀+j+1)|I|≥(v₀+j+1)b_j; taking the ceiling proves the next step.
Index an ordinary family by its own blocks to obtain the ordinary result. ∎

The [combined table](bounds.md) contains 151 distinct triples with v<100,
k<25 and 2≤t<9. Its three constituent lists are disjoint:

- **59 earlier lifts:** b₀=21 at (4k,k,2), for
  k=9,10,11,13,14,15,17,18,19,21,22,23. The order-four theorem proves
  these seeds, including its repeated-occurrence lower version.
- **78 direct additions:** the eight pair lower bounds in §4 and the five
  seeds (42,7,2), (78,13,2), (84,14,2), (90,15,2), (96,16,2), each at 43.
  The latter already follow from Proposition 2a and Corollary 3 because
  their block sizes are not divisible by 6. Five rows are these seeds
  themselves; 73 are positive-step lifts.
- **14 order-six consequences:** (36,6,2) and (72,12,2), both at 43,
  and six successive lifts from each. These two seeds require the separate
  [unrestricted order-six proof](../6k-k-2/proof.md).

For example, (55,11,2) gives C(56,12,3)≥⌈56·31/12⌉=145, and
(65,13,2) gives C(66,14,3)≥147. The lower-only seed (70,14,2)≥31
also lifts, without any attaining construction. From (95,19,2) the chain
is 31→149→689→3070→13215, giving C(98,22,5)≥3070 and
C(99,23,6)≥13215. Each ceiling is taken separately.

All seeds are universal proved bounds. The dated catalogue comparisons in
[the table](bounds.md) are not premises. The table distinguishes 112 LJCR
improvements, seven additional comparisons against retained cvkt claims,
and 32 rows without an external comparison. Six earlier rows are evaluated
through the general theorem and kernel-checked ceiling identities; the
other 145 rows have separately named numerical lower-bound theorems.

## Appendix A. Lean correspondence and trust boundary

Import `CoveringDesigns.Qk_K_2` for the numerical results and equality
description. Smaller imports are `.Lifting` for the general lifted bound,
`.NumericalLower` for the eight numerical pair lower bounds, `.Construction`
for upper constructions, and `.Equality` for the 20-block description.
These smaller imports avoid the historical witness modules.

For the full parameter ranges in Proposition 4, import
`CoveringDesigns.PairConsequences.Intervals`. Its affine and open-interval
theorems allow q≥2, and the weighted theorems allow r≥q. The earlier
`Qk_K_2.Exact` statements remain valid special cases. In the table below,
names are in `CoveringDesigns.Qk_K_2` unless prefixed by `PairConsequences.`.
All construction interfaces take a point count and the stated numerical
conditions; a field is not an additional caller-supplied premise.

| Statement | Module / declarations |
|---|---|
| Proposition 2 | `.Determinant`: `twisted_determinant`, `exclude_twisted`; `.Exclusions`: `nonsquare_seven`, `nonsquare_nine`, `no_twisted_seven`, `no_twisted_nine` |
| Corollary 3 and §4 lower bounds | `.Exclusions`: `indexed_exclusion`; `.NumericalLower`: `indexed_lower_v_k_2`, `lower_bound_v_k_2` for all eight listed parameters |
| Full expanded and restricted construction | `.Construction`: `weighted_expanded`, `weighted_interval` |
| Incidence bounds for q≥2 | `PairConsequences.Intervals`: `PairConsequences.indexed_pair_floor`, `PairConsequences.indexed_open_floor` |
| Proposition 4, full parameter ranges | `PairConsequences.Intervals`: `PairConsequences.affine_exact`, `PairConsequences.weighted_open_exact`, `PairConsequences.weighted_endpoint_divisibility`, `PairConsequences.weighted_endpoint_exclusion` |
| Historical witnesses | `.Perona`, `.DeHeerMuir`: `blocks_distinct`, `family_card`, `family_uniform`, `family_covers`, `family_isCover`, `attainment` |
| Seven ordinary exactness statements | `.Numerical`: `exact_v_k_2`, `attainment_v_k_2`, `covering_number_v_k_2` for the seven exact rows |
| Theorem 5 | `.Equality`: `twenty_description`, `twenty_unit_pure`, `twenty_converse` |
| Proposition 2a | `PairConsequences.Arithmetic`: `square_factor_iff`, `determinant_square_parity`, `nonsquare_six`, `no_twisted_six` |
| Proposition 5a | `PairConsequences.Equality`: `equality_description`, `determinant_equality_description`, `equality_converse` |
| Proposition 5b | `PairConsequences.Primitive`: `primitive_parameters`, `primitive_blocks_injective`, `twisted_replication`, `primitive_quotient`, `indexed_primitive_exclusion` |
| Proposition 5c | `PairConsequences.Replication`: `primitive_replication`, `replication_exact` |
| Proposition 6, general indexed bound | `CoveringDesigns.LiftingComparison.Covering`: `CoveringDesigns.LiftingComparison.indexed_lower_bound`; its `Multicover.CoverLower` premise ranges over all residual point and occurrence types |
| 59 earlier lifts | `.Lifting`: `lifted_lower_bound`; `.Lifts`: `ceilings_k` for all rows and `lower_bound_v_k_t` for the 53 compared rows |
| 78 direct additions | `PairConsequences.Numerical`: `indexed_lower_v_k_t`, `lower_bound_v_k_t` for all 78 rows |
| 14 order-six consequences | `CoveringDesigns.C6k_K_2.Numerical`: `indexed_lower_v_k_t`, `lower_bound_v_k_t` in `CoveringDesigns.C6k_K_2` |

The determinant module uses the general incidence Gram identity and
mate-pair determinant theorem. For q=7 and q=9, Lean proves nonsquareness
by placing each determinant strictly between consecutive integer squares.

The construction proof takes traces before padding once, as in
`TwoKMinusTwo.pad_indexed`. The existing Lean construction pads the full
expansion and then restricts and pads again. Both routes preserve coverage
and the same upper bound. The construction module imports no lower bound
or historical witness. The earlier lifts import the order-four **lower-bound** module
and the existing `Multicover.bound` recurrence, not attainment or new
numerical proofs. The direct-addition module instead imports its pair
lower bounds and the universal indexed lifting theorem. The primitive
quotient has no determinant dependency. The general divisibility theorem
remains unchanged.

`twenty_description` returns the actual `Plane 4 I (Fin 5)`, core occupancy,
`NatDescription`, and an actual-point equivalence preserving support and
incidence. The counts in Theorem 5 follow from that plane's proved cardinality
and degree properties. `twenty_converse` exposes the expanded indexed cover,
injective block map, actual point count and arbitrary-label ordinary family.
The unchanged `actualEquiv`, `support_reindex`, `support_relabel` and
`expanded_reindex` provide the point and occurrence transports.

The [Qk_K_2 audit](../../lean/audits/Qk_K_2.lean) checks the numerical,
construction and equality contracts; the [PairConsequences audit](../../lean/audits/PairConsequences.lean)
checks the wider intervals, determinant criterion, equality descriptions,
primitive quotient, replication and 78 direct bounds. The
[order-six audit](../../lean/audits/C6k_K_2.lean) checks the unrestricted
order-six proof and its 14 rows. These audits check full types and transitive
axioms. The policy permits only `propext`,
`Classical.choice` and `Quot.sound`; principal and explicit ordinary contracts
must have exactly that set. Closed arithmetic and witness checks may use
fewer. No admission, new axiom, native proof assertion or external certificate
is a proof premise. Data checks establish provenance and table correspondence;
they are separate from kernel proof compilation and record validation.

The Perona and de Heer–Muir families are transcribed from preserved block
lists, subtracting one from every label and retaining row order. Independent
data checks compare the compressed archives, ordered rows and Lean source.
Lean proves the resulting families' sizes, distinctness and coverage; this
is verification of explicit constructions, not exhaustive search. The five
geometric constructions are not identified with particular generated lists.

See [sources.md](sources.md) for historical attribution and the
[shared verification guide](../../technical-details.md) for reproduction.
