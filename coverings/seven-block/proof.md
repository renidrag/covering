# (7a+4,3a+2,2) coverings with 7 blocks

**Rob Gardiner, with AI assistance. 24 October 2026.**

## Abstract

For every integer a≥1, a (7a+4,3a+2,2) covering with 7 blocks has one of
two forms based on the Fano plane. We keep distinct points separate even
when they belong to exactly the same blocks. The proof allows repeated
block occurrences, then shows that the blocks must be distinct. The two
forms are not isomorphic and both give C(7a+4,3a+2,2)=7.

The classification follows from earlier results described in
[sources.md](sources.md). Here we prove it directly and formalise the proof
in Lean. The appendix links the mathematical steps to the Lean declarations.

## Introduction, conventions and main theorem

Let V and I be finite sets of actual points and occurrence labels. A covering
is a map i↦Bᵢ⊆V, with |V|=7a+4, |I|=7, |Bᵢ|=3a+2 and every two-element
subset of V contained in at least one Bᵢ. Its point support is Sₓ={i:x∈Bᵢ}.
Two indexed coverings are equivalent if there are bijections of points and
occurrences preserving membership. This is stronger information than an
identification of their sets of distinct point supports.

Identify the seven positions with nonzero vectors of F₂³, labelled 1,…,7
in binary. The lines are 123,145,167,246,257,347,356. For a weight g on these
seven lines and two four-subsets H,G of positions, define the actual point
set to be the disjoint union of {p,q} and the sets {(L,j):0≤j<g(L)}. The
block at i contains (L,j) exactly when i∈L, and p or q exactly when i∈H or
G respectively. A fibre of weight zero is empty; no other points merge.

**Main theorem.** For every a≥1 every covering above is equivalent to
exactly one of the following forms (uniqueness is of form, not of bijection).

| Form | Weights | Exceptional supports | Codegree of p,q |
|---|---|---|---:|
| I | a+1 on 123,145; a on the other five lines | 2467 and 3567 | 2 |
| II | a+|L∩124|−1 on each L | both 3567 | 4 |

Both forms cover all pairs with 7 distinct blocks, so they give the upper
bound C(7a+4,3a+2,2)≤7. Section 6 proves the matching lower bound. Type II has an empty fibre on 356 at a=1.

The proof retains the exact slack in the existing Stanton intersecting-triple
count. Complete pair shadow recognises the Fano geometry, after an explicit
boundary argument at a=2. Row equations recover the multiplicities and high
supports. The a=1 case uses the unchanged ordinary Stanton classification
through a proved ordinary/indexed adapter; it is a separate dependency.
Attribution and the limits of historical priority are in [sources.md](sources.md).

## 1. Independent count, including duplicate supports

Let I have b elements, b≥r≥2, and let X be a finite set of m≥0 **actual
point indices**. For each x∈X let S_x⊆I have size r. Require S_x∩S_y≠∅
for distinct x,y. Distinct points may have identical supports. Put
d_i=|{x:i∈S_x}|, n_ij=|{x:i,j∈S_x}|, h_xy=|S_x∩S_y| and M=binom(b,2)>0.
Euclidean division gives m binom(r,2)=MA+s with A≥0, 0≤s<M.

Counting unordered pairs of actual point indices, first with one and then
with two common positions, gives

    E := Σ_i binom(d_i,2) − binom(m,2) = Σ_{x<y}(h_xy−1),
    Q := Σ_{i<j} binom(n_ij,2) = Σ_{x<y}binom(h_xy,2).

All subtraction here is in the integers. Expanding the quadratic and using
Σ n_ij=MA+s gives

    Q − [M binom(A,2)+sA]
       = (1/2)Σ_{i<j}(n_ij−A)(n_ij−A−1) =: δ ≥0.

Each product is nonnegative for every integer n_ij−A, including negative
values. Write the bracket as Qmin. The elementary identity
r(h−1)−h(h−1)=(h−1)(r−h) yields

    rE−2Qmin = Σ_{x<y}(h_xy−1)(r−h_xy)+2δ.           (R1)

Here 1≤h_xy≤r is essential for nonnegativity, but not for the algebraic
identity. Equal supports have h=r and contribute zero to the first sum;
their contribution to E and Q is retained. The formulas also hold for
m=0, m=1, r=2 and r=b. At r=3 the first sum counts exactly the pairs of
distinct points with intersection size two, denoted A₂. No collapsing of
point indices has occurred.

## 2. Degree profiles and exact arithmetic

Two occurrences through a point can cover at most 2(k−1)=6a+2 of its
7a+3 companions. Every point therefore has degree at least three, and
7k−3v=2 leaves either one degree-five point or two degree-four points.

For one degree-five point the m=7a+3 low points have row counts
(3a+1)^5(3a+2)^2. Direct expansion gives
E=7a²−a−1, A=a, s=9, Qmin=21 binom(a,2)+9a and
3E−2Qmin=−3. This contradicts (R1).

For degree-four points p,q put z=|S_p∩S_q|. Coverage and support sizes
give 1≤z≤4. There are m=7a+2 low points, with row counts
(3a)^z(3a+1)^(8−2z)(3a+2)^(z−1). Now

    E=7a²−3a+z−2, A=a, s=6,
    Qmin=21 binom(a,2)+6a,
    A₂+2δ=3(z−2).                                    (R2)

In particular z≥2. This checks the claimed identity without assuming
that all seven positions or all pairs occur in the low shadow.

## 3. Complete shadow, especially a=2,z=4

For z=2, δ=0 and n_ij∈{a,a+1}. For z=3, integrality gives δ≤1.
A zero n_ij costs a(a+1)/2≥3 when a≥2, so is impossible. For z=4,
δ≤3, and the same cost is ≥6 when a≥3.

At a=2,z=4 a zero costs exactly three. It would force δ=3, A₂=0,
one zero and twenty entries in {2,3}; any second zero already exceeds
the budget. Distinct low supports then intersect in exactly one position,
so their three-element sets of position-pairs are disjoint. The shadow
has size divisible by three. It cannot have size twenty. This closes
the boundary; the generic strict-positivity estimate alone does not.

## 4. Independent seven-position shadow argument

Choose a member abc of a pairwise-intersecting triple family H with full
pair shadow, and let W be the remaining four positions. An edge through
P⊂W must be P plus one of a,b,c. Its complementary pair W\P must use
the same third position, or the two triples are disjoint. Nor can P
use a second third position. Thus the three perfect matchings of W
receive colours a,b,c.

If all colours are a, any edge omitting a must meet abc, leaving at most
two positions to meet all six edges of K4 on W. This is impossible: a
vertex cover of K4 has size at least three. All edges contain a. Full
shadow then forces every one of the fifteen triples aij, i,j≠a: the
family is the full star, not an unspecified subset of it.

If exactly two colours occur, call the repeated colour a, the other b,
and the unused one c. To cover cx, x∈W, a third position a misses the
b-matching edge avoiding x; a third position b misses an a-edge avoiding
x. A third position y∈W would have to make xy a vertex cover of the
a-coloured four-cycle, hence an opposite pair. These are precisely the
b-matching pairs, so this triple misses the complementary b-edge. This
excludes two colours.

With three colours all different, abc and the six matching triples cover
each of the 21 pairs once. They are seven pairwise-intersecting lines of
the Fano plane. A nonline triple meets exactly six of these lines: its
three points give nine incidences, with three different pair-lines each
counted twice, and no line counted three times. Such a triple misses
one line, so H has no additional member. This also constructs the usual
binary-vector coordinates and establishes the required plane uniqueness.

Apply this to the distinct low supports (only for this geometry step do
we temporarily forget their positive multiplicities). A star would put
all 7a+2 low points in one block, exceeding capacity 3a+2. Thus all seven
Fano lines occur. They have no partial two-position overlaps, so A₂=0;
(R2) rules out z=3 by parity.

## 5. Recovering all multiplicities and high supports

Number positions by the nonzero vectors 1,…,7 of F₂³; line triples have
xor zero. Write g_L for the number of actual low points supported on L.

**Type I (z=2).** Each position pair is on a unique line and its count
n_ij equals g_L. Since δ=0, g_L∈{a,a+1}. The total 7a+2 gives exactly
two augmented lines L₁,L₂. Uniform row capacity forces
1_H+1_G=2·1−1_L₁−1_L₂. Hence H,G omit their intersection, both contain
the two positions outside their union, and divide the four arm positions
two each. Taking a whole arm would make the other high support disjoint
from that line. The only divisions are the two cross divisions. Fano
automorphisms are transitive on line pairs; for 123 and 145 the linear
map fixing 1,4 and sending 2 to 3 swaps the cross divisions. One form is

    g_123=g_145=a+1; other g_L=a;
    H=2467, G=3567.

**Type II (z=4).** H=G=I\T. Since every low line occurs, T cannot be a
line. Put g_L=a+u_L. The row equations are Σ_{L∋i}u_L=2·1_T(i).
The incidence matrix has row Gram matrix 2I+J, positive definite over
the reals, hence is invertible. The unique solution is
u_L=|L∩T|−1: at i, Σ_{L∋i}|L∩T|=3+2·1_T(i).
A nonline triple has three secants, three tangents and one disjoint line.
Thus the multiplicities are (a+1)^3 a^3 (a−1). Its three vector points
are independent, so GL(3,2) is transitive on choices of T. Take

    T=124; H=G=3567.

Conversely these are covers: their row capacities are k, their low
supports intersect, each high complement is a nonline triple, and their
high supports intersect. All distinct actual points, including equal
supports, are counted in these statements. Any pair covering for these
parameters has b≥ceil(3v/k)=7, since 3v>6k. If a seven-occurrence
construction repeated a block, deduplication would retain coverage with
at most six blocks, a contradiction. This proves distinctness uniformly.
For a≥2 there is also a direct check: a line through one of two positions
but not the other has a positive fibre, so the two rows differ.

For a=1 the constructions still work; the Type-II disjoint-line fibre
has size zero. Deduplication of any seven-occurrence cover cannot reduce
its size, by the preceding lower bound. The ordinary Stanton theorem
therefore applies. The two constructions belong to different Stanton
classes: the uniquely degree-four points have codegrees two and four.
Since Stanton gives exactly two ordinary classes, these exhaust them.
Reinserting the bijection between the seven occurrence labels and their
distinct block images gives the indexed conclusion. No stronger a=1
shadow claim is needed or made.


## 6. Assembly and exact covering number

For a≥2, §2 leaves precisely two degree-four points, §3 proves the complete
low pair shadow including its boundary, §4 identifies the seven Fano lines,
and §5 recovers exactly the displayed weights and exceptional supports.
The positive low fibres are transported individually by bijections, then
combined with the two exceptional points; this gives a bijection of actual
point sets. The position coordinates give the occurrence bijection. Their
membership equations prove equivalence of coverings.

For a=1, the degree lower bound excludes a cover with at most six block
images, so the seven occurrences map bijectively to their ordinary family.
The two constructed ordinary families are nonisomorphic because their unique
degree-four pair has different codegree. Stanton's exhaustive two-class
theorem therefore puts every ordinary family in one of these two classes.
Composing the point equivalence and the occurrence-to-image bijections yields
the required indexed equivalence. The omitted Type-II fibre causes no loss
of point identity and is not used in the a≥2 shadow argument.

For any number b of occurrences the same local count gives degree at least
three. Hence (3a+2)b≥3(7a+4)>6(3a+2), so b≥7. The two explicit families
use 7 blocks. A bijection gives the same construction on any set of
7a+4 points. This proves the numerical conclusion as well
as the classification.

## Appendix A. Lean correspondence and evidence boundary

The formalisation separates the general a≥2 proof from the a=1 adapter.
`Foundations.Intersecting` supplies both actual-index double counts;
`Multicover.Links` preserves parent occurrence subtypes; `Foundations.Relabelling`
and `Multicover.Family` supply ordinary transport and deduplication. The
existing Fano module imports Stanton and is not an input to the general branch.

The supported entry for a≥2 is `CoveringDesigns.SevenBlock.Core`. The entry
`CoveringDesigns.SevenBlock` adds only the a=1 Stanton adapter. In the table,
names without a prefix lie in the `CoveringDesigns.SevenBlock` namespace.

| Statement | Lean declarations |
|---|---|
| Signed identity and nonnegative integer imbalance (§1) | `support_slack_identity`, `support_imbalance_identity`, `support_imbalance_nonneg`, `partial_overlap_nonneg`, `partial_overlap_three` |
| Degree profile and exact slack (§2) | `covering_degree_profile`, `covering_slack` |
| Complete low shadow, including a=2 (§3) | `zero_partial_shadow_divisible`, `shadow_positive`, `low_support_shadow` |
| Universal seven-position recognition (§4) | `complete_pair_shadow`, `low_support_fano` |
| Multiplicities and exceptional supports (§5) | `fano_incidence_identity`, `fano_weights_unique`, `exceptional_support_normal_form`, `classification_ge_two` |
| Actual point identities (§§5–6) | `support_fibre_isomorphism`, `IndexedIsomorphic` |
| Ordinary/indexed a=1 adapter (§6) | `indexed_ordinary_equivalence`, `ordinary_isomorphism_to_indexed`, `classification_one` |
| Exhaustive and unique form for every a≥1 | `classification`, `classification_expanded` |
| Lower seven, constructions, distinctness and nonisomorphism | `seven_le_card`, `blocks_injective`, `template_isCover`, `template_injective`, `templates_not_isomorphic` |
| Attainment and exactness on arbitrary labels | `template_attainment`, `covering_number_on` |

`TemplatePoint a tag` is a disjoint sum of the two exceptional points and
the dependent finite fibres. `false` denotes Type I and `true` Type II;
Lean labels 0,…,6 correspond to positions 1,…,7 above. The formal proof
recovers integer weights directly with the Fano incidence identity rather
than introducing a second real-matrix invertibility argument. Fixed Fano
incidences and binary-frame normalisations use kernel reduction. The complete
shadow theorem uses the universal matching-colour proof, not enumeration of
candidate covering families or a bounded range of a.

Full typed audits cover every nonprivate theorem outside internal bookkeeping,
including all hypotheses needed for signed nonnegativity and boundary cases.
The principal and expanded contracts are required to have exactly the three
foundational axioms `propext`, `Classical.choice`, `Quot.sound`; auxiliary
contracts may use a subset. There are no admissions, new axioms, native
assertions or external proof certificates. Source/data checks and validation
of a recorded run are separate from Lean compilation. The
[shared verification guide](../../technical-details.md) explains setup,
focused verification and checking the resulting records.
