# Exact values of C(4k,k,2)

**Rob Gardiner, with Codex assistance.**

**Theorem 1 (exact family).** For every k≥8,

\[
C(4k,k,2)=20\quad(4\mid k),\qquad
C(4k,k,2)=21\quad(4\nmid k).
\tag{1}
\]

**Abstract.** We prove the lower bounds even when blocks may repeat, and
construct coverings with exactly 20 or 21 distinct blocks on any set of
4k points, as specified in (1). For q≥4 and k≥q, we also prove that a pair
covering on qk points with exactly q(q+1) blocks requires q∣k or (q+1)∣k.

**Introduction and proof outline.** Incidence counting converts equality
into a family of point supports with positive, equal coordinate loads.
Füredi's geometric classification gives a truncated core or a twisted plane.
The load theorem and mate equations then give the divisibility alternatives.
The twisted determinant excludes the second branch at order four. Affine
and weighted projective expansion, with Barker's construction at k=11,
give attainment. The proofs below connect these steps on the original points
and block occurrences; [sources](sources.md) records their attribution.

## 1. Conventions and proved prerequisites

An indexed pair covering is a map B from a finite occurrence set I to the
k-subsets of a finite point set X such that every two-element subset of X
lies in some B_i. Repeated block images are permitted. An ordinary family is
a finite set of k-subsets, so its blocks are distinct. Its elements provide
an indexed covering of the same size. The covering number C(v,k,2) is the
minimum size of an ordinary pair covering on v points.

We use the following included proofs.

* **Geometric equality (Füredi).** If q≥4, |I|=q(q+1), H is an intersecting
  family of distinct (q+1)-subsets of I, and positive real support weights
  give load one at every coordinate, then H contains an actual truncated
  plane of order q on I, or H itself is an actual twisted plane. The exact
  truncated-plane incidence contract and both derived twisted mate relations
  are proved in [PairEquality](../pair-equality/proof.md).
* **Positive core loads.** If such an occupied truncated core has positive
  natural support multiplicities and equal coordinate load k>0, then q∣k.
  The theorem allows all original positive extra supports; its complete
  extension and load classification is in
  [TruncatedPlaneLoads](../truncated-plane-loads/proof.md).
* **Finite planes and expansion.** The existing finite-field constructions
  give the affine and projective planes of prime-power order. Integer fibre
  expansion, padding, restriction and relabelling are proved for actual
  finite sets. Their relevant mechanisms are spelled out in §5 below.

These are the dependency boundary of this proof. No fractional optimization,
general near-equality theorem or unweighted regularity assumption is added.
The historical attribution and source qualifications are in [sources.md](sources.md).

## 2. From actual coverings to geometric equality

**Lemma 2 (incidence bound and equality case).** Let q≥4 and k≥q. Every
indexed pair covering on qk points by k-element blocks has at least q(q+1)
occurrences. At equality, its point supports and normalized multiplicities
satisfy the hypotheses of the geometric equality theorem.

**Proof.** Let q≥4, k≥q and |X|=qk. For p∈X write

\[
S_p=\{i\in I:p\in B_i\},\quad d(p)=|S_p|.
\]

The occurrences through p cover the other qk−1 points. Each contains k−1 of
them, so d(p)(k−1)≥qk−1. If d(p)≤q, the left side is at most qk−q<qk−1.
Thus d(p)≥q+1. Counting all point-occurrence incidences gives

\[
|I|k=\sum_{p\in X}d(p)\ge qk(q+1),
\]

and k>0 implies |I|≥q(q+1).

Suppose equality holds. The displayed sum is then the sum of |X| lower
bounds q+1, so every d(p)=q+1. Define

\[
H=\{S_p:p\in X\},\qquad m(E)=|\{p\in X:S_p=E\}|\quad(E\in H).
\]

H is a set of actual subsets of the **original** I. Its members have size
q+1 and m(E)>0. Distinct supports can be represented by distinct points;
their covered pair shows that the supports intersect. Counting the points
in a single occurrence gives

\[
\sum_{E\in H:\ i\in E}m(E)=k.                 \tag{2}
\]

Therefore w(E)=m(E)/k is positive and has unit coordinate loads, exactly the
input of geometric equality. Only equal support subsets are identified:
the m(E) distinct actual points in a fibre are retained in every load count.
Repeated block images do not affect any argument.

In the truncated-core branch the core consists of actual members of H on I.
Apply the positive core-load theorem with the **original** m and all of H.
It gives q∣k. The auxiliary weights used internally by geometric extraction
play no role in this application.

## 3. Twisted multiplicities and general divisibility

**Theorem 3 (general divisibility and refinement).** Let q≥4 and k≥q.
If an indexed pair covering on qk points by k-element blocks has exactly
q(q+1) occurrences, then q∣k or (q+1)∣k. If q∤k, its occupied support
family is twisted and its multiplicities satisfy (4)–(5).

**Proof.** In the other branch H is the entire actual twisted family. It has q(q+1)
supports, each of size q+1, and degree q+1 at every coordinate. Each support
E has a unique distinct mate E′ meeting it in two coordinates; all its other
distinct intersections have size one. The mate map is an involution.

Sum (2) over I, and count the contribution of each support. Since q+1>0,

\[
\sum_{E\in H}m(E)=qk.                         \tag{3}
\]

Summing (2) over the q+1 coordinates of E gives

\[
(q+1)k=(q+1)m(E)+2m(E')+
                   \sum_{F\ne E,E'}m(F).
\]

Subtract (3), and repeat for E′:

\[
q\,m(E)+m(E')=k,\qquad q\,m(E')+m(E)=k.      \tag{4}
\]

Their difference is (q−1)(m(E)−m(E′))=0. Thus m(E)=m(E′), and

\[
(q+1)m(E)=k\qquad(E\in H).                   \tag{5}
\]

All multiplicities are consequently equal. H is nonempty, so (q+1)∣k.
Together with the core branch this proves general divisibility. Moreover,
if q does not divide k, the original H must be twisted and satisfies (4)–(5).
If neither divisor divides k, equality in the incidence floor is impossible,
and every indexed covering has at least q(q+1)+1 occurrences. Ordinary
families inherit both statements. No prime-power hypothesis occurs here.

## 4. The order-four determinant obstruction

**Proposition 4 (order-four obstruction).** An actual twisted plane of order
four does not exist.

**Proof.** Suppose H is a twisted plane of order four. The verified incidence interface
gives 20 coordinates and 20 supports, with five incidences in every row and
column. It also gives a fixed-point-free involution ν on the coordinates:
the pair {x,ν(x)} has codegree two, and every other distinct coordinate pair
has codegree one. In particular pair coverage is a proved consequence of
the geometric component, not an assumption inferred from the parameters.

Let A be the integer coordinate-by-support incidence matrix. Use any bijection
between the two 20-element index sets to make it square; this only relabels
columns. Let P be the permutation matrix of ν and J the all-ones matrix.
The diagonal and codegrees give

\[
AA^{\mathsf T}=4I+J+P.                        \tag{6}
\]

Split the coordinates into ten pairs of ν. On pair differences (6) acts by
3; on pair sums it acts by 5I₁₀+2J₁₀. More explicitly, after ordering the two
halves of each pair its blocks are 4I+J on the diagonal and I+J off the
diagonal. The invertible rational change of basis with blocks
\(\left(\begin{smallmatrix}I&I\\I&-I\end{smallmatrix}\right)\)
intertwines this matrix with block diagonal matrices 5I+2J and 3I.
The determinant lemma for a rank-one addition gives

\[
\det(5I_{10}+2J_{10})=5^{10}(1+20/5)=5^{11}.
\]

Consequently

\[
(\det A)^2=\det(AA^{\mathsf T})=3^{10}5^{11}. \tag{7}
\]

The exponent of 5 in the right side is odd, so it is not an integer square.
This contradiction excludes the twisted branch. (The formal arithmetic
check equivalently places the right side strictly between 1698014² and
1698015².) For q=4 the equality case must therefore have 4∣k. For every
k≥4, all indexed pair coverings on 4k points have at least 20 occurrences,
and at least 21 if 4∤k. These lower bounds use no construction theorem.

## 5. Attaining ordinary families

**Proposition 5 (construction).** For every k≥8, there is an ordinary pair
covering on any set of 4k points with at most the number of blocks in (1).

**Proof.** For k=4u, the affine plane of order four has 16 points and 20 lines, each
containing four points. Replace each point by u distinct labelled points.
The expanded lines have size 4u=k and the point set has size 16u=4k.
Distinct base points share a line, and two points in the same fibre share
every expanded line through that base point. This is the existing affine
expansion construction, yielding an ordinary family with at most 20 blocks.

Now write k=4u+r, where 1≤r≤3 and u≥r. In the projective plane of order
four choose a line L. Give its five points weight r and the other sixteen
points weight u. The expanded point set is the disjoint union of those
fibres, with size

\[
5r+16u=4k+r.
\]

Every other line meets L once, so its expanded size is r+4u=k.
The selected line has size 5r≤k. A pair of expanded points lies on an
expanded line: distinct base points share a line, and a single base point
also lies on a line when both points belong to its fibre.

Choose any 4k expanded points and intersect each expanded line with them.
Every retained pair remains covered, and each trace has size at most k.
Enlarge each trace to size k inside the chosen set, then discard duplicate
blocks. This gives at most 21 blocks. Relabelling gives the construction
on any set of 4k points.

The same weighted argument works at any prime-power q: a selected line of
q+1 points has weight r, the other q² points weight u, and the total is
q(qu+r)+r. The other lines have size qu+r, and the selected line has size
(q+1)r≤qu+r when r≤u. The formal reusable construction proves this version;
only q=4 is used to establish (1).

For completeness, the line-intersection fact used here is derived from the
existing projective-space construction. Distinct lines are distinct
two-dimensional kernels in a three-dimensional vector space. Their
intersection has dimension at least one by the dimension formula. If it
had dimension two, the kernels, and hence the lines, would coincide.
Its dimension is therefore one, giving exactly one projective point.

The arithmetic range is precise. If k≥8, then u=⌊k/4⌋≥2. For residues 1
and 2 this gives u≥r. For residue 3, failure of u≥3 forces u=2 and k=11.
For that exception use Barker's retained 21 distinct 11-subsets of a
44-point set. Their sizes, distinctness and all 946 pair incidences are
checked independently against the original archive; Lean proves the finite
family properties by ordinary kernel reduction. Relabelling supplies the
witness on any 44-point type. Its historical provenance is retained.

**Assembly of Theorem 1.** Every k≥8 now has an ordinary covering with at most the value in (1).
The matching lower bound forces its number of distinct blocks to equal
that value, even if an intermediate expansion or padding recipe had
duplicate images. This assembles both attainment and universal lower bounds
on every finite point type of cardinality 4k, proving (1).

## Appendix: Lean correspondence and trust boundary

| Mathematical step | Public interface |
|---|---|
| Lemma 2: occurrence floor and forced point degrees | `PairDivisibility.incidence_floor`, `equality_support_size` |
| Original supports and normalized multiplicities | `PairDivisibility.normalized_loads` |
| Theorem 3: equations (4)–(5) | `PairDivisibility.twisted_mate_equation`, `twisted_multiplicity` |
| General necessary condition and structural refinement | `PairDivisibility.divisibility`, `twisted_of_not_dvd` |
| Ordinary compatibility and improved floor | `family_divisibility`, `family_improved_floor` |
| Proposition 4: actual mate pairing and Gram determinant | `TwistedArithmetic.mateEquiv`, `pairedGram_det`, `incidence_gram`, `order_four_determinant` |
| Order-four exclusion | `TwistedArithmetic.no_twisted_four` |
| Indexed lower bounds | `C4k_K_2.indexed_twenty`, `indexed_twenty_one` |
| Proposition 5: weighted projective construction | `PairConstructions.projective_line_intersection`, `weighted_projective` |
| Exceptional historical family | `C4k_K_2.Barker.family_isCover`, `family_card`, `attainment` |
| Theorem 1: arbitrary-label and canonical formula | `C4k_K_2.lower_bound`, `attainment`, `exactness`, `covering_number` |

`C4k_K_2.Examples` applies the general theorem at k=8,9,10,11,15. The
indexed lower interfaces use `Multicover.IsCover B k 2 1`; the final ordinary
contracts use only `IsCover C k 2`, the point cardinality and k≥8. The
cardinality of an ordinary family is never identified with a recipe budget.
Section 5 restricts the expanded lines before padding them once, as in
`TwoKMinusTwo.pad_indexed`. The existing construction proof uses
the existing `weighted_expansion` and `family_reduce_points` interfaces,
which pad before and after restriction. Both routes preserve coverage and
the stated block-count bound; equality of their resulting families is not needed.

For lower bounds alone, import `CoveringDesigns.C4k_K_2.LowerBound`.
The entry `CoveringDesigns.C4k_K_2` additionally supplies attainment and
exactness. General divisibility is independent of determinant machinery;
construction modules are independent of the lower-bound argument. Barker's
data serve provenance and correspondence, not a proof premise. Typed public
contracts and transitive-axiom audits use the unchanged foundational policy.
The only permitted transitive axioms are `propext`, `Classical.choice` and
`Quot.sound`; principal and expanded-contract audits check the exact expected
axiom sets. No admissions, additional axioms, native proof assertions or
external proof certificates are used. Source/data checks, Lean compilation
and validation of the resulting verification records are separate checks.
See the [shared guide](../../technical-details.md) for verification commands.
