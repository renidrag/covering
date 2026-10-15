# C(11,5,2) = 7 and the two minimum covering types

**Rob Gardiner**

A $(11,5,2)$ covering is a family of distinct five-element subsets, called
blocks, of an eleven-point set, containing every pair of points in at least
one block. The minimum number of blocks is denoted by $C(11,5,2)$.
Two coverings are isomorphic if a bijection of their point sets maps one
block family exactly onto the other.

**Theorem.** $C(11,5,2)=7$. Every seven-block covering is isomorphic to
exactly one of two covering types. Both types are completions of the
seven-block template derived below.

**Proof provenance: a reconstruction of a known theorem.** GPPT attribute
the classification to R. G. Stanton in their Theorem 3.1. This is a
self-contained proof of that result, developed from the project owner's
structural reconstruction of 12 October 2026 and shortened during its Lean
formalization. Stanton's original chapter has not been obtained, so this
is not claimed to translate or reproduce his argument.

The template is the established one recorded by GPPT and Mullin; the
counting and structural deductions below supply a proof of its completeness
and derive the geometry needed by later components. The
[source comparison](#sources-and-contribution) distinguishes the historical
theorem and construction from this reconstruction, without claiming
historical novelty for the argument. Appendix A maps the argument to Lean
declarations, and Appendix B states the formal contracts and the scope of
the checks.

**Dependencies and route.** The proof uses elementary finite counting and
set intersections; no twelve- or thirteen-point result is a prerequisite.
Sections 2–3 force a block of five degree-three points. Sections 4–5
show that the other blocks determine two doubled edges on it. Section 6
then recovers the template, and Section 7 identifies and separates its
two completion types. Section 8 derives the local geometry used by GPPT,
including marked couples and the Fano plane on the seven block rows. All
these conclusions follow for an arbitrary minimum covering from the
template established in Sections 1–7.

## 1. The lower bound

Write $r(x)$ for the number of blocks containing a point $x$. Its ten
partners must be covered by those blocks, each of which contains only four
other points. Thus $r(x)\ge3$. If there are $b$ blocks, counting point-block
incidences gives

$$
5b=\sum_x r(x)\ge11\cdot3=33.
$$

Consequently $b\ge7$. Section 6 constructs seven-block coverings, giving
equality.

For the classification, fix an arbitrary seven-block covering
$\mathcal C$ on a point set $V$. Its 35 incidences leave exactly two
incidences above the lower bound three at each point.

## 2. An inequality for intersecting triples

We first prove a counting lemma used twice below.

**Lemma.** Let $T_1,\ldots,T_m$ be pairwise-intersecting three-element
subsets of a seven-element set, and let $d_i$ count the triples containing
its $i$th vertex. Equal triples at different indices are counted separately.
Then

$$
\sum_{i=1}^7\binom{d_i}{2}\ge\binom m2+2m-14.
$$

**Proof.** For each vertex pair $\{i,j\}$, let $n_{ij}$ count the triples
containing it. Define, using integer subtraction,

$$
E=\sum_i\binom{d_i}{2}-\binom m2,
\qquad
Q=\sum_{i<j}\binom{n_{ij}}2.
$$

Count a vertex together with two distinct triple indices, and then a
vertex pair together with two distinct triple indices. These two counts give

$$
E=\sum_{a<b}(|T_a\cap T_b|-1),
\qquad
Q=\sum_{a<b}\binom{|T_a\cap T_b|}{2}.
$$

Every intersection has size $h\in\{1,2,3\}$, and
$2\binom h2\le3(h-1)$, so $2Q\le3E$.
Also, $\binom n2\ge n-1$ for every nonnegative integer $n$.
There are 21 vertex pairs, and each triple contains three pairs. Therefore

$$
Q\ge\sum_{i<j}(n_{ij}-1)=3m-21.
$$

It follows that $3E\ge6m-42$, hence $E\ge2m-14$, as required.
This argument includes equal triples, whose intersection has size three.
$\square$

## 3. The point degrees and a distinguished block

The nonnegative integers $r(x)-3$ sum to two. Its partitions $1+1$ and $2$
permit only two degree patterns: nine points of degree three and two of
degree four, or ten points of degree three and one of degree five.

Represent each degree-three point by the triple of block indices containing
it. These incidence triples pairwise intersect, since every pair of original
points is covered.

Suppose there is a degree-five point. The other ten points give ten
incidence triples on the seven block indices. Five blocks contain four of
these points and the other two contain five, so the vertex degrees of this
indexed triple family are $(4,4,4,4,4,5,5)$. The lemma would require

$$
50=5\binom42+2\binom52
\ge\binom{10}{2}+2\cdot10-14=51,
$$

a contradiction. Thus there are exactly nine degree-three points and two
degree-four points.

Suppose the two degree-four points together meet every block. Their eight
incidences then occupy seven blocks, so exactly one block contains both.
The incidence triples of the other nine points have vertex degrees
$(3,4,4,4,4,4,4)$. The lemma would now require

$$
39=\binom32+6\binom42
\ge\binom92+2\cdot9-14=40,
$$

another contradiction.

There is consequently a block $A$ consisting entirely of degree-three
points. Put $X=V\setminus A$, so $|A|=5$ and $|X|=6$.

## 4. The six other blocks

First, any two distinct blocks intersect in between one and three points.

To rule out disjoint blocks $B,D$, let $z$ be the lone point outside
$B\cup D$. At least three of the other five blocks contain $z$.
A block containing $z$ covers at most four pairs between $B$ and $D$:
if it uses $u$ points of $B$ and $v$ of $D$, then $u+v\le4$ and
$uv\le4$. Any other block covers at most six such pairs, since
$u+v\le5$. These product bounds follow from $4uv\le(u+v)^2$
and integrality. Neither $B$ nor $D$ covers a cross pair. If $q\ge3$ of
the other five blocks contain $z$, they supply at most
$4q+6(5-q)=30-2q\le24$ occurrences of the 25 required cross pairs,
which is impossible.

For the upper bound, an intersection of size at least four contains a
degree-three point $x$, since only two points have degree four. Those two
blocks have union of size at most six. The third block through $x$ adds
at most four new points, so the three blocks cannot meet all eleven points.
That contradicts coverage of every pair containing $x$.

Now suppose a block $B\ne A$ meets $A$ in three points. For each point
$x\in A\cap B$, let $D_x$ be the third block through $x$. Every point of
$X\setminus B$ must be in $D_x$ to cover its pair with $x$. This set has
four points, forcing

$$
D_x=\{x\}\cup(X\setminus B).
$$

In particular, $D_x\cap A=\{x\}$. Different choices of $x$ give
distinct blocks intersecting in the same four points of $X$, contrary to
the bound just proved.

Thus each block other than $A$ meets $A$ in one or two points. The five
points of $A$ each have two further incidences, so these six intersection
sizes sum to ten. Exactly four blocks meet $A$ in two points, and two
meet it in one point. Call the latter two the singleton blocks.

Call a two-point intersection with $A$ an **edge**, and the three-point
$X$-part of its block its **trace**. The four edges are indexed by their
distinct blocks; two edges are allowed to be equal as two-point sets.
If the edges of two distinct blocks meet, their common degree-three point
has no further block beyond $A$ and those two. Its pairs with $X$ force
the two three-point traces to cover $X$. Since $|X|=6$, the traces are
disjoint and complementary.

## 5. The two doubled edges

The four traces cannot all be parts of one partition $X=T\sqcup T^c$,
where complements in this section are relative to $X$. Such traces cover
none of the nine pairs between $T$ and $T^c$. The two remaining blocks
have four-point $X$-parts and can cover at most four cross pairs each.

The four traces are distinct. Indeed, two blocks with the same trace $T$
would have disjoint edges, since meeting edges have complementary traces.
Every remaining edge must meet one of these two edges: a pair cannot
avoid four of the five points of $A$. Both remaining traces would therefore
be $T^c$, contradicting the preceding obstruction.

Choose traces $T,W$ from different complementary partitions. Their edges
are disjoint. Each remaining edge meets one of them, so its trace is
$T^c$ or $W^c$. Distinctness forces one of each. We may therefore order
the traces as

$$
T,\quad T^c,\quad W,\quad W^c.
$$

The union of the edges belonging to $T,T^c$ is disjoint from the union of
those belonging to $W,W^c$: a meeting across the two groups would force
two traces to be complementary, contrary to the choice of partitions.

Every point of $X$ occurs exactly twice in these four blocks. Its degree
is at least three, so it must occur in at least one of the two remaining
blocks. If their four-point $X$-parts are $U,V$, then

$$
U\cup V=X,\qquad |U\cap V|=2.
$$

Consequently $P=U\setminus V$ and $Q=V\setminus U$ are disjoint pairs.

We now show that the edges belonging to each complementary trace pair are
equal. Suppose the edges for $T,T^c$ differ. Choose a vertex exclusive to
each edge. Each chosen vertex lies on exactly one of the four edges, and
has degree three, so it belongs to exactly one of the two singleton
blocks. Those vertices are distinct and must use different singleton
blocks, since each such block meets $A$ in only one point.

After possibly interchanging $U,V$, coverage at these vertices forces
$T^c\subseteq U$ and $T\subseteq V$. Hence
$P\subseteq T^c$ and $Q\subseteq T$.
None of the four pairs between $P,Q$ is covered by $U,V,T,T^c$.
They must all be covered by $W$ or $W^c$.
Choose $p_0\in P$ and $q_0\in Q$. They must lie together in one of
$W,W^c$. Every point of $P$ must then lie with $q_0$, and every point of
$Q$ with $p_0$, forcing all four points into that same three-point part.
This is impossible.

The same argument applies to the edges for $W,W^c$. We have two disjoint
pairs $F,G\subset A$, each used as an edge twice. Their four points have
used both incidences outside $A$, so both singleton blocks meet $A$ in
its remaining point $a$.

The covering has therefore acquired the form

$$
\begin{aligned}
&A=\{a\}\sqcup F\sqcup G,\\
&F\cup T,\quad F\cup T^c,\quad G\cup W,\quad G\cup W^c,\\
&\{a\}\cup U,\quad \{a\}\cup V.
\end{aligned}
$$

## 6. The forced template and its completions

Put $k=|T\cap W|$. The four cells of the two partitions have sizes
$k,3-k,3-k,k$. The cases $k=0,3$ would make $T,W$ complementary or equal,
so $k=1$ or $2$. Interchanging $W,W^c$ if necessary gives cell sizes
$1,2,2,1$. Write

$$
T\cap W=\{s\},\quad T\cap W^c=C,\quad
T^c\cap W=D,\quad T^c\cap W^c=\{t\}.
$$

Here $C,D$ are disjoint pairs, and $X=\{s,t\}\sqcup C\sqcup D$.
A pair misses both traces of one partition exactly when its endpoints
lie in opposite parts. Missing all four traces means lying in opposite
cells of both partitions. Thus the pairs of $X$ not covered by the four
edge blocks are exactly $\{s,t\}$ and the four pairs between $C,D$.

No such uncovered pair can join $P=U\setminus V$ to $Q=V\setminus U$.
Suppose neither $P$ nor $Q$ equals $\{s,t\}$. Both then meet $C\cup D$.
Those meetings must all lie in the same one of $C,D$, to avoid an
uncovered cross pair. Since $P,Q$ are disjoint and that side has only
two points, each meeting has size one. Each of $P,Q$ must consequently
take one of $s,t$, making $\{s,t\}$ an uncovered pair between them.
This is impossible.

After interchanging $U,V$ if necessary, we therefore have

$$
Q=\{s,t\},\qquad U=C\cup D,\qquad V=\{s,t\}\cup R,
$$

Indeed, $V\setminus U=\{s,t\}$ forces the four-set $U$ to avoid
$s,t$, hence to equal $C\cup D$. Put $R=U\cap V$, which has size two;
then $V=(V\setminus U)\sqcup R=\{s,t\}\sqcup R$. The seven blocks are

$$
\boxed{\begin{aligned}
&\{a\}\cup F\cup G,\\
&F\cup\{s\}\cup C,\qquad F\cup\{t\}\cup D,\\
&G\cup\{s\}\cup D,\qquad G\cup\{t\}\cup C,\\
&\{a\}\cup C\cup D,\\
&\{a,s,t\}\cup R.
\end{aligned}}
$$

All seven cells $\{a\},\{s\},\{t\},F,G,C,D$ are pairwise disjoint and
together contain the eleven points.

Conversely, every choice of the two-point set $R\subseteq C\cup D$
produces a covering. In fact, replacing the last block by the triple
$\{a,s,t\}$ already covers every pair. Each of the six choices of two
different groups among $F,G,C,D$ appears together in one full block.
The point $a$ meets all four groups in the first and sixth blocks;
$s,t$ meet them in the four middle blocks. Pairs within any group
are covered there, and pairs among $a,s,t$ lie in the last triple.
Adding $R$ makes that last block a five-set. It contains all three of
$a,s,t$, whereas each other block contains exactly one. The two blocks
associated with each of these distinguished points use different unions
of pair cells. Thus the seven blocks are distinct, proving
$C(11,5,2)=7$.

## 7. Exactly two isomorphism types

There are two possibilities for $R$: it is a whole pair $C$ or $D$, or
it takes one point from each pair. Permuting within each pair preserves
the partial template. Simultaneously interchanging $C,D$ and $s,t$
also preserves it. These permutations identify all choices within
each of the two possibilities.

To distinguish them, number the six full blocks in the displayed order
as $B_1,\ldots,B_6$, and let $B_7=\{a,s,t\}\cup R$. Among the first six,
the pairs $(B_1,B_6),(B_2,B_4),(B_3,B_5)$ intersect in one point; all
other pairs intersect in two. None intersects another in three points.

Writing $c=|R\cap C|$ and $d=|R\cap D|$, the remaining intersections are

$$
\bigl(|B_7\cap B_1|,\ldots,|B_7\cap B_6|\bigr)
=(1,1+c,1+d,1+d,1+c,3).
$$

| Completion | Intersections with $B_1,\ldots,B_6$ |
|---|---|
| Whole pair $R=C$ | $1,3,1,1,3,3$ |
| Transversal | $1,2,2,2,2,3$ |

The whole-pair type therefore has a block meeting at least two distinct
other blocks in three points. The transversal type has only one pair
of blocks intersecting in three points, namely $B_6,B_7$, so has no such
block. This property is invariant under relabelling and separates the two
types. It is also the invariant used in Lean.

For explicit examples, take
$a=1$, $s=2$, $t=3$, $F=\{4,5\}$, $G=\{6,7\}$,
$C=\{8,9\}$ and $D=\{10,11\}$. The first six blocks are

$$
\begin{gathered}
\{1,4,5,6,7\},\quad \{2,4,5,8,9\},\quad \{3,4,5,10,11\},\\
\{2,6,7,10,11\},\quad \{3,6,7,8,9\},\quad \{1,8,9,10,11\}.
\end{gathered}
$$

Use $\{1,2,3,8,9\}$ as the seventh block for the whole-pair type,
or $\{1,2,3,8,10\}$ for the transversal type.
These are isomorphic to the library's representatives with tags
`true` and `false`, respectively; the library uses zero-based labels.

This proves the stated classification. $\square$

## 8. The intrinsic geometry used by GPPT

We derive the local properties needed in the twelve- and thirteen-point
proofs. Keep the template of Section 6, including its arbitrary completion
$R$. Put $Z=\{a,s,t\}$ and $S=Z\cup R$. Call the six blocks other than $S$
**full blocks**.

Regard the four disjoint pairs $F,G,C,D$ as the vertices of a complete
graph on four vertices. Each edge gives a full block: take its two endpoint
pairs and add the point indicated below.

| Added point | Edges |
|---|---|
| $a$ | $FG,\ CD$ |
| $s$ | $FC,\ GD$ |
| $t$ | $FD,\ GC$ |

Each row is a perfect matching. Adjacent edges have different added points;
disjoint edges have the same added point.

### 8.1. Couples, spouses and the short block

For distinct points $x,y$, let $\lambda(x,y)$ be their pair multiplicity.
A two-point set is a **couple** if its multiplicity is at least three.
This definition uses the completed covering, independently of its labels.
The full-block counts are:

| Pair of points | Number of full blocks containing it |
|---|---:|
| The two members of one of $F,G,C,D$ | 3 |
| Two different members of $Z$ | 0 |
| Any other distinct pair | 1 |

The first count is the number of edges through a graph vertex. The second
holds because each full block contains one member of $Z$. For the last,
two different couples determine one edge, while a couple and a member of
$Z$ determine the unique incident edge in that member's matching.

The completed block adds one occurrence precisely for pairs contained in
$S$. Thus the couples are exactly $F,G,C,D$. They partition the eight
points outside $Z$; each such point has a unique **spouse**. Every full
block contains two couples, while $S$ contains at most one. Hence $S$ is
intrinsically the unique block containing at most one couple. It is called
the **short block**, although after completion it too has five points.

Each couple-point occurs in three full blocks, and each member of $Z$ in
two. Therefore the points of $R$ have degree four and all others have degree
three. The **short points**, defined as the degree-three points in the short
block, are exactly $a,s,t$. A degree-three point need not be a short point.
The degree-four points, also called **free points**, lie in the short block
and have spouses. Spouses have identical incidence columns among the full
blocks; their completed columns can differ if exactly one belongs to $R$.

### 8.2. Intersections and multiplicity two

Two full blocks correspond to two graph edges. Adjacent edges give
intersection equal to their common couple; disjoint edges give intersection
equal to their common short point. Distinct full blocks therefore intersect
in one or two points. The short block meets each full block in its short
point and at most the two additions in $R$, recovering the bound of three
on intersections of distinct blocks.

The count table also proves the following facts used later.

- Each couple occurs in exactly three full blocks. A block containing one
  spouse without the other must be the short block.
- Every pair containing a nonshort point is covered by a full block.
- Every full block contains exactly one short point. A block containing
  two distinct short points must be the short block.
- The two full blocks carrying any one short point intersect exactly in it.
- A pair in two distinct full blocks must be a couple, so lies in three
  full blocks. No pair has full-block multiplicity two.
- If $\lambda(x,y)=2$, then $x,y$ lie in the short block and at least one
  has degree four.

For the last fact, the full-block count must be one: zero can rise only to
one, while three cannot fall to two. The second occurrence is in $S$.
The pair cannot consist of two short points, so one of its members is in
$R$ and has degree four. This is GPPT's pair-multiplicity-two rule.

### 8.3. Marking any couple

Choose any intrinsic couple $K$. For $z\in Z$, let $K_z$ be the other
endpoint of the edge through $K$ in the matching labelled $z$:

| $K$ | $K_a$ | $K_s$ | $K_t$ |
|---|---|---|---|
| $F$ | $G$ | $C$ | $D$ |
| $G$ | $F$ | $D$ | $C$ |
| $C$ | $D$ | $F$ | $G$ |
| $D$ | $C$ | $G$ | $F$ |

The three **marked triads** $T_z=K_z\cup\{z\}$ partition the nine points
outside $K$. The three full blocks containing $K$ are exactly $K\cup T_z$.
The selected point of $T_z$ is $z$, its unique short point. If
$\{z,z',z''\}=Z$, the other full block carrying $z$ is

$$
M_z=\{z\}\cup(T_{z'}\setminus\{z'\})
              \cup(T_{z''}\setminus\{z''\}).
$$

Its graph edge is the edge disjoint from $KK_z$ in the matching labelled
$z$. The complete covering is consequently

$$
\{S\}\ \cup\ \{K\cup T_z:z\in Z\}\ \cup\ \{M_z:z\in Z\}.
$$

This works for every couple and both completion types. The short block can
meet $K$, or contain all of it. In the latter case four blocks contain
$K$, but only three are full blocks; those three define the triads.

Every $M_z$ meets every triad, in its own selected point or in the other
triad's two nonselected points. The short block meets every triad because
it contains all selected points. In particular, every block not containing
the whole marked couple meets all three triads. The triad order is a choice
of coordinates; the short block, short points and spouse relation are
intrinsic.

### 8.4. The Fano plane on the seven rows

Here the points of the incidence plane are the seven **block rows**, not
the eleven original points. Keep the row order $1,\ldots,7$ of Section 7.
Define seven triples of row indices:

$$
\begin{array}{lll}
L_F=\{1,2,3\},&L_G=\{1,4,5\},&L_C=\{2,5,6\},\\
L_D=\{3,4,6\},&L_a=\{1,6,7\},&L_s=\{2,4,7\},\\
&&L_t=\{3,5,7\}.
\end{array}
$$

The first four consist of the edges incident with one graph vertex; the
last three consist of a matching and row 7. They form a **Fano plane**:
seven triples in which every pair of rows belongs to exactly one triple
and any two triples meet.

Indeed, two full rows corresponding to adjacent graph edges lie in the
unique line of their common couple. Two disjoint edges lie in the unique
line of their common short point. Row 7 and a full row lie in the unique
line of that full row's short point. For intersections of lines, two
couple-lines share their joining edge; a couple-line and a short-point
line share the incident edge in that matching; two short-point lines share
row 7. This proves both required properties.

The **column** of an original point is the set of rows containing it. A
short point $z$ has column $L_z$. A point in a couple $K$ has column $L_K$
if it is outside $R$, and $L_K\cup\{7\}$ if it belongs to $R$. Thus every
column contains a line, and every degree-three column is itself a line.

**Five-line rigidity.** Two Fano planes on the same row set sharing at
least five lines are equal.

To prove this, at most two lines of the first plane are absent from the
second. Suppose a line $T$ of the second is absent from the first. Each
pair in $T$ belongs to a line of the first plane, which cannot be a common
line: uniqueness through that pair in the second plane would make it $T$.
Hence the three pairs of $T$ are covered by at most two missing lines.
Two pairs lie in one missing triple; their union is $T$, so that triple
equals $T$, a contradiction. Equality follows since both planes have seven
lines.

Consequently five **distinct degree-three columns** that are lines of a
proposed plane identify it with the covering's plane. Five distinct points
alone do not suffice: spouses can have identical columns. Every column
then meets every line of the identified plane, since it contains a line
and any two lines meet. This is the incidence property used in GPPT's
projective branch.

All these properties are preserved under point relabelling and the induced
relabelling of block rows. No coordinate choice restricts the covering.

## Sources and contribution

The classification theorem is attributed to Stanton; the structural
reconstruction and its main ideas were supplied by the project owner.
During formalization, the initial degree contradictions were combined
using the indexed-triples inequality, the three-point intersection case
was shortened using a forced third block, and complementary traces
replaced a classification of five-vertex multigraphs. These are recorded
contributions to the proof presented here, without a historical novelty
claim for the theorem or these arguments.

- R. G. Stanton, *Isomorphism Classes of Small Covering Designs with Block
  Size Five*, in C. J. Colbourn and R. Mathon (eds.), *Combinatorial Design
  Theory*, North-Holland, 1987, pp. 441-448.
  [DOI](https://doi.org/10.1016/S0304-0208(08)72910-4).
  The bibliography has been checked; the full chapter remains unread.
- D. M. Gordon, O. Patashnik, J. Petro and H. Taylor, *Minimum (12,6,3)
  Covers*, *Ars Combinatoria* 40 (1995), pp. 161-177.
  [Publisher record](https://combinatorialpress.com/ars-articles/volume-040-ars-articles/minimum-12-6-3-covers/),
  [retained author copy](../../data/sources/gppt-1995.pdf).
  In the author copy, Theorem 3.1 on page 4 attributes the classification
  to Stanton; Figure 2 and the two-completion explanation are on page 5.
  Our template matches Figure 2 under
  $a=3$, $s=6$, $t=9$, $F=\{1,2\}$, $G=\{4,5\}$,
  $C=\{7,8\}$ and $D=\{10,11\}$.
- R. C. Mullin, *On Covering Pairs by Quintuples: The Cases v congruent to
  3 or 11 modulo 20*, *Journal of Combinatorial Mathematics and
  Combinatorial Computing* 2 (1987), pp. 133-146.
  [Retained paper](../../data/sources/mullin-1987-quintuples.pdf).
  Its order-eleven construction on page 136 gives the same partial
  template under
  $a=1$, $s=2$, $t=3$, $F=\{4,9\}$, $G=\{5,10\}$,
  $C=\{6,11\}$ and $D=\{7,8\}$.
  This identifies the construction, without supplying a completeness proof.

The [focused provenance record](../../data/sources/stanton-11-5-2-provenance.json)
retains the citation checks, source hashes, and explicit permutations
matching the two GPPT completions to the Lean representatives.
No claim is made here about priority for the numerical value seven.

## Appendix A. Correspondence with Lean

The proof starts with an arbitrary finite point set and an arbitrary
seven-block covering. The template is a conclusion. The declaration
`template_classification` alone classifies completions of the template;
the preceding structural reductions are what establish completeness for
all coverings.

In the first table, unqualified declarations are in `CoveringDesigns`.
Names prefixed by `SS.` are in `CoveringDesigns.StantonStructural`.
Private helpers are cited by their source-level names and are not exported
interfaces. The links point to the modules containing the declarations.

| Passage | Lean declarations and role |
|---|---|
| §1, degree and block lower bounds | [SmallBounds](../../lean/CoveringDesigns/C11_5_2/SmallBounds.lean): `degree_at_least_three_11_5_2`, `lower_bound_11_5_2`; [Basic](../../lean/CoveringDesigns/Foundations/Basic.lean): `degree_sum_of_uniform`. |
| §2, indexed-triples inequality | [Intersecting](../../lean/CoveringDesigns/Foundations/Intersecting.lean): `indexedDegree_choose_sum`, `indexedSubsetDegree_sum`, `indexedSubsetDegree_choose_sum`, `intersecting_triples_bound`. Lean writes the final inequality without natural-number subtraction. Equal triples retain distinct indices. |
| §3, degree distribution and all-low block | [Degrees](../../lean/CoveringDesigns/C11_5_2/Structural/Degrees.lean): `structural_degree_excess_sum`, `structural_triples_inequality`, `structural_degree_bound`, `structural_degree_three_or_four`, `structural_degree_four_card`, `structural_degree_three_card`, `structural_all_low_block`. |
| §4, intersections between one and three | [Intersections](../../lean/CoveringDesigns/C11_5_2/Structural/Intersections.lean): `cross_pairs_capacity`, `structural_blocks_intersect`, `degree_three_star_union`, `degree_three_intersection_le_three`, `structural_intersection_le_three`. The upper-bound proof only needs the earlier fact that at most two points are not degree three. |
| §4, forced third block and intersection counts with $A$ | Same module: `degree_three_forced_third`, `structural_low_block_intersection_le_two`, `structural_low_block_intersection_sum`, `structural_low_block_intersection_counts`. |
| §4, complementary traces and complete frame | Same module: `structural_complementary_traces`, `structural_trace_complement`; [Frame](../../lean/CoveringDesigns/C11_5_2/Structural/Frame.lean): `SS.six_block_frame_of_low_block`, `SS.exists_six_block_frame`. The frame's seven rows equal the original family. |
| §5, one partition cannot cover the right-hand pairs | [PairCapacity](../../lean/CoveringDesigns/Foundations/PairCapacity.lean): `two_four_sets_not_cover_three_by_three`; Frame: `SS.no_single_trace_of_right_cover`. |
| §5, four distinct traces and complementary pairing | [TracePairs](../../lean/CoveringDesigns/C11_5_2/Structural/TracePairs.lean): `SS.FourTraceSystem.trace_injective`, `.exists_other_partition`, `.trace_two_alternatives`, `.disjoint_of_complement_pair`, `.complement_pairing`. |
| §5, doubled edges and common singleton | [DoubledEdges](../../lean/CoveringDesigns/C11_5_2/Structural/DoubledEdges.lean), namespace `SS.SixBlockFrame`: `right_union_of_trace_pairing`, `doubled_of_pairing`, `exists_doubled_frame`, with private helpers `unique_edge_data`, `differences_not_separated`, `edge_pair_equal`; [PartitionObstruction](../../lean/CoveringDesigns/Foundations/PartitionObstruction.lean): `cross_pair_cover_forces_one_part`, `two_disjoint_triples_not_cover_two_by_two`. |
| §6, four cells and residual pairs | [Grid](../../lean/CoveringDesigns/C11_5_2/Structural/Grid.lean): `SS.exists_grid_cells`; [Residual](../../lean/CoveringDesigns/C11_5_2/Structural/Residual.lean): `SS.residual_difference_pair`, `SS.residual_completion`, with private helper `residual_pair_same_side`. |
| §6, arbitrary covering has the displayed template | [NormalForm](../../lean/CoveringDesigns/C11_5_2/Structural/NormalForm.lean): `SS.DoubledFrame.nonempty_templatePartition`, `SS.SixBlockFrame.nonempty_templatePartition`; [Partition](../../lean/CoveringDesigns/C11_5_2/Structural/Partition.lean): `SS.TemplatePartition`, `SS.TemplatePartition.nonempty_template`; [Stanton](../../lean/CoveringDesigns/C11_5_2/Stanton.lean): `stanton_partition_on`, `stanton_template_on`. |
| §6, every completion is a seven-block covering | [Template](../../lean/CoveringDesigns/C11_5_2/Structural/Template.lean): private helper `core_with_triple_covers`; `SS.templateBlocks_uniform`, `SS.templateBlocks_card`, `SS.templateBlocks_covers`, `SS.templateBlocks_isCover`. Lean checks the fixed partial template by kernel evaluation and then proves the assertion for arbitrary allowed additions. |
| §7, two types exhaust completions | Same module: `SS.pair_completion_cases`, `SS.template_classification`, with private helpers `other_pair_isomorphic`, `transversal_isomorphic`; Stanton: `stanton_classification_on`. |
| §7, the types are different | [Classification](../../lean/CoveringDesigns/C11_5_2/Classification.lean): private predicate `hasTwoTripleNeighbors`, its relabelling lemma, and `stanton_representatives_not_isomorphic`. The intersection table explains exactly the predicate checked for the two explicit representatives. |
| Numerical value and complete classification | Same module: `covering_number_11_5_2`, `stanton_classification_unique_on`. The unique object is the representative tag, not the point permutation. |

The residual argument only needs the displayed five pairs to be absent
from the four traces; Lean proves that direction in `residual_not_in_grid_line`.
The stronger descriptive word “exactly” in §6 follows from the explicit
opposite-cell argument there. Likewise, the explanatory graph derivations
in §8 spell out the finite facts that Lean verifies on the two representatives
before transporting them to every minimum covering.

For §8, all names in the following table are in
`CoveringDesigns.StantonGeometry`.

| Passage | Lean declarations and role |
|---|---|
| §8.1, intrinsic definitions | [Geometry/Basic](../../lean/CoveringDesigns/C11_5_2/Geometry/Basic.lean): `multiplicity`, `IsCouple`, `coupleCount`, `IsShortBlock`, `IsShortPoint`. |
| §§8.1–8.2, degrees, spouses, full rows and multiplicities | [Geometry/Properties](../../lean/CoveringDesigns/C11_5_2/Geometry/Properties.lean): the twenty fields of `Facts`, `representative_facts`, `Facts.relabel`, `Facts.two_full_couple`; [Geometry](../../lean/CoveringDesigns/C11_5_2/Geometry.lean): `geometry_facts`, `degree_four_has_spouse` and the set-valued multiplicity wrappers. |
| §8.3, marking any intrinsic couple | Geometry/Basic: `markedRow`, `MarkingFrame`; [Geometry/Representatives](../../lean/CoveringDesigns/C11_5_2/Geometry/Representatives.lean): `representative_marking_frame`; Geometry: `exists_marking_frame`. The contract retains the actual completed short block, which may contain the marked couple. |
| §8.3, every unmarked row meets each triad | [Geometry/FrameLemmas](../../lean/CoveringDesigns/C11_5_2/Geometry/FrameLemmas.lean): `MarkingFrame.nonmarked_meets_triad`, with its short-row and full-row lemmas. |
| §8.4, Fano incidence structure and columns | [Geometry/Fano](../../lean/CoveringDesigns/C11_5_2/Geometry/Fano.lean): `FanoPlane`, `fanoLines_plane`, `fanoRepresentativeRow_columns`, `incidentRows_card`, `HasFanoColumns`, `exists_fano_columns`, `fano_column_of_degree_three`. |
| §8.4, five-line rigidity and its consequence | Same module: `triangle_of_two_triples`, `FanoPlane.eq_of_five_common`, `fano_eq_of_five_columns`, `column_meets_line_of_five_columns`. The last two require distinct column sets, not just distinct original points. |

### Coordinate correspondence

The abstract template in Lean uses
$a=0,s=1,t=2,F=\{3,4\},G=\{5,6\},C=\{7,8\},D=\{9,10\}$.
Thus subtracting one from the explicit labels of §7 gives exactly that
template. The representative permutations are:

| Point of §7 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Whole-pair → `true` | 8 | 9 | 10 | 2 | 6 | 3 | 7 | 0 | 4 | 1 | 5 |
| Transversal → `false` | 2 | 0 | 1 | 5 | 7 | 6 | 8 | 3 | 9 | 4 | 10 |

They are `wholePairToRepresentative` and `transversalToRepresentative` in
Template. The equalities of the mapped families are proved by
`whole_pair_to_representative` and `transversal_to_representative`.
The seven lines in §8.4 map to the literal `fanoLines` by sending rows
$(2,4,3,5,6,1,7)$ to $(0,1,2,3,4,5,6)$, respectively.

## Appendix B. Contracts, dependencies and verification

### What is formally proved

`Family α` is a finite set of finite subsets of `α`: block repetitions are
absent. `IsCover C 5 2` says every member has size five and every two-set of
points is contained in a member. The numerical theorem supplies a
seven-block witness and proves that every such covering has at least seven
blocks. The arbitrary-point-set classification assumes `Fintype.card α = 11`
and `C.card = 7` as well as these covering conditions, and concludes that
exactly one Boolean representative tag admits a bijective relabelling.
The [component audit](../../lean/audits/C11_5_2.lean) restates the numerical
and classification contracts using explicit cardinalities, inclusions and
bijections.

The import `CoveringDesigns.C11_5_2` exports the minimum, classification,
template and elementary degree/intersection bounds. The richer geometry
has separate imports `CoveringDesigns.C11_5_2.Geometry` and
`CoveringDesigns.C11_5_2.Geometry.Fano`. GPPT imports those extensions; they
depend on Stanton, never on a twelve- or thirteen-point theorem. The
standalone C11 audit covers the public entry point. The geometry extensions
are additionally compiled and checked in the GPPT and C13 dependency chains.

### Scope of the finite checks

Arbitrary coverings are reduced by counting and set arguments to the
template. There is no exhaustive covering-family enumeration or external
classification certificate in this proof. Ordinary kernel evaluation is
used for the displayed finite templates, permutations, representative
intersection property, and local geometry. These evaluations produce
kernel-checked proof terms; they are not native assertions. Relabelling
lemmas then establish the corresponding statements for arbitrary labels.

The transitive `#guard_standard_axioms` permits only `propext`,
`Classical.choice` and `Quot.sound`; it does not require every lemma to use
all three. The recorded audit separately checks the expected exact axiom
sets of the numerical theorems, their structural dependencies, and independence
from the larger covering components. The historical papers supply
attribution, not unproved premises in Lean.

From the repository root, use `./covering verify 11-5-2` for the
standalone component and `./covering verify 12-6-3` for GPPT together with
the geometry it consumes. `./covering audit` validates recorded verification
against the current source and build fingerprints. See the
[verification guide](../../technical-details.md) for setup and reproduction.
These checks verify the Lean statements and proofs. The correspondence
tables are a separately reviewed explanation of them; Lean does not check
the Markdown prose.
