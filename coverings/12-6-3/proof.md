# C(12,6,3) = 15 and the structure of minimum coverings

**Rob Gardiner**

A $(12,6,3)$ covering is a family of distinct six-element subsets, called
blocks, of a twelve-point set, containing every triple in at least one
block. Its minimum size is denoted by $C(12,6,3)$. Isomorphism means exact
equality of block families after a bijection of the point sets.

**Theorems.** $C(12,6,3)=15$. Every fifteen-block covering is isomorphic
either to a completion of GPPT Figure 1 or to the covering in Figure 6,
and these alternatives are disjoint. Every minimum covering is also
isomorphic to an entry of the explicit 68-entry catalogue.

**Proof provenance: an adaptation of known results.** The exact minimum
and structural alternatives are due to Gordon, Patashnik, Petro and Taylor
(GPPT). This is a self-contained Lean proof of these conclusions, not a
literal translation of their paper. Its prerequisite is the separately
proved [reconstruction of Stanton's classification](../11-5-2/proof.md).

Minimum-pair compatibility in Section 3 follows GPPT Lemma 5.2, proved here
in the at-most-fifteen-block setting. Using it to prove the numerical lower
bound in Section 4 replaces the paper's Section 4 argument. The
repeated-triple branch in Section 5 follows GPPT Lemma 5.8 with shorter
excess bookkeeping. Sections 6–9 replace the argument of Lemmas 5.6–5.7
with projection, Fano-plane identification and the seven-cap lemma. These
choices give self-contained structural prerequisites reusable in Lean.
The [source comparison](#sources-and-contribution) records the relationship
to the original arguments; no historical novelty is claimed for these
supporting arguments.

Catalogue completeness is a separate finite calculation checked by the
Lean kernel. The formal result does not assert that all 68 entries are
pairwise nonisomorphic, or prove the paper's element-minimality assertions.

**Dependencies and route.** Sections 1–4 prove the numerical minimum using
Stanton's theorem and compatibility of minimum point links. For the
structural classification, a repeated triple gives the frame argument in
Section 5; the absence of a repeated triple gives the projective argument
in Sections 6–9. Section 10 separates the two outcomes. These sections
supply the structural prerequisite for the
[thirteen-point proof](../13-7-4/proof.md). Section 11 then verifies the
remaining completions to establish catalogue completeness; none of the
preceding structural arguments uses that check.

A completion of Figure 1 means adding two points to each of its three
four-point rows while retaining its twelve six-point rows. Section 2
constructs this template without relying on the paper's figure; Section 5.2
describes Figure 6 explicitly. Appendix A maps the proof to Lean declarations
and explains the coordinate checks. Appendix B gives the exact theorem
contracts, dependency boundaries and verification scope. The
[source comparison](#sources-and-contribution) identifies which historical
arguments are followed and which are replaced.

## 1. Degrees, links and the eleven-point geometry

Let $\mathcal C$ be a covering on a twelve-point set $X$.
Write $d(x)$ for the number of blocks through $x$, and $d(x,y)$ for the
number through both distinct points $x,y$. Deleting $x$ from its incident
blocks gives its **link**, an $(11,5,2)$ covering. The deletion preserves
the number of distinct blocks.

The eleven-point lower bound gives $d(x)\ge7$. Incidence counting yields

$$
6|\mathcal C|=\sum_{x\in X}d(x)\ge84,
$$

so $|\mathcal C|\ge14$. For a covering with at most fifteen blocks,

$$
\sum_{x\in X}(d(x)-7)\le6.
$$

At least six points consequently have degree seven. We call these
**minimum points**. A link at such a point has exactly seven blocks and
therefore has the Stanton template.

We use the following consequences of that template. In an eleven-point
minimum link, a **couple** is a point pair of multiplicity at least three.
There are four disjoint couples. The **short block** is the distinguished
block obtained by completing the template's three-point block; the other
six blocks are full. Its three degree-three points are the **short points**,
and its two added points are the degree-four points.

The template gives these local rules:

1. Every point has degree three or four. A pair of multiplicity two has
   at least one degree-four endpoint and lies in the short block.
2. Every couple occurs in exactly three full blocks. No pair occurs in
   exactly two full blocks.
3. Choose a marking couple. The three full blocks containing it partition
   the other nine points into three triads. Each nonmarked block meets
   every triad.
4. The three other full blocks select one short point from one triad and
   the two nonselected points from each of the other triads. The short
   block contains the three selections and its two additions.

These statements are proved in the
[Stanton geometry section](../11-5-2/proof.md#8-the-intrinsic-geometry-used-by-gppt),
which also gives intrinsic definitions independent of any labelling.
For later calculations, if the marking couple is $K$, write
$T_i=\{s_i\}\sqcup K_i$, where $K_0,K_1,K_2$ are the other couples.
The six full rows are exactly

$$
K\cup\{s_i\}\cup K_i,\qquad
\{s_i\}\cup K_j\cup K_k,
\quad \{i,j,k\}=\{0,1,2\}.
$$

The short row contains $s_0,s_1,s_2$ and two additions. It may meet the
marked couple, or contain both its members. “Nonmarked” here means a row
not containing the whole marked couple; the three full rows containing it
are the ones that define the triads.

## 2. A fifteen-block upper bound

It is useful to describe the partial covering in GPPT Figure 1 by projective
incidence. Let $V=\mathbb F_2^4$, and choose a two-dimensional subspace $L$
of the dual vector space. Take the twelve covering points to be the nonzero
linear functionals outside $L$. For each nonzero row vector $v\in V$, form

$$
B_v=\{n\in V^*\setminus L:n(v)=0\}.
$$

There are fifteen rows. If $v$ annihilates $L$, the row has four points;
otherwise it has six. Thus there are three four-point rows and twelve
six-point rows. The four-point rows are disjoint and partition the twelve
points.

This partial family covers every triple of point columns: three linear
equations in a four-dimensional space have a nonzero common solution.
Complete each four-point row by adding any two of the eight points outside
it. This preserves triple coverage and makes all rows six-point blocks.

The completed rows remain distinct. A full row meets each four-point row
in two points, so it cannot equal a completion containing all four.
Two completed short rows cannot coincide, since their union would have
to contain two disjoint four-point rows. The full rows are distinct:
two different seven-point hyperplanes in the dual space differ on eight
nonzero points, and deleting the three nonzero members of $L$ cannot
erase that difference.

This gives fifteen distinct blocks and proves $C(12,6,3)\le15$.

Here is an explicit labelling, so that “Figure 1” requires no external
diagram. Choose $L$ to be the span of the first two coordinate functionals.
For $i=0,1,2$, put $(c_i,d_i)=(1,0),(0,1),(1,1)$, respectively, and label
the normal

$$
n_{4i+2u+v}=(u,v,c_i,d_i),\qquad u,v\in\mathbb F_2,
$$

by the integer $4i+2u+v$. Thus a row $(a,b,c,d)\ne0$ contains that point
exactly when $au+bv=cc_i+dd_i$. The three four-point rows are the fibres

$$
P_0=\{0,1,2,3\},\quad P_1=\{4,5,6,7\},\quad
P_2=\{8,9,10,11\}.
$$

Equivalently, write points as $(i,x)$ with $x=(u,v)\in\mathbb F_2^2$.
The twelve full rows are

$$
B_{\ell,\varepsilon}
=\bigcup_{i=0}^2\{(i,x):\ell(x)=\varepsilon_i\},
\qquad \ell\ne0,\qquad
\varepsilon_0+\varepsilon_1+\varepsilon_2=0.
$$

There are three nonzero linear forms $\ell$ and four allowed vectors
$\varepsilon$. Each row meets every fibre in two points. Together with
$P_0,P_1,P_2$ these are exactly the retained
[Figure 1](../../data/gppt-figure1.json), as the fixed Lean incidence
identity verifies. Figure 6, described and checked in Section 5.2, supplies
the explicit witness used in the numerical Lean theorem.

## 3. Minimum-point pairs occur exactly three times

**Lemma.** In any $(12,6,3)$ covering with at most fifteen blocks, distinct
degree-seven points $p,q$ satisfy $d(p,q)=3$.

This is the local compatibility statement corresponding to GPPT Lemma 5.2.
The project proves it under the stated at-most-fifteen hypothesis, before
using it to rule out fourteen blocks.

**Proof.** The ten other points must occur with $p,q$ to cover their ten
triples. Each incident block supplies only four of them, so $d(p,q)\ge3$.
The Stanton link at $p$ bounds this degree by four. Suppose it is four.

In that link, $q$ belongs to a marking couple $\{q,w\}$. The three full
blocks through the couple have the form

$$
\{p,q,w\}\cup T_i,\qquad i=0,1,2,
$$

where the $T_i$ partition the other nine points into triads.
In the link at $q$, $\{p,w\}$ is also a couple, since it occurs in at
least these three blocks.

The two marking frames have the same three marked blocks. Each has three
of the four blocks through $p,q$, so at least two marked blocks coincide.
Their outside triads partition the same nine points, forcing the third
marked block to coincide too. The fourth common block $W$ is therefore
the short block in both links.

Write $s_i$ and $t_i$ for the selections in the $p$- and $q$-frames.
The block $W$ contains $p,q$ and both selection sets. It has room for at
most four outside points, so the selections agree in at least two triads.

For an agreeing triad, its two nonselected points occur together in the
marked block, two $p$-full blocks, and two $q$-full blocks.
These five blocks are distinct: the two complementary $p$-rows avoid $q$,
the two complementary $q$-rows avoid $p$, and the marked block contains
both. The pair therefore has degree at least five, so neither endpoint
can be minimum: a minimum endpoint's Stanton link has maximum point degree
four. The selected point is also nonminimum. It occurs with $p,q$ exactly
in its marked block and $W$. Its pairs with $p$ and $q$ each have degree
three because it is a short point in both local templates; this uses no
instance of the pair lemma being proved. If it were minimum, its link would have a multiplicity-two
pair with both endpoints of degree three, contrary to the local rule.

Each agreeing triad thus gives three nonminimum points. Agreement in all
three triads would exceed the six available excess incidences.
There are exactly two agreeing triads; their six nonminimum points force
every other point to be minimum.

Reindex these two triads as $T_0,T_1$, and write
$s_i=t_i$ there. In the remaining triad, write

$$
T_2=\{x,y,z\},\qquad s_2=x,\quad t_2=y,\quad x\ne y.
$$

The shared short block is exactly
$W=\{p,q,s_0,s_1,x,y\}$, so it omits $z$.
The three blocks through $p,z$ are the marked block for $T_2$ and
the $p$-full blocks for $T_0,T_1$.

In the minimum link at $z$, the pair $\{p,y\}$ is a couple because
all three just-listed blocks contain it. Those are exactly the three
blocks through $p,z$: the description in the $p$-link and $z\notin W$
give $d(p,z)=3$. Since a couple already occurs in three full rows, these
known occurrences must all be full rows of the $z$-link. Its marked
triads are therefore exactly

$$
\{q,w,x\},\qquad
\{s_0\}\cup(T_1\setminus\{s_1\}),\qquad
\{s_1\}\cup(T_0\setminus\{s_0\}).
$$

But the $q$-full block for $T_1$, after deleting $z$, is

$$
\{q,x,s_1\}\cup(T_0\setminus\{s_0\}).
$$

It is nonmarked and misses the second displayed triad entirely.
That contradicts the Stanton rule that every nonmarked block meets
each marked triad. Pair degree four is impossible, proving the lemma.
$\square$

## 4. The exact minimum and the branch point

If there were fourteen blocks, the 84 incidences and degree lower bound
seven would force every point to have degree seven. The pair lemma would
then make every one of the eleven points in any link have degree three.
Its incidence sum would be $11\cdot3=33$, whereas seven five-point
blocks have $7\cdot5=35$ incidences. This is impossible.

Together with Section 2, this proves $C(12,6,3)=15$.
Fix a fifteen-block covering for the classification. Its total excess is
now exactly six.

A triple of minimum points cannot have multiplicity two: in the link at
one of them, it would be a pair of multiplicity two whose endpoints both
have degree three. Its multiplicity is at most three by the pair lemma.
Consequently a repeated triple of minimum points occurs exactly three times.

We split according to whether such a repeated triple exists.
This is a split on an intrinsic property of an arbitrary covering,
before any catalogue enumeration.

We also need **shortness symmetry** between minimum points. First observe
two facts about the Stanton rows in Section 1. For each $i$, the full rows
$K\cup\{s_i\}\cup K_i$ and $\{s_i\}\cup K_j\cup K_k$ intersect
exactly in $\{s_i\}$. Every other full/full intersection is a couple.
The short row contains the unique short point of every full row. Consequently every
short point occurs as a singleton intersection of two full rows, and
every singleton intersection of two distinct rows consists of a short
point.

Suppose $q$ is short in $p$'s link, with both points minimum. Lift two
full rows intersecting exactly in $\{q\}$ to their original blocks.
Those blocks intersect exactly in $\{p,q\}$. Deleting $q$ gives distinct
rows in its link intersecting exactly in $\{p\}$, so $p$ is short there.
This proves the symmetry. It only needs the two minimum links, not a bound
on the number of blocks in the whole covering.

Finally, if a minimum point $q$ belongs to the short row of a minimum
point $p$, the pair lemma gives $d(p,q)=3$. It cannot be a degree-four
addition, so it is a short point there. These are the local compatibility
facts used in the next branch.

## 5. A repeated triple: the three-root frame

Let $a_0,a_1,a_2$ be minimum points whose triple has multiplicity three.
Their stars each have seven blocks, their pairwise overlaps have three,
and their triple overlap has three. Inclusion-exclusion gives

$$
7+7+7-3-3-3+3=15,
$$

so their stars contain the entire covering.

In each root's link, mark the couple consisting of the other two roots.
Its three full occurrences exhaust the pairwise star overlap, which has
size three. Thus the private full rows and the short row contain no other
root. The three common blocks partition the other nine points into triads
$T_0,T_1,T_2$; the same common blocks align these triads in all three links.
For root $a_r$, let $s_{rj}\in T_j$ be the selected short point. The rows
have the following form:

- Three common blocks $\{a_0,a_1,a_2\}\cup T_j$.
- For each $r,j$, a full block
  $\{a_r,s_{rj}\}\cup\bigcup_{k\ne j}(T_k\setminus\{s_{rk}\})$.
- For each $r$, a short block $\{a_r\}\cup W_r$, where $W_r$ has five
  outside points and contains $s_{r0},s_{r1},s_{r2}$.

Every block belongs to one of the stars, and each star is exactly its
seven Stanton rows. The displayed fifteen positions therefore account for
the whole fifteen-block covering, so no two positions can coincide. This
is a description of the given arbitrary covering, not a restricted model
assumed at the outset.

For an outside point $x$, let $m(x)$ count roots selecting it, and let
$e(x)$ count nonselected occurrences in the short traces $W_r$.
Its degree is

$$
d(x)=1+(6-m(x))+(m(x)+e(x))=7+e(x).
$$

Each short trace has two additions, so $\sum_x e(x)=6$.

### 5.1. Each selection column is injective

Suppose the three selections in each $T_j$ are distinct.
Permute within each triad so that root $r$ selects its $r$th point.
Label the roots $0,1,2$ and the triads $\{3,4,5\},\{6,7,8\},
\{9,10,11\}$. The selection array is then

$$
\begin{pmatrix}3&6&9\\4&7&10\\5&8&11\end{pmatrix}.
$$

The frame formula specifies twelve full rows and the three short cores
$\{0,3,6,9\},\{1,4,7,10\},\{2,5,8,11\}$. This is the partial family
called Figure 4. The point permutation with image array

$$
\begin{array}{c|rrrrrrrrrrrr}
x&0&1&2&3&4&5&6&7&8&9&10&11\\\hline
\pi(x)&0&3&6&9&1&4&7&10&2&5&8&11
\end{array}
$$

maps the three fibres and twelve rows defined in Section 2 to these short
cores and full rows, respectively. This follows by substituting the
twelve point labels into the row formulas; Lean checks both family
equalities exactly. The permutation is the paper's
$(2\,6\,7\,10\,8)(1\,3\,9\,5\,4)$.

Applying its inverse to the actual covering gives a Figure 1 completion.
The actual short rows supply the added pairs; no classification of their
choices is needed for this structural conclusion.

### 5.2. A point is selected by all three roots

Suppose all roots select the same point $x\in T_0$.
Put $Y=T_0\setminus\{x\}$ and $Z=T_1\cup T_2$.
None of the twelve triples $\{x,y,z\}$, with $y\in Y$, $z\in Z$, occurs
in a common or full block. They must be covered by the three short traces.

A five-point short trace containing $x$ covers at most four pairs
between $Y$ and $Z$: if it contains $u$ points of $Y$ and $v$ of $Z$,
then $u\le2$, $u+v\le4$, and $uv\le4$.
If $u\le1$, its capacity is at most three.
Covering twelve pairs forces capacity four in each trace.
Both points of $Y$ occur in every $W_r$, using all six additions.

Every point in $T_1,T_2$ is consequently minimum. A repeated selection
in either triad would make its two mates have pair degree at least five,
contrary to their minimum links. Those columns are injective.
Relabelling gives exactly GPPT Figure 6.

For an explicit description on $\{0,\ldots,11\}$, take roots $0,1,2$,
triads $\{3,4,5\}$, $\{6,7,8\}$, $\{9,10,11\}$, and selections

$$
(s_{rj})=
\begin{pmatrix}
3&6&9\\
3&7&10\\
3&8&11
\end{pmatrix},
\qquad
W_r=\{3,4,5,s_{r1},s_{r2}\}.
$$

Together with the frame formula, this specifies all fifteen blocks in
the [retained Figure 6](../../data/gppt-figure6.json).
Its ten minimum points have degree seven; points 4 and 5 have degree ten.

For completeness, the following direct coverage argument verifies the
displayed witness without a list of 220 triples. Write
$T_0=\{x,u,v\}$, $T_1=\{b_0,b_1,b_2\}$ and
$T_2=\{c_0,c_1,c_2\}$. In addition to the three common rows, the four
rows private to $a_r$ are

$$
\begin{aligned}
F_r&=\{a_r,x\}\cup(T_1\setminus\{b_r\})\cup(T_2\setminus\{c_r\}),\\
G_r&=\{a_r,b_r,u,v\}\cup(T_2\setminus\{c_r\}),\\
H_r&=\{a_r,c_r,u,v\}\cup(T_1\setminus\{b_r\}),\\
S_r&=\{a_r,x,u,v,b_r,c_r\}.
\end{aligned}
$$

Every triple containing a root is covered by its Stanton link. An outside
triple in a single triad lies in a common row. For triples with two points
in one triad, the following rows suffice:

| Two points | Third point | Covering row |
|---|---|---|
| $x$ and one of $u,v$ | $b_r$ or $c_r$ | $S_r$ |
| $u,v$ | $b_r$; $c_r$ | $G_r$; $H_r$ |
| $T_1\setminus\{b_r\}$ | $x$; $u$ or $v$ | $F_r$; $H_r$ |
| $T_1\setminus\{b_r\}$ | $c_j$, $j\ne r$; $c_r$ | $F_r$; $H_r$ |

Interchanging $T_1,T_2$ and $G,H$ supplies the symmetric cases. Finally,
for one point from each triad, $b_i,c_i$ occur with every point of $T_0$
in $S_i$. For $i\ne j$, the triple $x,b_i,c_j$ lies in $F_k$ for the
third index $k$, while $u,b_i,c_j$ and $v,b_i,c_j$ lie in $G_i$.
These cases exhaust all triples. The rows are distinct by their root
content and their different traces on the triads. Lean verifies the same
explicit family by fixed kernel reduction in its witness theorem.

### 5.3. A point is selected exactly twice

Assume no column is constant, excluding the preceding case. A noninjective
column of three entries then has exactly the pattern $x,x,y$ after
reindexing the roots, with third point $z$ in its triad.

The point $x$ is nonminimum. If it were minimum, shortness symmetry would
make the first two roots short in its link. Their unique common block
containing $x$ would be that link's short block. It also contains the
third minimum root, so symmetry would make $x$ short for that root too,
contrary to its selection $y$.
The two mates $y,z$ are nonminimum because their pair already has degree
at least five. Thus the repeated triad consumes at least three additions.

There cannot be two repeated columns. They would consume all six additions,
making every point of the remaining triad minimum. That triad's selections
would be distinct, and each $W_r$ would meet it only at its selected point.
For the first repeated column, every triple formed from $x,y$ and a point
of the remaining triad is absent from the common and full blocks.
Covering the three such triples forces $x,y$ into every $W_r$.
But $y$ is selected only once, so it requires two additions. Together
with one each for $x,z$, this triad would need at least four additions,
exceeding the total budget with the second repeated triad.
The other two columns are therefore injective.

At least six points are minimum. Three are roots and none belongs to the
repeated triad. Among the other two triads, one has at least two minimum
points. Its injective selections include a minimum point selected by
one of the first two roots.

Relabel so that this point is 6, short for root 0, and the selections are

$$
(s_{rj})=
\begin{pmatrix}
3&6&9\\
3&7&10\\
4&8&11
\end{pmatrix}.
$$

Point 6 has no nonselected short-trace additions. It belongs to $W_0$
as a selection and to neither $W_1$ nor $W_2$. Its remaining incident
blocks are therefore fixed by the displayed frame. In its link, the
pair $\{3,9\}$ occurs exactly twice:
in root 0's short block and root 1's full block for the first triad.
A multiplicity-two pair lies in the short block. By shortness symmetry,
root 0 is short in the 6-link; only the first of those two blocks contains
root 0. Thus it is the 6-link's short block.

Outside that short block, the pair $\{4,5\}$ occurs in exactly two full
blocks of the 6-link: root 0's full block for the second triad and root 1's
full block for the third. This contradicts the Stanton rule that a pair
cannot occur in exactly two full blocks.

The twice-selected case is impossible. This completes the repeated-triple
branch, with the two alternatives in Sections 5.1 and 5.2.

## 6. No repeated triple: exactly six minimum points

Assume now that every triple of minimum points occurs only once.
We first show there are at most six minimum points.

Suppose $S$ consists of seven minimum points. For each block $B$, put
$r_B=|B\cap S|$. Since a six-point block meets any seven points of a
twelve-point set, $1\le r_B\le6$. The polynomial
$(r-1)(r-3)(r-4)$ is nonnegative at these six integer values.
Equivalently,

$$
10\binom r2+12\le6\binom r3+12r.
$$

The incidence moments give

$$
\sum_B r_B=49,\qquad
\sum_B\binom{r_B}{2}\ge3\binom72=63,\qquad
\sum_B\binom{r_B}{3}=\binom73=35.
$$

The pair lower bound is three; triple coverage and the no-repetition
hypothesis give the last equality. Summing the polynomial inequality
would force

$$
810=10\cdot63+12\cdot15
\le6\cdot35+12\cdot49=798,
$$

a contradiction.

There are therefore exactly six minimum points, since Section 1 gives
at least six. Denote their set by $P$, and put $H=X\setminus P$.
Each of the six points of $H$ has degree at least eight; the total excess
six forces each to have degree exactly eight.

## 7. The six-point projection

A block contains at most four points of $P$. To see this, fix a minimum
point $p$ in a block containing $r$ minimum points. Each other minimum
point in that block occurs twice more with $p$, by pair degree three.
Each of the other six blocks through $p$ contains at most one of those
$r-1$ points, or a minimum-point triple would repeat. Thus
$2(r-1)\le6$.

Let $n_j$ count blocks meeting $P$ in $j$ points. Counting blocks,
point incidences, pair incidences and triple incidences gives

$$
\begin{aligned}
\sum_{j=0}^4 n_j&=15, &
\sum_{j=0}^4 jn_j&=42,\\
\sum_{j=0}^4\binom j2 n_j&=45, &
\sum_{j=0}^4\binom j3 n_j&=20.
\end{aligned}
$$

These equations give
$n_3=20-4n_4$, $n_2=6n_4-15$, $n_1=12-4n_4$, and $n_0=n_4-2$.
Nonnegativity of $n_2,n_1$ forces $n_4=3$. Hence

$$
(n_0,n_1,n_2,n_3,n_4)=(1,0,3,8,3).
$$

The three four-point traces meet pairwise in exactly two points:
their intersection has size at least two on a six-point set, and
three common minimum points would repeat a triple.
Their complementary pairs therefore partition $P$; call them $E_1,E_2,E_3$.

Every three-point trace is a transversal of these pairs.
If it contained both points of one $E_i$, its third point and that pair
would already lie together in a four-point trace.
There are exactly eight transversals and eight triple traces; repetition
is forbidden, so all occur once.

A pair joining different $E_i$ already occurs in one four-point trace
and two transversals, using its three incidences. A pair $E_i$ occurs
in two four-point traces and no transversal, requiring one further row.
The three two-point traces are consequently $E_1,E_2,E_3$.
Together with the empty trace, every projected trace occurs exactly once.

Label the minimum points by $(i,b)$, where $i=1,2,3$ and $b\in\mathbb F_2$.
Give each actual row the following nonzero vector
$v=(t,x_1,x_2,x_3)$ of $\mathbb F_2^4$:

| Trace on $P$ | Row vector |
|---|---|
| $\{(1,b_1),(2,b_2),(3,b_3)\}$ | $(1,b_1,b_2,b_3)$ |
| $E_i$ | $t=0$, $x_i=0$, $x_j=1$ for $j\ne i$ |
| $P\setminus E_i$ | $t=0$, $x_i=1$, $x_j=0$ for $j\ne i$ |
| $\varnothing$ | $(0,1,1,1)$ |

The fifteen traces occur exactly once, and these are the fifteen nonzero
vectors. Thus the table gives a bijection of actual blocks with row
vectors, under which the minimum-point incidence columns are

$$
K_{i,b}=\{v\ne0:x_i+bt=0\}.
$$

Rows with $t=1$ are the eight transversals. Rows with $t=0$ give the
three pair traces, three four-point traces, and empty trace.
The empty trace is

$$
r_\infty=(0,1,1,1),
$$

whose actual block consists of all six points of $H$.

## 8. Stanton's local Fano planes identify the coordinate geometry

The seven rows in a minimum-point column form a Stanton link. The
[row-plane construction](../11-5-2/proof.md#84-the-fano-plane-on-the-seven-rows)
gives a Fano plane on them. Before adding the short row to the two
degree-four columns, the four couples give four duplicated line columns,
and the three short points give the other three lines. A degree-four
column contains its underlying line and the extra short row.
Thus every point column contains a line and meets every line of the local
Fano plane.

Fix one minimum column $K_p$. The five other minimum columns restrict
to five distinct lines there: their sizes are three by the pair lemma,
and their pair intersections have size one by the no-repeated-triple
hypothesis and coverage.
In the displayed coordinates these are the five lines $K_p\cap K_q$.

The ordinary projective lines in the three-dimensional vector space
$K_p\cup\{0\}$ also form a Fano plane: two distinct nonzero vectors
determine the triple $\{u,v,u+v\}$, and two two-dimensional subspaces
of a three-dimensional space intersect nontrivially. These two planes
share the five distinct lines just identified, so the five-line rigidity
lemma from the Stanton proof makes them equal. Recall its short argument:
if a line of the second plane were new, its three pairs would have to lie
in at most two missing lines of the first plane; two pairs in one triple
force that triple to be the supposed new line. Hence the local Stanton
plane is exactly this coordinate projective plane.

Fix a high point $h\in H$, and let $S_h$ be its seven absent rows.
In each minimum hyperplane $K_p$, the set $S_h\cap K_p$ contains
no projective line: every point column meets every local Fano line.
Also $r_\infty\notin S_h$, since its block contains all high points.

We now pass from these six local restrictions to a global restriction.
The only projective lines not contained in any $K_{i,b}$ are lines
through $r_\infty$ and the line

$$
L_0=\{(0,x_1,x_2,x_3)\ne0:x_1+x_2+x_3=0\},
$$

consisting of the three pair rows.
For a line generated by independent vectors $u,v$, avoiding all six
minimum hyperplanes says that each coordinate pair $(u_i,v_i)$
differs from $(0,0)$ and $(u_0,v_0)$.
If $(u_0,v_0)\ne(0,0)$, choose the nonzero coefficient pair
$(\alpha,\beta)$ orthogonal to it. Its dot product with each of the
two remaining allowed coordinate pairs is one. The vector
$\alpha u+\beta v$ is therefore $r_\infty$.

If $(u_0,v_0)=(0,0)$, the other three coordinate pairs are nonzero.
If they used at most two of the three possible values, a coefficient
pair could take value one on all of them, again producing $r_\infty$.
Otherwise the three values are $(1,0),(0,1),(1,1)$ in some order.
Their sum is zero, so the whole line lies in $t=0$ and
$x_1+x_2+x_3=0$: it is $L_0$.

Thus the only line that could lie in $S_h$ is $L_0$.
If $L_0\subseteq S_h$, each of the other three cosets of its
two-dimensional vector span contains at most one member of $S_h$:
two such members sum to a nonzero member of $L_0$, producing a
different line in $S_h$. This would give $|S_h|\le3+3=6$.

Consequently $S_h$ is a **seven-cap**: it contains no three distinct
vectors summing to zero.

## 9. Seven-caps give the Figure 1 core

Every seven-point subset of $\mathbb F_2^4\setminus\{0\}$ containing
no projective line lies in an affine hyperplane of size eight that avoids
zero. The exclusion of zero is part of this statement and is satisfied
by $S_h$. Here is a structural proof.

Choose distinct $a,b,c$ in the cap. They are independent: a dependence
involving one or two contradicts nonzeroness or distinctness, and a
dependence involving all three contradicts the cap condition. Their span
meets the cap only in $\{a,b,c,a+b+c\}$, since zero and the three pair
sums are excluded. There is therefore a cap member $d$ outside this span.
The four chosen members form a basis.
The six weight-two vectors are excluded because each is the sum of
two basis members. If the weight-four vector were present, it would
exclude every weight-three vector, leaving at most five cap members.
It is therefore absent, and all seven members have odd weight in this
basis. The linear functional summing the four coordinates takes value one
on the cap, giving the required affine hyperplane avoiding zero.

Apply this to $S_h$. Its complement among the fifteen nonzero rows
is a seven-point projective hyperplane with one extra row.
That complement is the incidence column of $h$.
Each minimum column is already a projective hyperplane.
Delete the one extra incidence from each of the six high columns.

The resulting core has twelve indexed nonzero normals and row sizes
at most six. Its normals are distinct. If one normal had multiplicity
$m$, summing core incidences over its seven-point hyperplane gives

$$
7m+3(12-m)=36+4m\le7\cdot6=42.
$$

Equal hyperplanes meet in seven points and distinct ones in three;
the inequality forces $m\le1$.

Exactly three nonzero normals are omitted. They meet every row
hyperplane, since a row avoiding all three would retain seven core
points. Three distinct nonzero normals meeting every hyperplane form
a projective line. Otherwise they would be independent, and a linear
functional taking value one on all three would define a hyperplane
avoiding them.

Choose two independent vectors of the omitted line, extend them to a
basis, and send that basis to the coordinate basis. The omitted line is
now the span of the first two coordinate normals, with zero removed.
Changing coordinates on normals induces the dual change of coordinates
on rows and preserves incidence. Label the twelve remaining normals by
the explicit formula in Section 2. The core is exactly its Figure 1
family: three rows have four points and twelve have six.

Each full core row is contained in an original six-point block, so that
block must equal it. Each four-point core row also extends to an original
block. Those three extensions are distinct from the twelve full rows,
since a full row meets a four-point fibre in only two points; they are
distinct from each other, since a six-set cannot contain two disjoint
four-sets. These fifteen blocks exhaust the original family. It is
therefore a Figure 1 completion, with two additions in each short row.
This last counting step ensures equality of whole families, not just the
presence of a partial template.

This completes the alternative projective proof for the no-repeated-triple
branch. Its arbitrary-cover projection, Fano identification, cap
construction and change of basis are proved separately from the
fixed coordinate checks.

## 10. The alternatives are disjoint

Every point in the Figure 1 partial template has degree seven and lies
in exactly one of its three four-point rows. Completing the other two
rows can raise its degree by at most two. Hence every point in any
Figure 1 completion has degree at most nine.

Figure 6 has points 4 and 5 of degree ten, as the explicit frame in
Section 5.2 shows. Degree is invariant under isomorphism, so Figure 6
cannot be isomorphic to a Figure 1 completion.

Sections 5 and 6–9, followed by this separation, establish the structural
alternatives of GPPT Theorem 5.9. No catalogue completeness theorem
has been used in obtaining them.

## 11. Kernel-checked catalogue completeness

The structural theorem leaves the three Figure 1 four-point rows to be
completed. Each has $\binom82=28$ possible added pairs, giving
$28^3=21,952$ labelled completions before symmetry.

For the first row, its outside points are the two other four-point fibres.
We explain the symmetry reduction explicitly. Use the $(i,x)$ coordinates
and full-row formula of Section 2. For a common invertible linear map
$g$ of $\mathbb F_2^2$, translations satisfying $t_0+t_1+t_2=0$, and a
permutation $\sigma$ of the three fibres, the point map

$$
(i,x)\longmapsto(\sigma(i),gx+t_i)
$$

preserves the partial template. Indeed, it permutes the fibres, and
transports a full row to another nonzero linear form with new constants
whose sum is still zero. Take $\sigma(0)=0$.

For an outside pair within one fibre, first swap fibres 1 and 2 if needed.
Choose $g$ sending the pair's nonzero difference to $(0,1)$, and translate
its first point to $(0,0)$ in fibre 1. Choose the translations of fibres
0 and 2 so that their sum equals the translation of fibre 1. The resulting
pair has labels $\{4,5\}$.
For a cross-fibre pair $(1,x),(2,y)$, take $g$ to be the identity and
$t_1=x,t_2=y,t_0=x+y$. Its image is $\{4,8\}$.

These maps fix the first fibre setwise and transport both other added
pairs to valid choices in the appropriately permuted fibres. Lean checks
one such normalizer for each of the 28 first-row choices. Thus only

$$
2\cdot28^2=1,568
$$

normalized labelled inputs remain. This is not a count of isomorphism
classes.

The retained data supply 28 normalizers, 256 shared automorphisms,
and an explicit isomorphism witness for each normalized completion.
Lean checks:

- Each listed automorphism is a bijection preserving the full-block core
  and permuting the three four-point fibres.
- Every possible added pair occurs in the 28-choice list for its row.
- Every first added pair has a template-preserving normalizer fixing the
  first fibre and sending that pair to $\{4,5\}$ or $\{4,8\}$.
- All 1,568 normalized inputs occur in the witness table.
- Each witness maps the whole completed family exactly to one of the
  first 67 catalogue entries.

The 256 automorphisms are sufficient witnesses; completeness of the
entire automorphism group is not an assumption.
The [witness generator](../../scripts/generate_gppt_completions.py)
proposes data, and every mathematical property used is checked by
ordinary kernel proofs. The exceptional Figure 6 is the last catalogue
entry, index 67 in Lean's zero-based numbering.

Combining the structural reduction with these witnesses proves
that every minimum covering is isomorphic to an entry of the
[68-entry catalogue](../../data/links-68.json).
This is a completeness assertion. Pairwise nonisomorphism of those
entries is a separate statement, reported by GPPT's computer calculations
and not asserted by this component's Lean theorem.

## Sources and contribution

- D. M. Gordon, O. Patashnik, J. Petro and H. Taylor,
  *Minimum (12,6,3) Covers*, *Ars Combinatoria* 40 (1995), pp. 161-177.
  [Publisher record](https://combinatorialpress.com/ars-articles/volume-040-ars-articles/minimum-12-6-3-covers/),
  [retained author copy](../../data/sources/gppt-1995.pdf).
  Theorem 4.4 establishes the numerical minimum; Theorem 5.9 establishes
  the structural alternatives. Lemma 5.8 supplies the repeated-triple
  argument, and the remarks after Theorem 5.9 report the 67 + 1
  nonisomorphic covering count.
- R. G. Stanton, *Isomorphism Classes of Small Covering Designs with
  Block Size Five*, in C. J. Colbourn and R. Mathon (eds.),
  *Combinatorial Design Theory*, North-Holland, 1987, pp. 441-448.
  [DOI](https://doi.org/10.1016/S0304-0208(08)72910-4).
  GPPT cite this classification in Theorem 3.1.
  The project uses its own structural reconstruction and
  [Lean verification](../11-5-2/README.md); the original Stanton
  chapter remains unread.

The following correspondence separates the historical results from the
proof supplied here. Section numbers refer to this document; theorem and
property numbers refer to the retained GPPT author copy.

| Present statement | GPPT source and relationship |
|---|---|
| §1, Stanton prerequisite | Theorem 3.1 attributes the classification to Stanton. This project independently proves it in the companion component. |
| §1, marked couples and short rows | Properties 3.2–3.7 and 3.10–3.17. The companion Stanton proof now derives the required geometry explicitly. |
| §1, multiplicity-two rules | Properties 3.20–3.21 and 3.23. No pair has full-row multiplicity two, and a pair of total multiplicity two lies in the short row with a degree-four endpoint. |
| §2, partial Figure 1 covers triples | Lemma 2.1; the project gives an incidence proof. Its additional element-minimality conclusion is not needed or formally claimed. |
| §§1, 3–4, minimum points and compatibility | Proposition 5.1, Lemma 5.2, Corollary 5.3 and Lemmas 5.4–5.5. The at-most-fifteen formulation allows these facts to prove the lower bound without circularity. |
| §4, numerical minimum | Theorem 4.4. The project proves the same conclusion using the preceding compatibility lemma. |
| §5, repeated minimum triple | Lemma 5.8, with the excess argument and exact shared-row contradiction written out here. |
| §§6–9, no repeated minimum triple | These sections replace the proof of Lemmas 5.6–5.7 by projection, Fano rigidity and the seven-cap argument. |
| §10, disjoint structural alternatives | The structural classification and separation in Theorem 5.9. Its additional element-minimality assertions are outside the formal result. |
| §11, 67 + 1 types | The computer-calculation remarks after Theorem 5.9 report pairwise nonisomorphism. The present checked completion witnesses prove catalogue coverage, a strictly narrower assertion. |

The local compatibility and repeated-triple arguments follow GPPT,
with the shortened excess reasoning identified in Section 5.3.
The projective branch in Sections 6–9 replaces the argument of GPPT
Lemmas 5.6–5.7. The kernel-checked finite witnesses certify
catalogue completeness as a separate reusable result. The thirteen-point
proof uses the structural theorem and its local lemmas, with no dependency
on those completion witnesses.
These are contributions to the proof and verification presented here;
no historical novelty claim is made for the known theorems or the
alternative arguments.

## Appendix A. Correspondence with Lean

This appendix records the actual hypotheses and deductions connecting the
arbitrary covering to the two structural forms. In particular, the frame,
six-point projection, row labelling and projective normals are proved to
exist; none is assumed as an additional classification hypothesis.

The abbreviations below refer to namespaces:

- `G` = `CoveringDesigns.GPPTStructural`.
- `F` = `CoveringDesigns.GPPTStructural.TriplicateFrame`.
- `P` = `CoveringDesigns.GPPTProjective`.
- `T` = `CoveringDesigns.GPPTProjectiveTemplate`.
- `S` = `CoveringDesigns.StantonGeometry`.
- `B` = `CoveringDesigns.BinaryCap`.
- `CV` = `CoveringDesigns.GPPTStructural.CompletionVerification`.

Other unqualified names are in `CoveringDesigns`. Source-local private
helpers are identified as such; they are not additional exported theorems.

### A.1. Links, minimum pairs and the lower bound

| Passage | Lean declarations and role |
|---|---|
| §1, links and incidence counts | [Links](../../lean/CoveringDesigns/Foundations/Links.lean): `link_card`, `link_isCover`; [SmallBounds](../../lean/CoveringDesigns/C12_6_3/SmallBounds.lean): `degree_at_least_seven_12_6_3`, `lower_bound_12_6_3_schonheim`; [GPPTConsequences](../../lean/CoveringDesigns/C12_6_3/GPPTConsequences.lean): `six_minimum_points_at_most_fifteen`. |
| §1, excess budget | [Moments](../../lean/CoveringDesigns/C12_6_3/Structural/Moments.lean): `G.total_excess_le_six`, `G.total_excess_six`. |
| §1, Stanton geometry used | [Geometry](../../lean/CoveringDesigns/C11_5_2/Geometry.lean): `S.geometry_facts`, `S.exists_marking_frame`; see the [Stanton correspondence appendix](../11-5-2/proof.md#appendix-a-correspondence-with-lean) for their independent derivation. |
| §2, explicit partial covering and witness | [ProjectiveTemplate](../../lean/CoveringDesigns/C12_6_3/Structural/ProjectiveTemplate.lean): `T.standardNormal`, `T.standard_coreFamily`; [Witnesses](../../lean/CoveringDesigns/C12_6_3/Witnesses.lean): `figure1_covers`, `figure6_isCover`, `figure6_card`. The numerical theorem uses Figure 6. |
| §3, pair degree between three and four | Moments: `G.pair_degree_at_least_three_12_6_3`; GPPTConsequences: `minimum_pair_degree_le_four`. |
| §3, aligned marking frames and common short row | [CommonShort](../../lean/CoveringDesigns/C12_6_3/Structural/CommonShort.lean): `G.CommonShort.of_frames`, `G.exists_common_short_frame`. |
| §3, agreeing triads are nonminimum | [MinimumPairs](../../lean/CoveringDesigns/C12_6_3/Structural/MinimumPairs.lean), namespace `G.MinimumPairs`: `two_shared_selections`, `nonselected_pair_at_least_five`, `selected_triple_count`, `triple_two_forces_nonminimum`, `selected_nonminimum`. |
| §3, the remaining triad and its contradiction | Same module and namespace: `third_triad_minimum`, `shortTrace_of_different_selection`, `nonshort_pair_degree_three`, `minimum_third_triad_impossible`; [Frames](../../lean/CoveringDesigns/C12_6_3/Structural/Frames.lean): `G.RootedFrame.nonmarked_meets_triad`. |
| §3, minimum-pair lemma | MinimumPairs: `G.minimum_pair_degree_three`, under the at-most-fifteen hypothesis. Its proof uses neither the lower bound fifteen nor shortness symmetry. |
| §4, lower bound and multiplicity of a repeated minimum triple | [Branching](../../lean/CoveringDesigns/C12_6_3/Structural/Branching.lean): `G.lower_bound_fifteen`, `G.minimum_triple_not_two`, `G.repeated_minimum_triple_count`. |
| §4, shortness symmetry | [ShortSymmetry](../../lean/CoveringDesigns/C12_6_3/Structural/ShortSymmetry.lean): `S.Facts.short_of_singleton_intersection`, `G.swap_link_singleton_intersection`, `G.minimum_short_symmetry`, `G.minimum_short_iff`. The symmetry conclusion requires only the two minimum links, with no total-size bound. |
| §4, minimum point in another short row | Same module: `G.minimum_in_short_block_is_short`, using the minimum-pair lemma and hence the at-most-fifteen hypothesis. |

The frame-alignment paragraph in §3 uses the fact that two common marked
rows determine the third by their complementary triads. Lean obtains the
same equality by first excluding a marked row being the other frame's
short row: one of its selected points would then belong to two disjoint
marked triads. Both arguments establish the actual shared-row equality,
without a symmetry assumption.

### A.2. The repeated-triple branch

| Passage | Lean declarations and role |
|---|---|
| §5, all blocks belong to the three stars | [Frames](../../lean/CoveringDesigns/C12_6_3/Structural/Frames.lean): `G.three_minimum_stars_cover`. |
| §5, construction and alignment of the root frames | Same module: `G.exists_rooted_frame`, `G.RootTriads.alignment`, `G.RootedFrame.exists_alignedRow`, `G.RootedFrame.couple_point_not_mem_short`, `G.exists_triplicate_frame`; [Branching](../../lean/CoveringDesigns/C12_6_3/Structural/Branching.lean): `G.triplicate_frame_of_not_noDuplicate`. The construction uses the chosen roots; the public result packages the resulting frame as `Nonempty (TriplicateFrame C)`. |
| §5, distinct positions and degree formula | [Triplicate](../../lean/CoveringDesigns/C12_6_3/Structural/Triplicate.lean): `F.blockAt_image`, `F.blockAt_injective`, `F.row_incidence_count`, `F.degree_eq_seven_additions`, `F.additions_total`. |
| §5.1, injective columns | Same module: `F.injective_isFigure4Completion`, `F.injective_isomorphicTemplateCompletion`; [Templates](../../lean/CoveringDesigns/C12_6_3/Structural/Templates.lean): `G.figure1To4`, `G.relabel_core`, `G.map_spine`, `G.figure4Completion_isomorphicTemplateCompletion`. |
| §5.2, saturation of the twelve uncovered triples | Triplicate: `G.short_cross_capacity`, `G.common_short_saturation`, `G.common_short_mates_forced`, `F.common_short_cross_covered`, `F.additions_eq_common_mates`. |
| §5.2, remaining columns injective | Same module: `F.other_triad_degree_seven`, `F.repeated_selection_mates_pair_ge_five`, `F.other_column_injective`. |
| §5.2, exact Figure 6 family | [Exceptional](../../lean/CoveringDesigns/C12_6_3/Structural/Exceptional.lean): `F.common_column_isomorphic_figure6_of_injective`, `F.common_column_isomorphic_figure6`. Private coordinate helpers construct a bijection and prove equality of entire families. The direct coverage explanation in §5.2 concerns the same explicit witness checked by `figure6_isCover`. |
| §5.3, repeated triad has no minimum point | Triplicate: `F.minimum_selected_twice_all`, `F.repeated_column_no_minimum`. |
| §5.3, no second repeated column | Same module: `F.repeated_column_excess_ge_four_of_zero`, `F.other_columns_injective_of_repeated`. |
| §5.3, existence of a suitable minimum selection | Same module: `F.exists_minimum_selected_other_column`. Lean expresses the equivalent budget contradiction as at least $3+2+2>6$ excess incidences. |
| §5.3, exact two-occurrence contradiction | [TriplicateContradiction](../../lean/CoveringDesigns/C12_6_3/Structural/TriplicateContradiction.lean): `F.repeated_column_minimum_selected_contradiction`, with internal pair-count facts `hpair` and `hmates`. These counts are uniform in the unknown short-row additions. |
| §5.3, normalization and exhaustive alternatives | [TriplicateReindex](../../lean/CoveringDesigns/C12_6_3/Structural/TriplicateReindex.lean): `F.reindex`; [TriplicateClassification](../../lean/CoveringDesigns/C12_6_3/Structural/TriplicateClassification.lean): `F.repeated_column_minimum_contradiction`, `F.columns_injective_or_common`, `F.classification`. Reindexing permutes coordinates of the given frame; it assumes no automorphism of the covering. |

### A.3. The projective branch

| Passage | Lean declarations and role |
|---|---|
| §6, incidence moments and polynomial obstruction | [Moments](../../lean/CoveringDesigns/C12_6_3/Structural/Moments.lean): `G.containment_moment`, `G.point_incidence_moment`, `G.intersection_moment_inequality`, `G.repeated_triple_of_seven_minimum_points`. |
| §6, six minimum and six degree-eight points | Same module: `G.no_duplicate_minimum_points_card`, `G.no_duplicate_degree_seven_or_eight`, `G.no_duplicate_degree_eight_card`. |
| §7, at most four minimum points per row | [Projection](../../lean/CoveringDesigns/C12_6_3/Structural/Projection.lean): `G.no_duplicate_common_minimum_card`, `G.no_duplicate_block_minimum_card`. |
| §7, five-bin histogram | Same module: `G.five_bin_moments`, `G.no_duplicate_low_histogram`. |
| §7, pair partition and exhaustive distinct traces | [ProjectionFrame](../../lean/CoveringDesigns/C12_6_3/Structural/ProjectionFrame.lean): `G.ThreePairPartition`, `G.LowProjectionFrame`, `G.exists_low_projection_frame`. |
| §7, bijective row coordinates | [ProjectionCoordinates](../../lean/CoveringDesigns/C12_6_3/Structural/ProjectionCoordinates.lean): `G.coordinateTrace_range`, `G.coordinateTrace_injective`, `G.LowProjectionFrame.rowEquiv`, `.mem_iff_lowEquation`, `.toProjectionLabelling`. The fixed trace table is separate from the argument that the arbitrary covering has exactly these traces. |
| §8, local planes from Stanton | [Geometry/Fano](../../lean/CoveringDesigns/C11_5_2/Geometry/Fano.lean): `S.exists_fano_columns`, `S.fano_eq_of_five_columns`, `S.column_meets_line_of_five_columns`. |
| §8, identification of the coordinate planes | [ProjectiveGluing](../../lean/CoveringDesigns/C12_6_3/Structural/ProjectiveGluing.lean): `P.fanoVector`, `P.lowVector`, `P.localRowEquiv`, `P.coordinatePlane`, `P.lowColumn_mem`, `P.lowColumn_injective`, `P.lowColumn_card`; [ProjectiveCover](../../lean/CoveringDesigns/C12_6_3/Structural/ProjectiveCover.lean): `P.ProjectionLabelling.column_blocks_lines`. The distinct-column hypothesis is proved. |
| §8, actual absence sets and local restrictions | ProjectiveCover: `P.ProjectionLabelling.absentRows_card`, `.zero_not_absentRows`, `.infinity_not_absentRows`, `.absentRows_locallySumFree`. |
| §8, the exceptional line and its exclusion | ProjectiveGluing: `P.line_low_or_exceptional`, `P.sum_in_exceptional`, `P.card_le_six_of_exceptional_subset`, `P.seven_locally_sum_free`. |
| §9, zero-free seven-cap lemma | [BinaryCap](../../lean/CoveringDesigns/Foundations/BinaryCap.lean): `B.seven_cap_affine_hyperplane`; its private helpers `choose_four`, `combine_injective`, `fourfold_not_mem`, `parity_eq_one` implement the basis and parity argument. |
| §9, cores of the actual columns | ProjectiveCover: `P.ProjectionLabelling.high_column_normal`, `.all_column_normals`. These conclude the existence of normals; they do not assume them. |
| §9, no repeated normal | [ProjectiveTemplate](../../lean/CoveringDesigns/C12_6_3/Structural/ProjectiveTemplate.lean): `T.kernel_row_sum`, `T.normal_injective`. |
| §9, the omitted three normals form a line | Same module: `T.omitted_card`, `T.omitted_meets_kernel`, `T.omitted_is_line`; BinaryCap: `B.three_point_blocking_collinear`. |
| §9, incidence-preserving coordinate change | BinaryCap: `B.pair_normalize`; ProjectiveTemplate: `T.exists_dual_row`, `T.coreFamily_linear`, `T.coreFamily_isomorphic_figure1`, `T.standard_coreFamily`. |
| §9, exact completion family | ProjectiveTemplate: `T.templateCompletion_of_partial_extension`, `T.isomorphic_completion_of_normal_cores`. These establish equality of the original family with twelve full rows and three short-row completions. |
| §§6–9, complete no-repetition branch | ProjectiveCover: `P.no_duplicate_isomorphicTemplateCompletion`. It supplies its pair-degree premise from `G.minimum_pair_degree_three` and constructs all subsequent data. |

The row-table formula in §7 is the concrete meaning of `coordinateTrace`.
For the local Fano identification, Lean's `fanoVector` labels its seven
rows by the three-dimensional vectors
$100,010,001,111,011,101,110$, in that order. For a minimum point $(i,b)$,
`lowVector` inserts $x_i=bt$, leaving $t$ and the other two coordinates
free. This transports the Stanton row-plane to the coordinate plane.
The fixed `standardNormal` table is exactly the labelling formula of §2.
These small identities identify explicit objects; they do not assert that
an arbitrary covering has those objects without the preceding deductions.

### A.4. Separation, catalogue and assembly

| Passage | Lean declarations and role |
|---|---|
| §10, degree obstruction separates the alternatives | [Separation](../../lean/CoveringDesigns/C12_6_3/Structural/Separation.lean): `G.templateBlocks_degree_le_nine`, `G.figure6_degree_four`, and the isomorphism obstruction. The second name refers to the point labelled 4, whose degree is ten. The upper bound is proved even for arbitrary additions. |
| §10, structural dichotomy and disjointness | [Reduction](../../lean/CoveringDesigns/C12_6_3/Structural/Reduction.lean): `gppt_structural_reduction`, `gppt_structural_alternatives_disjoint`. |
| §11, exact completion inputs | [CompletionEncoding](../../lean/CoveringDesigns/C12_6_3/Structural/CompletionEncoding.lean): `CV.NormalInput`; [CompletionData](../../lean/CoveringDesigns/C12_6_3/Structural/CompletionData.lean): `CV.choiceData`, `CV.choice`, `CV.normalizerData`, `CV.normalizer`; [CompletionChecks](../../lean/CoveringDesigns/C12_6_3/Structural/CompletionChecks.lean): `CV.choices_checked`, `CV.completion_inputs_checked`. |
| §11, normalization and sound witnesses | [Completions](../../lean/CoveringDesigns/C12_6_3/Structural/Completions.lean): `CV.normalizer_sound`, `CV.exists_normalization`, `CV.completionCheck_sound`, `G.template_classification`; CompletionChecks: `CV.targets_checked`. |
| §11, exceptional catalogue entry | [CatalogueBridge](../../lean/CoveringDesigns/C12_6_3/CatalogueBridge.lean): `G.figure6_eq_exceptional`. |
| Full catalogue completeness and numerical value | [Classification](../../lean/CoveringDesigns/C12_6_3/Classification.lean): `gppt_classification`, `gppt_classification_on`, `lower_bound_12_6_3`, `covering_number_12_6_3`. |

The normalized input type is `Bool × Fin 28 × Fin 28`. In particular,
`completion_inputs_checked` proves that the list of witness keys equals
the complete normalized-input list; it does not merely check that each
supplied key is valid. `completionCheck_sound` proves equality of the entire
relabelled completed family with its target. The point symmetries in §11
explain the normalization; Lean checks the particular 28 chosen normalizers,
without needing a classification of the automorphism group.

## Appendix B. Contracts, dependencies and verification

### B.1. Exact theorem statements

`Family α` means `Finset (Finset α)`, so repeated blocks are absent.
`IsCover C 6 3` requires every block to have exactly six points and every
three-element subset of the point type to be contained in a member of `C`.
`Isomorphic C D` requires a point bijection whose action gives exact
equality of the two block families.

The structural contract, available from
`CoveringDesigns.C12_6_3.Structural.Reduction`, is:

```lean
theorem gppt_structural_reduction {C : Family (Fin 12)}
    (hC : IsCover C 6 3) (hb : C.card = 15) :
    GPPTStructural.IsomorphicTemplateCompletion C ∨ Isomorphic C figure6
```

`IsomorphicTemplateCompletion` means isomorphic to `templateBlocks R` for
some `R` satisfying `ValidAdditions`: for each of the three fixed spines,
`R i` is a two-set outside that spine. `templateBlocks R` is the union of
the fixed twelve-block core and the three completed rows. Thus this is an
exact family description. The companion theorem is:

```lean
theorem gppt_structural_alternatives_disjoint (C : Family (Fin 12)) :
    ¬ (GPPTStructural.IsomorphicTemplateCompletion C ∧ Isomorphic C figure6)
```

The full import `CoveringDesigns.C12_6_3` additionally exports:

```lean
theorem gppt_classification {C : Family (Fin 12)}
    (hC : IsCover C 6 3) (hb : C.card ≤ 15) :
    C.card = 15 ∧ ∃ i : Fin 68, Isomorphic C (linkRepresentative i)
```

`gppt_classification_on` transports this to any finite point type of
cardinality twelve. The numerical theorem `covering_number_12_6_3` combines
an explicit fifteen-block witness with a universal lower bound of fifteen.
There is no classification assumption, computational hypothesis or
unproved citation in these statements.

The catalogue index is existential, not unique. Pairwise nonisomorphism
of the 68 entries and GPPT's element-minimality conclusions are not
asserted. The structural result does not depend on either assertion.

### B.2. Dependency boundary used by C(13,7,4)

The dependency chain for the structural result is shared finite-counting
foundations, the separately proved Stanton classification and its geometry,
then the local compatibility and two branches described here. The C13
proof imports this structural layer and its local lemmas. It imports none
of `Catalogue`, `CatalogueBridge`, `Classification`, or the five completion
modules `CompletionEncoding`, `CompletionData`, `CompletionSupport`,
`CompletionChecks`, `Completions` from the GPPT component.

The full GPPT entry point adds those catalogue modules after the structural
reduction. The numerical lower bound is already established in `Branching`;
the upper bound uses the independently checked Figure 6 witness. No part
of this component depends on the thirteen-point theorem or exploratory
research code. The source audit enforces these import boundaries.

### B.3. What the checks establish

The arbitrary-cover arguments are structural. Fixed finite checks identify
the explicit Stanton representatives, local incidence geometry, coordinate
tables, permutations and Figure 1/Figure 6 witnesses. The separate catalogue
step checks all 1,568 normalized completion witnesses. All of these finite
checks use ordinary Lean kernel proofs, with no native assertions or
external solver certificates. The witness generator proposes data; the
properties needed by the proof, including exhaustive normalized inputs,
are established inside Lean.

The [component audit](../../lean/audits/C12_6_3.lean) prints the basic and
template-completion definitions, checks the exact structural, disjointness
and catalogue signatures, and restates the numerical theorem using explicit
cardinalities and inclusions. Transitive `#guard_standard_axioms` checks
permit only `propext`, `Classical.choice` and `Quot.sound`; individual lemmas
need not use all three. The recorded verification separately requires the
expected exact three-axiom set for the numerical theorem and its explicit
restatement. It also validates the source, log and build fingerprints.

From the repository root, `./covering check` checks source boundaries, retained
inputs and deterministic data generation; it does not verify Lean proofs.
`./covering verify 12-6-3` rebuilds the standalone component and prerequisites,
and `./covering audit 12-6-3` validates its recorded evidence. The
[shared verification guide](../../technical-details.md#gppt-verification-and-fresh-replay)
contains the focused verification and fresh-replay procedure, alongside
toolchain setup instructions.

The correspondence appendices are a reviewed account of the formal proofs.
Lean verifies the statements and their proof terms, not the Markdown text.
The historical sources provide attribution and comparison; a reader need
not obtain Stanton's original chapter to check this dependency chain.
