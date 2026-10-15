# A structural proof that C(13,7,4) = 30

**Rob Gardiner**

## Abstract

Every covering of the four-element subsets of a thirteen-point set by
seven-element blocks has at least thirty blocks. A known thirty-block
construction attains this bound, so $C(13,7,4)=30$. The lower bound is
proved by comparing minimum point links, using structural results for
coverings on eleven and twelve points. A hypothetical covering with at
most 29 blocks has at least five points of degree fifteen. Compatibility
between their links forces containment counts $15,7,3,1$ on the one-, two-,
three- and four-element subsets of a chosen five-set. An incidence count
then gives at least thirty blocks, contradicting the assumed bound. The
result and its structural prerequisites are formalized in Lean. The
thirteen-point proof uses no enumeration of covering completions or search
certificates; its public theorem depends only on Lean's three standard
foundational axioms.

## Introduction

For integers $1\le t\le k\le v$, a **$(v,k,t)$ covering** is a family of
distinct $k$-element subsets, called blocks, of a $v$-point set, such that
every $t$-element subset lies in some block. The **covering number**
$C(v,k,t)$ is the smallest possible number of blocks in such a family.

This note concerns coverings of four-subsets of thirteen points by
seven-subsets. A known thirty-block construction retained from the
La Jolla Covering Repository [3](#references) gives the upper bound.
The contribution here is the structural lower-bound argument establishing
the following result.

**Theorem 1.** Every family of distinct seven-element subsets of a
thirteen-point set that covers every four-element subset has at least
thirty blocks. A covering with exactly thirty blocks exists. Thus

$$
C(13,7,4)=30.
$$

### Background and contribution

The local ingredients come from smaller covering problems. Deleting a
point from the blocks through it gives a $(12,6,3)$ covering; deleting
two points from the blocks through that pair gives an $(11,5,2)$ covering.
The minimum forms of these smaller coverings constrain how blocks can
fit together on thirteen points.

R. G. Stanton's classification of minimum $(11,5,2)$ coverings
[1](#references) supplies the eleven-point geometry. The twelve-point
results are those of Daniel M. Gordon, Oren Patashnik, John Petro and
Herbert Taylor (**GPPT**), authors of *Minimum (12,6,3) Covers*
[2](#references). References to GPPT's Figure 1 and Figure 6 mean the
figures in that paper. These classifications and the local lemmas used
here are proved in this project's eleven- and twelve-point Lean components.

The thirteen-point argument compares local descriptions arising from the
same covering. It identifies shared structures intrinsically and aligns
their coordinates. In a hypothetical covering with at most 29 blocks,
these comparisons constrain how the degree-fifteen points can occur
together in blocks. The argument applies to arbitrary completions of the
GPPT forms; the separate catalogue of 68 twelve-point coverings is not used.

### Proof outline

Suppose a covering $\mathcal C$ had at most 29 blocks. A point's degree is
the number of blocks containing it. Lemma 6 gives at least five points of
degree fifteen, called minimum points. We prove two compatibility statements:

- distinct minimum points occur together in exactly seven blocks
  (Proposition 15);
- four minimum points whose internal pair multiplicities are seven cannot
  occur together in three blocks (Proposition 23).

Together with the local results, these statements force the multiplicities

$$
15,\quad 7,\quad 3,\quad 1
$$

on the one-, two-, three- and four-element subsets of those five points.
The counting lemma turns this profile into

$$
75+30\le |\mathcal C|+70+5,
$$

so $|\mathcal C|\ge30$, a contradiction.

Sections 1–2 give the notation, local results and counting target.
Section 3 proves the pair compatibility statement; Section 4 proves the
four-point statement. Section 5 assembles the proof of Theorem 1. The
numbered statements follow the mathematical steps of the Lean formalization.
[Appendix A](#appendix-a-lean-correspondence-and-dependency-checks) records
the exact correspondence with Lean and its dependency and axiom checks.
[Appendix B](#appendix-b-verification-and-retained-artifacts) gives
reproduction commands, verification evidence and source provenance.

## 1. Notation and the proved local results

Let $V$ be a set of thirteen points and let $\mathcal C$ be a family of
distinct seven-element subsets of $V$ covering every four-element subset.
Write

$$
d_{\mathcal C}(S)=|\{B\in\mathcal C:S\subseteq B\}|,
\qquad
\operatorname{star}_{\mathcal C}(p)=\{B\in\mathcal C:p\in B\}.
$$

We abbreviate $d_{\mathcal C}(\{p\})$ to $d(p)$, and use $d(pq)$,
$d(pqr)$ and $d(K)$ for the corresponding containment counts. A point is
called **minimum** when $d(p)=15$.

The **point link** is

$$
L_p=\{B\setminus\{p\}:B\in\mathcal C,\ p\in B\}.
$$

Its points belong to $V\setminus\{p\}$. When taking degrees inside a link,
we write the link explicitly as a subscript. This separates a global
containment count from a degree in a smaller covering.

In a displayed family of rows, a point's **column** records which rows
contain it. Two points have identical columns when their stars in that
family agree. A row will always be identified as a global block, a link
block or a trace.

The sizes of the sets used later are as follows.

| Object | Points retained | Size of a block or trace |
|---|---|---:|
| Global block | All of $V$ | 7 |
| Point-link block | One root deleted | 6 |
| Common trace at two roots | Both roots deleted from a block containing both | 5 |
| Private trace at two roots | The sole root of a block deleted; the other root was absent | 6 |
| Edge trace at four roots | The two roots present in a block deleted | 5 |

### Lemma 2. Links and incidence counts

For every $p\in V$, $L_p$ is a $(12,6,3)$ covering with $d(p)$ blocks.
For every $T\subseteq V\setminus\{p\}$,

$$
d_{L_p}(T)=d_{\mathcal C}(\{p\}\cup T).
\tag{1}
$$

Also,

$$
\sum_{p\in V}d(p)=7|\mathcal C|.
\tag{2}
$$

**Proof.** Deleting $p$ from a block through $p$ is injective: reinserting
$p$ recovers that block. The resulting blocks have size six. A triple $T$
outside $p$ is covered because the four-set $\{p\}\cup T$ is covered by
a global block containing $p$. The same deletion and reinsertion identify
the blocks counted on the two sides of (1). Finally, count point–block
incidences. Each global block contributes seven, proving (2). $\square$

The eleven- and twelve-point components prove the local results below.
Their full arguments are in the [Stanton proof](../11-5-2/proof.md) and
[GPPT proof](../12-6-3/proof.md).

### Lemma 3. Geometry of a minimum twelve-point link

Every fifteen-block $(12,6,3)$ covering $L$ has one of the following two
geometries.

**Ordinary geometry.** The covering is the disjoint union, as families of
blocks, of twelve full core blocks and three completed blocks. Each
completed block consists of a four-point **spine** and two additions outside
that spine. The three spines partition the twelve points. Every point
belongs to six full core blocks and to at least its own spine completion.
Distinct full core blocks intersect in at most three points. Every point
consequently has degree seven, eight or nine.

**Exceptional geometry.** There is a distinguished pair $H$ of points.
Both points of $H$ have degree ten and occur in exactly the same blocks;
every other point has degree seven. A distinguished point and a point
outside $H$ occur together four times. Whenever distinct blocks intersect
in four points, both endpoints of that block pair contain $H$.

In either geometry, distinct blocks intersect in at most four points.

**Proof.** The twelve-point component proves the structural alternative
of GPPT Theorem 5.9 [2](#references): up to relabelling, $L$ is a completion
of Figure 1 or the fixed Figure 6 family. Their incidence properties follow
from the descriptions below.

For **Figure 1**, regard the three spines as disjoint copies of the square
$\mathbb F_2^2$, with points $00,01,10,11$. The three nonzero linear
forms divide each square into the following halves; addition is modulo two.

| Linear form $\ell(u,v)$ | Half $\ell=0$ | Half $\ell=1$ |
|---|---|---|
| $u$ | $00,01$ | $10,11$ |
| $v$ | $00,10$ | $01,11$ |
| $u+v$ | $00,11$ | $01,10$ |

Choose one form $\ell$ and one half $\ell=\epsilon_j$ in each spine,
subject to $\epsilon_0+\epsilon_1+\epsilon_2=0$. Their union is a full
core block. The three forms and four even-parity choices give the twelve
blocks. For example, choosing $\ell=u$ and $(\epsilon_0,\epsilon_1,
\epsilon_2)=(0,0,0)$ takes $00,01$ from each spine.

Each point belongs to two blocks for each form, hence six full blocks.
Two distinct blocks using the same form agree in one spine and differ in
the other two, so intersect in two points. Blocks using different forms
meet in one point per spine, hence in three points. Each full block meets
each spine in two points. Its intersection with a completed block therefore
has at most those two points and the two additions. For two different
completed blocks, their intersection lies in the union of their two pairs
of additions, again giving at most four. Adding the three spine completions
to the six full-core incidences gives point degrees seven, eight or nine.

For **Figure 6**, the twelve points are a distinguished pair $H$ and the
ten edges of $K_5$. Write $E(K_5-W)$ for the edges whose endpoints both
avoid the vertex set $W$. The fifteen blocks are

$$
A_v=E(K_5-\{v\}),\qquad
B_e=H\cup\{e\}\cup E(K_5-\operatorname{ends}(e)).
$$

There are five $A_v$ blocks, each with six edges, and ten $B_e$ blocks,
each consisting of $H$, the edge $e$ and the three edges of the remaining
triangle. The points of $H$ lie in all ten $B_e$ blocks and in no $A_v$.
An edge-point lies in three $A_v$ blocks and four $B_e$ blocks: its own
$B_e$ and those indexed by the three edges disjoint from it. Thus its
degree is seven, and it occurs four times with either distinguished point.

For distinct blocks, $|A_v\cap A_w|=3$, while $|A_v\cap B_e|$ is three
if $v$ is an endpoint of $e$ and two otherwise. Two distinct $B_e,B_f$
intersect in four points precisely when $e,f$ are disjoint; their
intersection is then $H\cup\{e,f\}$. If the edges share an endpoint,
the intersection has size three. This proves both the intersection bound
and the distinguished-pair property.

To identify these models with the literal families in
[the Lean source](../../lean/CoveringDesigns/C12_6_3/Witnesses.lean), send
Figure 1's label $4j+2u+v$ to $(u,v)$ in spine $j$, where $j=0,1,2$.
For Figure 6, take $H=\{4,5\}$ and label the vertices of $K_5$ by
$0,1,2,3,4$. The remaining point labels correspond to edges as follows,
where $ij$ denotes the edge $\{i,j\}$:

| Literal point | 0 | 1 | 2 | 3 | 6 | 7 | 8 | 9 | 10 | 11 |
|---|---|---|---|---|---|---|---|---|---|---|
| $K_5$ edge | $34$ | $24$ | $23$ | $01$ | $12$ | $13$ | $14$ | $02$ | $03$ | $04$ |

Under these identifications, the displayed models give exactly the literal
Figure 1 core and Figure 6 family. Lean checks the incidence identities of
those literal families and transports the resulting properties along the
isomorphisms supplied by the structural reduction. $\square$

Here and below, a **matching of block pairs** means that every block
endpoint is distinct. The blocks themselves need not be disjoint as point
sets. In an ordinary link, any intersection-four pair must have a completed
block as an endpoint, since two full core blocks intersect in at most three
points. A matching therefore uses a different completed endpoint for each
pair. There are only three completed blocks.

Moreover, a point of degree seven in an ordinary link belongs to exactly
one completed block: six of its seven incidences are in the full core.
These observations give the following tests, which will be used repeatedly.

### Lemma 4. Tests excluding a minimum point

A point $r$ cannot be minimum if any of the following configurations occurs
in $\mathcal C$.

1. Two distinct blocks through $r$ intersect in at least six points.
2. There are four pairs of blocks through $r$, with all eight endpoints
   distinct, each pair intersecting in five points, and the common
   intersection of all eight endpoints is exactly $\{r\}$.
3. There are three such pairs, with six distinct endpoints and common
   intersection exactly $\{r\}$. Every endpoint meets $\{p,q\}$, where
   $p,q\ne r$ and $d(pr)=d(qr)=7$.

**Proof.** Suppose $d(r)=15$. Deleting $r$ preserves distinctness of the
blocks through it and lowers each pair-intersection size by one.

In the first configuration, two link blocks would intersect in at least
five points, contrary to Lemma 3.

In the second configuration, $L_r$ has a matching of four
intersection-four pairs. Ordinary geometry permits at most three. In
exceptional geometry the distinguished pair must lie in every endpoint,
whereas deleting $r$ has left their common intersection empty.

In the third configuration, the same empty common intersection excludes
exceptional geometry. For ordinary geometry, (1) makes $p,q$ degree-seven
points of $L_r$. Each belongs to exactly one completed block. Since every
endpoint meets $\{p,q\}$, all completed endpoints used by the matching
belong to the union of these two completed-block stars. That union has
at most two blocks, but the three pairs require three distinct completed
endpoints. $\square$

### Lemma 5. Minimum pairs and repeated triples in twelve points

Let $L$ be a $(12,6,3)$ covering with at most fifteen blocks.

1. Two distinct degree-seven points of $L$ have pair multiplicity three.
2. A three-set of degree-seven points that occurs at least twice occurs
   exactly three times.

**Proof.** The first statement is GPPT Lemma 5.2 [2](#references), proved
in the twelve-point component as the minimum-pair lemma.
For the second, the triple multiplicity is at most three because it is
bounded by any of its pair multiplicities. To exclude two, take the link
of one point of the triple. Its degree is seven, so this is a seven-block
$(11,5,2)$ covering to which Stanton's classification applies. The other
two points have degree three in that link by the first statement. If the
original triple occurred twice, their pair would have multiplicity two
in the link. Stanton's local multiplicity-two rule, stated as Property 3.21
in GPPT [2](#references), would then force one of those two points to have
degree four, a contradiction. Thus a repeated triple has multiplicity three.
$\square$

## 2. The degree budget and the target count

The proved twelve-point lower bound is $C(12,6,3)=15$. It has two uses here:
it bounds every global point degree, and it identifies a degree-fifteen
link as a minimum covering to which Lemmas 3 and 5 apply.

### Lemma 6. Five minimum points in a small covering

Every point has degree at least fifteen. If $|\mathcal C|\le29$, there are
at least five minimum points.

**Proof.** Lemma 2 and the twelve-point lower bound give $d(p)\ge15$.
Equation (2) now yields

$$
\sum_{p\in V}(d(p)-15)=7|\mathcal C|-13\cdot15\le8.
\tag{3}
$$

Each nonminimum point contributes at least one to this nonnegative excess.
There are at most eight such points, leaving at least five minimum points.
$\square$

### Lemma 7. The five-point count

For this lemma, $\mathcal C$ may be any finite family of finite subsets of
a point set. Let $M$ be a five-element set of points. Suppose every subset
of $M$ of size one, two, three or four
has containment count fifteen, seven, three or one, respectively. Then
$|\mathcal C|\ge30$.

**Proof.** Put $r_B=|M\cap B|$ for $B\in\mathcal C$. Double-counting
incidences between blocks and the subsets of $M$ gives the following
identities; all sums range over $B\in\mathcal C$. A block with $r_B$
points of $M$ contains $\binom{r_B}{t}$ of its $t$-subsets, while each
such subset is contained in its prescribed number of blocks.

$$
\sum_B r_B=5\cdot15=75,
\qquad
\sum_B\binom{r_B}{2}=\binom52\cdot7=70,
$$

$$
\sum_B\binom{r_B}{3}=\binom53\cdot3=30,
\qquad
\sum_B\binom{r_B}{4}=\binom54\cdot1=5.
\tag{4}
$$

For an integer $0\le r\le5$, the fourth Bonferroni inequality is

$$
r+\binom r3\le1+\binom r2+\binom r4.
\tag{5}
$$

It holds in each of the six scalar cases $r=0,1,2,3,4,5$. Summing (5)
over the blocks and using (4) gives

$$
75+30\le |\mathcal C|+70+5,
$$

hence $|\mathcal C|\ge30$. No value of the fivefold containment count
$d(M)$ is required. $\square$

The same calculation has an inclusion–exclusion interpretation. A block
meeting $M$ in $r$ points contributes

$$
r-\binom r2+\binom r3-\binom r4
=\begin{cases}1,&1\le r\le4,\\0,&r=0\text{ or }r=5.\end{cases}
$$

Thus the alternating total $75-70+30-5=30$ counts the blocks belonging to
at least one of the five stars, except those containing all five points.
The union of the stars consequently has $30+d(M)$ blocks. The per-block
inequality (5) obtains the same lower bound directly, using only the four
containment counts already specified.

It remains to show that a covering with $|\mathcal C|\le29$ would satisfy
the hypotheses of Lemma 7.

## 3. Compatibility of two minimum links

### Lemma 8. The possible pair multiplicities

If $p$ is minimum and $q\ne p$, then

$$
d(pq)\in\{7,8,9,10\}.
$$

If $d(pq)$ is eight or nine, $L_p$ is ordinary. Under this eight-or-nine
hypothesis, if $q$ is also minimum, both $L_p$ and $L_q$ are ordinary.

**Proof.** The link at the pair is an $(11,5,2)$ covering, obtained by
applying point deletion twice. Its number of blocks is $d(pq)$, so the
eleven-point lower bound gives $d(pq)\ge7$. Since $L_p$ is minimum,
Lemma 3 gives $d_{L_p}(q)=d(pq)\le10$. Exceptional geometry has only
degrees seven and ten, so a degree-eight or degree-nine point requires
ordinary geometry. Pair multiplicity is symmetric in $p,q$, giving the
last assertion. $\square$

### Lemma 9. Multiplicity ten is impossible

If $|\mathcal C|\le29$ and $p,q$ are distinct minimum points, then
$d(pq)\ne10$.

**Proof.** Suppose $d(pq)=10$. Ordinary geometry has maximum degree nine,
so both links are exceptional. In $L_p$, let $r$ be the distinguished
mate of $q$. Its column agrees with the column of $q$, giving
$d(pqr)=10$.

In $L_q$, the point $p$ is distinguished. If $r$ were outside its
distinguished pair, the distinguished–ordinary pair rule would give
$d(pqr)=4$, contradicting ten. Thus the distinguished pair of $L_q$
is $\{p,r\}$.

For every $x\notin\{p,q,r\}$, exceptional geometry in the two links
therefore gives

$$
d(px)=d(qx)=7,\qquad d(pqx)=4.
$$

If $x$ were minimum, $p,q$ would be two degree-seven points of $L_x$.
Lemma 5 would make their pair multiplicity three, contradicting four.
All minimum points are consequently confined to $\{p,q,r\}$, contrary
to Lemma 6. $\square$

For multiplicities eight and nine, the main difficulty is identifying which
six blocks in the common overlap are full core blocks in both links.
For Lemmas 10–14, fix **distinct minimum points** $p,q$ with
$d(pq)\in\{8,9\}$. By Lemma 8 both links are ordinary. We describe
$L_p$ rooted at the retained point $q$, and $L_q$ rooted at the retained
point $p$; the other global root has already been deleted from each link.

Their **common overlap** is the family of five-point traces

$$
\mathcal O_{pq}=\{G\setminus\{p,q\}:G\in\mathcal C,\ \{p,q\}\subseteq G\}.
$$

Reinserting $p,q$ recovers each common global block, so
$|\mathcal O_{pq}|=d(pq)$. The two rooted frames give coordinate
descriptions of this same family on the eleven points outside $p,q$.
The coordinates in Lemma 10 are chosen from $L_p$. Lemma 11 then proves
that the six full rows selected by the two descriptions agree.

### Lemma 10. Rooted coordinates for an ordinary link

An ordinary link $L_p$, rooted at $q$, can be labelled using three
companions

$$
A=\{a_0,a_1,a_2\}
$$

and four **spouse pairs**

$$
\{x_v,y_v\},\qquad v=0,1,2,3.
$$

The three spines are $\{q\}\cup A$, $B=\{x_0,x_1,x_2,x_3\}$ and
$D=\{y_0,y_1,y_2,y_3\}$. Put $X=B\cup D$.

Index the three perfect matchings of the four spouse indices by $m=0,1,2$,
with their two edges denoted $E_m^0,E_m^1$. The orientation index
$\epsilon$ takes the values zero and one:

| $m$ | $E_m^0$ | $E_m^1$ |
|---|---|---|
| 0 | $\{0,1\}$ | $\{2,3\}$ |
| 1 | $\{0,2\}$ | $\{1,3\}$ |
| 2 | $\{0,3\}$ | $\{1,2\}$ |

The six five-point traces of full core blocks through $q$ are

$$
F_m^\epsilon=\{a_m\}\cup
 \bigcup_{v\in E_m^\epsilon}\{x_v,y_v\}.
\tag{6}
$$

The six full core blocks avoiding $q$ are the six-point private traces

$$
D_m^\epsilon=(A\setminus\{a_m\})\cup
 \{x_v:v\in E_m^\epsilon\}\cup
 \{y_v:v\in E_m^{1-\epsilon}\}.
\tag{7}
$$

Their corresponding global blocks are, respectively,
$\{p,q\}\cup F_m^\epsilon$ and $\{p\}\cup D_m^\epsilon$.

If $d(pq)$ is eight or nine, the common overlap consists of the six rows
in (6), the own-spine trace

$$
S=A\cup R,\qquad R\subseteq X,\quad |R|=2,
$$

and one or two foreign-spine traces. After exchanging $B,D$ if necessary,
these are

$$
T=B\cup\{u\},\quad u\in A\cup D,
\qquad
U=D\cup\{w\},\quad w\in A\cup B,
\tag{8}
$$

with $U$ present only for multiplicity nine. All the additions remain
arbitrary.

**Proof.** To normalize the root, interchange the spine containing $q$
with the first square, then translate the first and second squares by the
coordinate $z\in\mathbb F_2^2$ of $q$ there, leaving the third square fixed.
This sends $q$ to $00$ and adds $\ell(z)$ to two of the three half constants
for every form $\ell$, preserving their even parity. The map therefore
preserves the full core and permutes the spines. It also transports each
pair of additions outside its spine to a pair outside the image spine.

In these coordinates the twelve full core blocks are
$\{q\}\cup F_m^\epsilon$ and $D_m^\epsilon$. Thus (6) describes five-point
traces after deleting $q$, whereas (7) describes the six-point blocks
already avoiding $q$.

The root belongs to six full blocks and to its own completed spine. A
completed foreign spine belongs to the common overlap precisely when it
contains $q$. Deleting $q$ from that six-point completion leaves its four
spine points and one added point, giving (8). Deleting $q$ from its own
completion leaves $A$ and two additions, giving $S$.

The completed blocks are distinct from each other and from the full core.
Thus $d(pq)=8$ means two completed blocks through $q$, and $d(pq)=9$
means three. The coordinates lift back to actual blocks of $\mathcal C$
by reinserting $p$. $\square$

Write $\mathcal F=\{F_m^\epsilon:m=0,1,2,\ \epsilon=0,1\}$.
The two rows with the same $m$ are **opposite**: their intersection is
$\{a_m\}$. Rows from different matchings intersect in two points. The
companions have degree two in $\mathcal F$; the eight spouse points have
degree three, with identical columns exactly within each spouse pair.

These fixed incidence identities are the invariants used in recognition.
More generally, call a family a **six-row core** if it has the following
properties: six rows; distinct-row intersections of size at most two; a
unique opposite for each row, meaning a different row meeting it in
exactly one point; degree two for the point in any singleton opposite
intersection; and, for each degree-three point,
a different point with the same column. These are precisely the properties
of the formal structure `IsSixCore`.

### Lemma 11. The six common full rows are intrinsic

If a six-row core $\mathcal Q$ is contained in the overlap described in
Lemma 10, then $\mathcal Q=\mathcal F$. Consequently the two rooted
descriptions of an actual overlap agree on their six common full rows.

**Proof.** If $U$ is absent from the actual overlap, first adjoin an
auxiliary row of its displayed form to the list of allowed rows. We prove
uniqueness in the larger family $\mathcal F\cup\{S,T,U\}$, which also
proves it in the actual overlap. The auxiliary row is used only in this
containment argument; it is not asserted to be a block of $\mathcal C$.

First exclude the own-spine row $S$. If $S\in\mathcal Q$,
no original opposite pair can remain in $\mathcal Q$: its companion
point would lie in those two rows and in $S$, contradicting its required
degree two. Each retained old row nevertheless needs an opposite. It
cannot use $T$ or $U$, since every old row meets each foreign row in at
least two points. It must therefore use $S$.

The opposite of $S$ is unique, so at most one old row can remain. Even
with all three added rows $S,T,U$, that gives at most four rows, not six.
Hence $S\notin\mathcal Q$.

Now compare the old rows with a foreign row. If $u=a_m$, $T$ intersects
both $F_m^0,F_m^1$ in three points. If $u=y_z$, $T$ intersects in three
points the one row of each matching whose edge contains $z$. Thus $T$
conflicts with at least two old rows, and with exactly two only when its
addition is a companion. The same calculation applies to $U$.

Neither foreign row is an old row: it contains all four points of one
transverse half, while an old row contains only two of them. The foreign
rows are also distinct from each other, since a five-point row cannot
contain both disjoint four-point halves $B,D$.

Suppose $\mathcal Q\ne\mathcal F$. At least one foreign row must enter,
forcing at least two old rows to leave. Since at most two foreign rows
are available and both families have size six, exactly two rows leave
and both foreign rows enter. Their conflicting old-row sets must be the
same two rows. Each foreign row therefore conflicts with exactly two old
rows, so both additions are companions. The conflicting rows for $a_m$
are precisely its opposite pair $F_m^0,F_m^1$; equality of the conflict
sets forces the same companion in both additions. Thus

$$
u=w=a_m,
\qquad
\mathcal Q=(\mathcal F\setminus\{F_m^0,F_m^1\})
 \cup\{B\cup\{a_m\},D\cup\{a_m\}\}.
$$

This replacement violates the duplicate-column invariant. In particular,
$x_0$ still has degree three but has no different point with its column.
The two surviving matchings distinguish the four spouse indices, while
the new $B,D$ rows distinguish the two members of each spouse pair.
Companions have degree two, so none can supply the required mate for
$x_0$.

Thus $\mathcal Q=\mathcal F$.

Finally, the coordinate transition between $L_q$ and $L_p$ describes the
same eleven actual points outside $p,q$. It preserves membership in the
common overlap. Transporting the second six-row core along that transition
therefore produces a six-row core contained in the first overlap, so it
must equal $\mathcal F$. $\square$

### Lemma 12. Private cores agree or differ by one spouse swap

For an actual overlap of multiplicity eight or nine, express both rooted
links in the common coordinates of Lemma 11. Their six private full traces
are either identical as families or differ by exchanging the two members
of one spouse pair.

**Proof.** The companions are recognized by degree two in $\mathcal F$;
the spouse pairs are recognized by identical degree-three columns. Hence
any coordinate transition preserving $\mathcal F$ preserves $A$ and the
spouse-pair relation. The foreign spines $B,D$ each select one member of
every spouse pair. Their images under the transition therefore also
select one member of each pair. We call such a set a **transverse half**.

The own-spine trace $S$ is the unique common row containing all of $A$.
It is therefore the same actual completed row in both descriptions.
Since the overlap has at least eight rows, choose a foreign completed row
in the first description. In the second description it is also foreign:
it cannot become a full row, since the full-row families agree, and it
cannot become the own row, since it does not contain all of $A$.

The shared foreign row consequently has two descriptions

$$
B\cup\{u\}=B'\cup\{u'\},
\qquad u\notin B,\quad u'\notin B',
\tag{9}
$$

where $B,B'$ are transverse halves in the same spouse-pair system. If
$u=u'$, deleting that point gives $B=B'$. If $u\ne u'$, (9) gives

$$
u'\in B,\quad u\in B',\quad B'=(B\setminus\{u'\})\cup\{u\}.
$$

Since $u\in B'\subseteq X$, it is a spouse point. Its mate lies in $B$
because $u\notin B$, and must be absent from $B'$ because $u\in B'$.
The only removed point is $u'$, so $u'$ is that mate. Thus $B'$ is obtained
by one spouse swap.

It remains to pass from a transverse half to the private family. For a
common full trace $F$, define

$$
\Phi_{A,B}(F)=(A\setminus F)\cup(F\cap B)
 \cup\bigl(X\setminus(F\cup B)\bigr).
\tag{10}
$$

Using (6), the six images in (10) are exactly the six traces in (7).
Using the opposite half $D$ gives the same private family, with the two
orientations interchanged. The formula commutes with relabelling, since
it uses only unions, intersections and differences.

If the transverse halves agree, (10) therefore gives equal private
families. If they differ by a spouse swap, that swap preserves every
common full row and $A$, so (10) gives private families related by that
same swap. This proves the dichotomy using one shared foreign row in
either multiplicity. $\square$

### Lemma 13. Equal private cores are impossible

Under $|\mathcal C|\le29$, the identical-private-core alternative of
Lemma 12 is impossible.

**Proof.** For each six-point private trace $D_m^\epsilon$, both
$\{p\}\cup D_m^\epsilon$ and $\{q\}\cup D_m^\epsilon$ are actual
global blocks. They are distinct and intersect in six points. Every point
outside $p,q$ belongs to at least one of these private traces, as seen
from (7). Lemma 4(1) excludes every such point from being minimum. Only
$p,q$ could then be minimum, contrary to Lemma 6. $\square$

### Lemma 14. One spouse swap is impossible

Under $|\mathcal C|\le29$, the spouse-swap alternative of Lemma 12 is
also impossible.

**Proof.** Normalize the swapped pair to $\{x_0,y_0\}$ and the chosen
foreign half to $B$. Identify the four spouse indices with $\mathbb F_2^2$.
Its translations are $\mathrm{id},(01)(23),(02)(13),(03)(12)$.
Applying one of these to both sets of spouse labels, followed if necessary
by simultaneously exchanging every $x_v$ with $y_v$, preserves the common
core and the private core of $L_p$. These relabellings carry the swap and
the additions into the normalized coordinates.

Let $\tau$ exchange $x_0,y_0$. The covering contains the private blocks

$$
P_m^\epsilon=\{p\}\cup D_m^\epsilon,
\qquad Q_m^\epsilon=\{q\}\cup\tau D_m^\epsilon,
\tag{11}
$$

the six common full blocks $C_m^\epsilon=\{p,q\}\cup F_m^\epsilon$,
and the own completed block

$$
O=\{p,q\}\cup A\cup R,
\qquad R\subseteq X,\quad |R|=2.
$$

In the nontrivial alternative of Lemma 12, the addition to the chosen
foreign half is the opposite member of the swapped spouse pair, now $y_0$.
The covering therefore also contains the shared foreign completed block

$$
W=\{p,q,x_0,y_0,x_1,x_2,x_3\}.
\tag{12}
$$

All twelve endpoints in (11) are distinct. Each corresponding pair
$P_m^\epsilon,Q_m^\epsilon$ intersects in five points: the swap removes
the chosen member of spouse pair zero from their common private trace,
and their roots are different.

**A worked example at $x_1$.** The three private pairs through $x_1$
use the orientations $\epsilon_0=0$, $\epsilon_1=1$ and $\epsilon_2=1$.
The first pair is

$$
P_0^0=\{p,a_1,a_2,x_0,x_1,y_2,y_3\},\qquad
Q_0^0=\{q,a_1,a_2,y_0,x_1,y_2,y_3\}.
$$

Add the pair $C_0^0,W$, using the common full block for the edge
$\{0,1\}$. The four pairs have the following intersections:

| Pair of global blocks | Five-point intersection |
|---|---|
| $P_0^0,\ Q_0^0$ | $\{a_1,a_2,x_1,y_2,y_3\}$ |
| $P_1^1,\ Q_1^1$ | $\{a_0,a_2,x_1,x_3,y_2\}$ |
| $P_2^1,\ Q_2^1$ | $\{a_0,a_1,x_1,x_2,y_3\}$ |
| $C_0^0,\ W$ | $\{p,q,x_0,y_0,x_1\}$ |

The six private endpoints are distinct by (11). The last two endpoints
contain both roots, so differ from every private endpoint; they differ
from each other because $C_0^0$ contains $a_0$ and $W$ contains no companion.
The first three intersections have common intersection $\{x_1\}$,
and the fourth also contains $x_1$. Thus all eight endpoints have common
intersection exactly $\{x_1\}$. Deleting $x_1$ leaves four
intersection-four pairs with distinct endpoints and empty common
intersection in $L_{x_1}$. Lemma 4(2) excludes $x_1$ from being minimum.

**The general cases.** We exclude every point outside $\{p,q,x_0,y_0\}$
using the configurations below. Every spouse index in the table is nonzero.

| Point | Configuration through that point | Exclusion test |
|---|---|---|
| Companion $a_k$ | Four private pairs from (11) | Lemma 4(2) |
| $x_v$ | Three private pairs, plus a pair using $W$ | Lemma 4(2) |
| $y_v\in R$ | Three private pairs, plus a pair using $O$ | Lemma 4(2) |
| $y_v\notin R$ | Three private pairs; both pair degrees with $p,q$ are seven | Lemma 4(3) |

**The companions.** For $a_k$, take the four pairs in (11) with $m\ne k$.
All endpoints contain $a_k$. For a fixed such $m$, intersecting both
orientations and both roots leaves $A\setminus\{a_m\}$. Intersecting
over the two choices of $m\ne k$ leaves exactly $\{a_k\}$.
Lemma 4(2) therefore excludes $a_k$.

**Three private pairs at a spouse point.** For any $r=x_v$ or $y_v$ with
$v\ne0$, choose one orientation $\epsilon_m$ from each matching. For
$r=x_v$, choose $v\in E_m^{\epsilon_m}$; for $r=y_v$, choose
$v\in E_m^{1-\epsilon_m}$. Formula (7) puts $r$ in $D_m^{\epsilon_m}$,
and the swap leaves $r$ fixed. Thus $P_m^{\epsilon_m},Q_m^{\epsilon_m}$
are three pairs through $r$, with six distinct endpoints and five-point
intersections.

Their common intersection is exactly $\{r\}$. Every companion $a_m$
is absent from the pair indexed by $m$. For an index $z\ne v$, the
indices $v,z$ lie on the same edge in exactly one of the three matchings
and on opposite edges in the other two. If $r=x_v$, the three traces use
$x_z$ once and $y_z$ twice; if $r=y_v$, they use $y_z$ once and $x_z$
twice. Neither point belongs to all three $P$-blocks. Those blocks have common
intersection $\{p,r\}$; the $Q$-blocks also contain $r$ and omit $p$,
leaving exactly $\{r\}$. Every endpoint contains one of $p,q$.
We now either supply a fourth pair or read the two local degrees needed
by Lemma 4(3).

**The points $x_v$, $v\ne0$.** Choose the common full block whose spouse
edge is $\{0,v\}$. Its intersection with $W$ is

$$
\{p,q,x_0,y_0,x_v\}.
$$

The common full block contains a companion, whereas $W$ contains none,
so the two blocks are distinct. Both contain both roots and are therefore
different from every private endpoint, each of which contains only one
root. This adds a fourth pair without reusing an endpoint. The common
intersection of all endpoints is still $\{x_v\}$, so Lemma 4(2) applies.

**The points $y_v\in R$, $v\ne0$.** Choose a common full block whose
spouse edge contains the indices of both additions in $R$. Two different
indices determine that edge; if the additions are spouses, any edge
through their index suffices. For the resulting $C_m^\epsilon$,

$$
O\cap C_m^\epsilon=\{p,q,a_m\}\cup R,
$$

an intersection of size five containing $y_v$. The two blocks are
distinct because $O$ contains all three companions and the common full
block contains only one. Both contain both roots, so neither endpoint
belongs to the three private pairs. Lemma 4(2) again applies.

**The points $y_v\notin R$, $v\ne0$.** Such a point avoids both shared
completed traces: $A\cup R$ and $B\cup\{y_0\}$. In either rooted
link there are exactly three completed blocks. Every point lies in one
of the three spines, each contained in its completion, so belongs to at
least one completed block. The two avoided completed blocks are distinct.
The point must consequently belong to the third and to no other
completion. Together with the six full-core incidences, this gives

$$
d(py_v)=d(qy_v)=7.
$$

The own completed row is shared by Lemma 12, and the foreign completed
row was chosen to be shared, so this argument applies in both links.
The three private pairs described above now satisfy Lemma 4(3).

Thus the three companions and all six spouse points with nonzero index
are nonminimum. There are at most four minimum points, all in
$\{p,q,x_0,y_0\}$, contrary to Lemma 6. The argument uses the same
shared rows for multiplicities eight and nine. $\square$

### Proposition 15. Minimum pairs have multiplicity seven

If $|\mathcal C|\le29$, then every pair of distinct minimum points
$p,q$ satisfies

$$
d(pq)=7.
\tag{13}
$$

**Proof.** Lemma 8 gives the four possibilities seven, eight, nine and ten.
Lemma 9 excludes ten. For eight or nine, extract the two actual ordinary
rooted frames of Lemma 10. Lemma 11 aligns their common core, and Lemma 12
gives the two alternatives excluded by Lemmas 13 and 14. Only seven
remains. $\square$

## 4. Compatibility of four minimum points

The second compatibility argument concerns a graph $K_4$ whose vertices
are four minimum points. This is a new use of $K_4$: in Section 3 its
vertices were the four spouse indices of a rooted ordinary link.

### Lemma 16. Triple and preliminary quadruple multiplicities

Under $|\mathcal C|\le29$, every triple of distinct minimum points has
multiplicity three, and every four-set of minimum points has multiplicity
one or three.

**Proof.** For a triple $p,q,r$, Proposition 15 gives $d(pq)=d(pr)=7$.
Thus $q,r$ are degree-seven points of the minimum link $L_p$. Lemma 5(1)
and (1) give $d(pqr)=3$.

For a four-set $\{p,q,r,s\}$, the three points $q,r,s$ all have degree
seven in $L_p$. Coverage gives $d(pqrs)\ge1$. If that count is at least
two, Lemma 5(2) applied to $\{q,r,s\}$ in $L_p$ makes it three.
Otherwise it is one. $\square$

To exclude multiplicity three, we compare the four links using the
following twelve-point frame.

### Lemma 17. The local triplicate frame with prescribed roots

Let $L$ be a fifteen-block $(12,6,3)$ covering on a point set $W$.
Let $H=\{h_0,h_1,h_2\}$ consist of three distinct points satisfying

$$
d_L(h_r)=7,\qquad d_L(h_rh_s)=3\quad(r\ne s),\qquad d_L(H)=3.
$$

There is a partition of $W\setminus H$ into three **triads**
$T_0,T_1,T_2$, each of size three. The blocks containing $H$ are
$H\cup T_i$. For each root $h_r$, its other four blocks contain no
other point of $H$. Deleting $h_r$ from them gives three **marked traces**

$$
M_{r,i}=\{s_{r,i}\}\cup
 \bigcup_{j\ne i}(T_j\setminus\{s_{r,j}\}),\qquad i=0,1,2,
$$

and one **short trace** $U_r$. Here $s_{r,i}\in T_i$; the short trace
contains these three selections and two further points outside $H$.
Together the three common blocks and the twelve private blocks describe
all of $L$.

For each triad $T_i$, the selections $s_{0,i},s_{1,i},s_{2,i}$ are either
all different or all equal. If they all equal $x$, the two further points
in every short trace are exactly $T_i\setminus\{x\}$.

**Proof.** The construction follows the repeated-triple argument in the
proof of GPPT Lemma 5.8 [2](#references), using the marking and selection
results proved in the twelve-point component. We work with the given
roots $h_0,h_1,h_2$.

Fix $h_r$ and take its link inside $L$, denoted $J_r$. This is a
seven-block $(11,5,2)$ covering. The two other roots have degree three
in $J_r$, and their pair multiplicity is $d_L(H)=3$. They therefore
form a **couple**, a pair of multiplicity at least three in a minimum
eleven-point covering. Use this pair to mark the covering. The
[local Stanton rules](../12-6-3/proof.md#1-degrees-links-and-the-eleven-point-geometry)
give three full blocks containing the couple; removing it leaves three
disjoint triads of size three that partition the other nine points.
The other three full blocks of $J_r$ are the marked traces $M_{r,i}$
displayed above, and the short block is $U_r$, containing one selected
point from each triad and two additions.

Reinserting $h_r$ in the three blocks through the marking couple gives
exactly the three blocks containing $H$. Deleting $H$ identifies the
triads. Order them once and use that order in all three frames, as in the
[three-root frame construction](../12-6-3/proof.md#5-a-repeated-triple-the-three-root-frame).
Each pair of roots already occurs in all three common blocks, exhausting
its multiplicity three. The other four blocks of $L$ through $h_r$
therefore omit the other two roots; in particular, $U_r$ avoids all of $H$.

Inclusion–exclusion gives $3\cdot7-3\cdot3+3=15$ blocks in the union
of the three root stars. Since $L$ has fifteen blocks, these stars cover $L$.

For a fixed triad $T_i$, its **selection column** is the map
$r\mapsto s_{r,i}$ on the three roots. The proved triplicate-frame
selection theorem gives either three injective columns or a constant
column in some triad. If no column is constant, the
[twice-selected-point argument](../12-6-3/proof.md#53-a-point-is-selected-exactly-twice)
excludes the intermediate pattern $x,x,y$ with $x\ne y$, using the
two additions in each short trace and the minimum-link rules.
If a column is constant with selected point $x$, the
[common-selection argument](../12-6-3/proof.md#52-a-point-is-selected-by-all-three-roots)
forces the two points of $T_i\setminus\{x\}$ to be every short trace's
additions and makes the other two columns injective. Thus each column
is constant or injective. $\square$

For Lemmas 18–22, suppose $K\subseteq V$ has four points, each is minimum,
all six internal pair multiplicities are seven, and $d(K)=3$. These
hypotheses alone provide the frames below; the size bound
$|\mathcal C|\le29$ is added where it is needed.

### Lemma 18. Aligning the four local frames

There is a partition of $V\setminus K$ into triads $T_0,T_1,T_2$.
The three blocks containing $K$ are $K\cup T_i$. For each edge
$e=\{p,q\}\subset K$, the four blocks meeting $K$ in exactly $e$
have five-point traces

$$
R_{e,i}=\{s_{e,i}\}\cup
 \bigcup_{j\ne i}(T_j\setminus\{s_{e,j}\}),\qquad i=0,1,2,
\tag{14}
$$

and a short trace $U_e$ containing the three selected points
$s_{e,0},s_{e,1},s_{e,2}$ and two additions. Both the selections and
$U_e$ are independent of which endpoint's link describes $e$.

**Proof.** Fix $p\in K$. In $L_p$, the other three roots have degree
seven, pair multiplicity three by Lemma 5(1), and triple multiplicity
three because $d(K)=3$. Lemma 17 therefore applies with $H=K\setminus\{p\}$.
Reinserting $p$ turns its common blocks into blocks containing $K$, and
its private blocks at $q\in H$ into blocks meeting $K$ in exactly
$\{p,q\}$. This gives a local description at each of the four roots.

The triads are intrinsic to the three blocks containing $K$: they are
what remains after deleting $K$. Frames from the four roots can therefore
be aligned by reordering their triads. This reordering changes no point
or block. What still needs proof is that the two descriptions of each
edge give the same selections.

For an edge $e$, both endpoint frames describe exactly the family of
blocks with intersection $e$ with $K$. Deleting the two roots gives the
same four-trace family. In either description, $R_{e,i}$ meets $T_i$ in
the singleton $\{s_{e,i}\}$, and the other two marked traces meet it in
two points. If the short trace has singleton intersection with $T_i$,
that singleton is also $\{s_{e,i}\}$ because it contains the selection.
Thus every singleton intersection with $T_i$ identifies the same point,
and at least one such intersection exists. The actual four-trace family
therefore determines $s_{e,i}$, even if the descriptions initially assign
different roles to its rows.

Once the selections agree, (14) identifies the same three marked traces
in both descriptions. Each short trace contains all three selections,
whereas every marked trace omits the selections in its two other triads.
The short trace is consequently the unique remaining trace of the
four-trace family. This also makes $U_e$ independent of the endpoint.
$\square$

### Lemma 19. The four root stars contain exactly twenty-seven blocks

Let $\mathcal U=\bigcup_{p\in K}\operatorname{star}_{\mathcal C}(p)$.
It consists of the three common blocks $K\cup T_i$ and the six disjoint
four-block edge families of Lemma 18. Consequently

$$
|\mathcal U|=3+6\cdot4=27.
\tag{15}
$$

**Proof.** Lemma 17 describes the entire fifteen-block link at any root.
After lifting, that root's star consists of the three common blocks and
the four blocks on each of its three incident edges. Taking the union
over the four roots accounts for every block meeting $K$.

Different edge families have different exact intersections with $K$, so
are disjoint as families of blocks. The three common blocks contain all
of $K$ and belong to none of those families. Within each edge family, the
three marked traces are distinct, and the short trace differs from each
marked trace because it contains all three selections. Each edge family
therefore has four blocks, giving (15). $\square$

Each of the six edges of $K$ now carries a selection in each triad.
Lemma 17 constrains the selections on the three edges at every vertex;
these constraints give the following coloring dichotomy.

### Lemma 20. The three coordinate colorings

For each triad $T_i$, color the six edges of the graph on $K$ by
$s_{e,i}$. This coloring is either constant or a proper three-edge-coloring.
Here proper means that the three edges at every vertex have different
colors. In the proper case, opposite edges have the same color.

**Proof.** Apply Lemma 17 in each root's link, using the alignment of
Lemma 18. Every vertex is therefore monochromatic or rainbow.
That is, its incident edges have one common color or three different
colors. The palette consists of the three points of $T_i$.

Suppose one vertex is monochromatic with color $x$. If another vertex
is monochromatic, its common edge forces the same color $x$; the two
remaining vertices then each see two edges of color $x$ and must also
be monochromatic. If all three other vertices were rainbow, their
triangle would require a proper edge-coloring using only the two colors
different from $x$, which is impossible: three pairwise incident triangle
edges require three distinct colors. Thus a monochromatic vertex forces
all six edges to have one color.

If no vertex is monochromatic, every vertex is rainbow, giving a proper
three-edge-coloring. The colors on the three edges at one vertex exhaust
the palette. Each opposite edge must avoid the colors on the other two
of those edges at its endpoints, so it has the remaining color. $\square$

### Lemma 21. A constant coordinate is impossible

Under $|\mathcal C|\le29$, none of the three colorings of Lemma 20 is
constant.

**Proof.** Suppose every edge selects $x$ in $T_j$. Put
$A'=T_j\setminus\{x\}$. Applying Lemma 17 at either endpoint of an
edge, and using Lemma 18 to identify its trace, forces the two additions
of every short trace to be exactly $A'$.

Fix an outside point $y\notin A'$. In each edge family it occurs twice.
If it is selected in its own triad, it occurs in one marked trace and
the short trace. If it is unselected there, it occurs in two marked
traces and not in the short trace, since it is neither selected nor an
addition. Each outside point also occurs in exactly one common block.
Consequently each point of

$$
Y=V\setminus(K\cup A')
$$

has degree $1+6\cdot2=13$ within $\mathcal U$. Since $|K|=4$ and
$|A'|=2$, this is a set of seven points.

By (15), at most two blocks lie outside $\mathcal U$. Every point of $Y$
has global degree at least fifteen by Lemma 6, so needs at least two
further incidences. There must therefore be two residual blocks, and
both must contain every point of $Y$. Each residual block has size seven,
so each equals $Y$. This contradicts distinctness of blocks. $\square$

### Lemma 22. Proper coordinates exclude a fifth minimum point

If all three colorings of Lemma 20 are proper, no point outside $K$ can
be minimum. This assertion requires no pair-multiplicity assumptions
between that point and $K$.

**Proof.** Suppose $r\notin K$ is minimum. Reorder the triads so that
$r\in T_0$. Label the four roots $u_0,u_1,u_2,u_3$ and use their three
perfect matchings

$$
01/23,\qquad 02/13,\qquad 03/12.
$$

By Lemma 20, the two edges of any matching have the same selection in
each triad. Denote this selection triple by $s_m$. In $T_0$ the three
values $s_{m,0}$ are distinct, because the edges at $u_0$ have distinct
colors. At most one equals $r$; choose two different matchings whose
selections avoid $r$.

For either chosen matching $m$, let $e_m^0,e_m^1$ be its two opposite
edges, and define $R_{m,i}$ by (14) with the common selection triple
$s_m$. The four actual blocks

$$
e_m^0\cup R_{m,1},\quad e_m^1\cup R_{m,1},\quad
e_m^0\cup R_{m,2},\quad e_m^1\cup R_{m,2}
\tag{16}
$$

all contain $r$, because their traces contain
$T_0\setminus\{s_{m,0}\}$. Pair the two opposite-edge blocks with
trace label 1, and likewise those with trace label 2. Each pair intersects
in exactly its five-point trace: its root edges are disjoint and its
trace avoids $K$.

The two chosen matchings supply four pairs and eight distinct endpoints.
Different edges are distinguished by the block's intersection with $K$.
For the same edge, the two trace labels are distinguished by their
different singleton-triad profiles. Deleting $r$ preserves distinctness
and turns the four pairs into intersection-four pairs in $L_r$.

To exclude exceptional geometry, calculate the common intersection for
just one of the chosen matchings. Formula (14) gives

$$
R_{m,1}\cap R_{m,2}=T_0\setminus\{s_{m,0}\}.
\tag{17}
$$

Intersecting the first pair in (16) gives $R_{m,1}$, and intersecting
the second gives $R_{m,2}$. Equation (17) therefore gives the common
intersection of all four endpoints: a two-point set containing $r$.
After deleting $r$, this intersection has one point. The common
intersection of all eight link endpoints is a subset of that singleton,
so has size at most one.

Ordinary geometry cannot accommodate four such intersection-four pairs
with eight distinct endpoints: each pair requires a different completed
block, but there are only three.
Exceptional geometry would put its distinguished pair in every endpoint,
contradicting the common-intersection bound of one. Lemma 3 therefore
excludes the minimum link $L_r$. $\square$

### Proposition 23. A triplicate quadruple is impossible

Suppose $|\mathcal C|\le29$ and $K$ is a four-set of minimum points
whose six internal pair multiplicities are seven. Then $d(K)\ne3$.

**Proof.** If $d(K)=3$, Lemma 18 constructs the aligned four-point
system. Lemma 20 gives a constant or proper coloring in each triad.
Lemma 21 excludes every constant coordinate, so all three are proper.
Lemma 6 provides at least five minimum points, one of which lies outside
$K$. Lemma 22 excludes that point, a contradiction. $\square$

## 5. Proof of Theorem 1

Let $\mathcal C$ be any $(13,7,4)$ covering. If $|\mathcal C|\ge30$,
the lower bound already holds. Otherwise $|\mathcal C|\le29$.

By Lemma 6 choose a five-set $M$ of minimum points. Proposition 15 makes
every pair in $M$ have multiplicity seven. Lemma 16 makes every triple
have multiplicity three and every quadruple have multiplicity one or
three. Proposition 23 excludes three for each quadruple: its six pair
multiplicities are already known to be seven. Every quadruple therefore
has multiplicity one.

The hypotheses of Lemma 7 are now satisfied. It gives $|\mathcal C|\ge30$,
contradicting $|\mathcal C|\le29$. This proves the universal lower bound.

For existence, the retained [thirty-block construction](../../data/ljcr-30.json)
has thirty distinct seven-element blocks covering all $\binom{13}{4}=715$
four-subsets. The same explicit family is defined as `knownCover30` in
[Witness](../../lean/CoveringDesigns/C13_7_4/Witness.lean), where its
cardinality, uniformity and coverage are checked by the kernel.
Together these prove Theorem 1. $\square$

## References

1. R. G. Stanton. *Isomorphism Classes of Small Covering Designs with
   Block Size Five*. In C. J. Colbourn and R. Mathon (eds.),
   *Combinatorial Design Theory*, North-Holland Mathematics Studies 149,
   North-Holland, 1987, pp. 441–448.
   [Publisher record](https://www.sciencedirect.com/science/chapter/bookseries/pii/S0304020808729104),
   [DOI](https://doi.org/10.1016/S0304-0208(08)72910-4).

2. Daniel M. Gordon, Oren Patashnik, John Petro and Herbert Taylor.
   *Minimum (12,6,3) Covers*. *Ars Combinatoria* 40 (1995), pp. 161–177.
   [Publisher record](https://combinatorialpress.com/ars-articles/volume-040-ars-articles/minimum-12-6-3-covers/),
   [author-hosted copy](https://dmgordon.org/papers/c-12-6-3.pdf).

3. La Jolla Covering Repository. Entry for $C(13,7,4)$.
   [Repository entry](https://ljcr.dmgordon.org/cover/show_cover.php?k=7&t=4&v=13),
   [retained zero-based data](../../data/ljcr-30.json).

Stanton's eleven-point classification and GPPT's twelve-point structural
results are established results. The
[eleven-point source account](../11-5-2/proof.md#sources-and-contribution)
and [twelve-point source account](../12-6-3/proof.md#sources-and-contribution)
give attribution and explain the structural reconstructions formalized in
this project. Their use here is through proved Lean prerequisites.

## Appendix A. Lean correspondence and dependency checks

The public entry point is

```lean
import CoveringDesigns.C13_7_4
```

In Lean, `Family α` is `Finset (Finset α)`, so blocks are distinct.
`IsCover C 7 4` is the conjunction of seven-point uniformity and coverage
of every four-set. The public theorem
`CoveringDesigns.covering_number_13_7_4` states

```lean
(∃ C : Family (Fin 13), IsCover C 7 4 ∧ C.card = 30) ∧
(∀ C : Family (Fin 13), IsCover C 7 4 → 30 ≤ C.card)
```

The public theorem wraps
`CoveringDesigns.C13Structural.covering_number_13_7_4`. Its structural
lower bound, `CoveringDesigns.C13Structural.lower_bound_30`, works on any
finite point type with thirteen elements. The public theorem specializes
that lower bound to `Fin 13` and combines it with the explicit witness.
It has no unproved classification or compatibility hypotheses.

In the table, `C13` abbreviates `CoveringDesigns.C13Structural` and `GPPT`
abbreviates `CoveringDesigns.GPPTStructural`. Each declaration is named
with its namespace, and each group links to the source containing it.

| Statement | Lean declarations and supporting proof steps |
|---|---|
| Theorem 1 | `CoveringDesigns.covering_number_13_7_4` in [the public wrapper](../../lean/CoveringDesigns/C13_7_4/CoveringNumber.lean); `C13.lower_bound_30` and `C13.covering_number_13_7_4` in [the structural assembly](../../lean/CoveringDesigns/C13_7_4/Structural/CoveringNumber.lean); `CoveringDesigns.knownCover30_card`, `CoveringDesigns.knownCover30_uniform`, `CoveringDesigns.knownCover30_covers`, `CoveringDesigns.upper_bound_30` in [Witness](../../lean/CoveringDesigns/C13_7_4/Witness.lean) |
| Lemma 2 | `CoveringDesigns.link_card`, `CoveringDesigns.link_isCover`, `CoveringDesigns.degree_link` in [Links](../../lean/CoveringDesigns/Foundations/Links.lean); `CoveringDesigns.degree_sum_of_uniform` in [Basic](../../lean/CoveringDesigns/Foundations/Basic.lean); `C13.containmentCount_link` in [C13 Basic](../../lean/CoveringDesigns/C13_7_4/Structural/Basic.lean) |
| Lemma 3 | `C13.template_geometry`, `C13.figure6_geometry`, `C13.minimum_geometry`, `C13.minimum_degree_le_ten`, `C13.minimum_block_inter_le_four`, `C13.gppt_core_spine_inter`, `C13.gppt_core_inter` in [GPPTGeometry](../../lean/CoveringDesigns/C13_7_4/Structural/GPPTGeometry.lean); `C13.OrdinaryGeometry` and `C13.ExceptionalGeometry` in [GPPTGeometryHelpers](../../lean/CoveringDesigns/C13_7_4/Structural/GPPTGeometryHelpers.lean); `CoveringDesigns.figure1`, `CoveringDesigns.figure6` in [the fixed families](../../lean/CoveringDesigns/C12_6_3/Witnesses.lean); `GPPT.core`, `GPPT.spine`, `GPPT.core_card` in [Templates](../../lean/CoveringDesigns/C12_6_3/Structural/Templates.lean); `GPPT.core_degree` in [Separation](../../lean/CoveringDesigns/C12_6_3/Structural/Separation.lean) |
| Lemma 4 | `C13.minimum_global_block_inter_le_five`, `C13.FiveIntersectionMatching.not_minimum_four`, `C13.FiveIntersectionMatching.not_minimum_three` in [HighPairs](../../lean/CoveringDesigns/C13_7_4/Structural/HighPairs.lean); `C13.FiveIntersectionMatching.toLink`, `C13.FiveIntersectionMatching.deleted_common_empty` in [SwapObstruction](../../lean/CoveringDesigns/C13_7_4/Structural/SwapObstruction.lean); `C13.OrdinaryGeometry.matching_le_three`, `C13.OrdinaryGeometry.matching_le_two_of_degree_seven`, `C13.ExceptionalGeometry.matching_subset` in [GPPTGeometryHelpers](../../lean/CoveringDesigns/C13_7_4/Structural/GPPTGeometryHelpers.lean) |
| Lemma 5 | `GPPT.minimum_pair_degree_three` in [MinimumPairs](../../lean/CoveringDesigns/C12_6_3/Structural/MinimumPairs.lean); `GPPT.minimum_triple_not_two`, `GPPT.repeated_minimum_triple_count` in [Branching](../../lean/CoveringDesigns/C12_6_3/Structural/Branching.lean) |
| Lemma 6 | `C13.degree_lower`, `C13.five_minimum_points` in [C13 Basic](../../lean/CoveringDesigns/C13_7_4/Structural/Basic.lean); `GPPT.lower_bound_fifteen` in [Branching](../../lean/CoveringDesigns/C12_6_3/Structural/Branching.lean); `CoveringDesigns.minimum_points_bound` in [Basic](../../lean/CoveringDesigns/Foundations/Basic.lean) |
| Lemma 7 | `C13.five_point_bonferroni`, `C13.five_point_count` in [FivePointCount](../../lean/CoveringDesigns/C13_7_4/Structural/FivePointCount.lean); `GPPT.containment_moment`, `GPPT.point_incidence_moment` in [Moments](../../lean/CoveringDesigns/C12_6_3/Structural/Moments.lean) |
| Lemma 8 | `C13.pair_degree_lower`, `C13.minimum_pair_degree_upper`, `C13.minimum_pair_options`, `C13.ordinary_link_of_pair_eight_or_nine` in [PairBounds](../../lean/CoveringDesigns/C13_7_4/Structural/PairBounds.lean) |
| Lemma 9 | `C13.minimum_pair_ne_ten`, including propagation of the distinguished pair, in [TenPair](../../lean/CoveringDesigns/C13_7_4/Structural/TenPair.lean) |
| Lemma 10 | `C13.ordinary_pair_frames` in [PairCompatibility](../../lean/CoveringDesigns/C13_7_4/Structural/PairCompatibility.lean); `C13.half`, `C13.commonTrace`, `C13.privateTrace`, `C13.rootedCore_eq_figure1`, `C13.rootMove_core`, `C13.rootMove_spines`, `C13.ordinary_rooted_frame_of_isomorphic_template` in [RootedCore](../../lean/CoveringDesigns/C13_7_4/Structural/RootedCore.lean); `C13.OrdinaryRootedFrame.own_trace_shape`, `C13.OrdinaryRootedFrame.foreign_trace_shape`, `C13.OrdinaryRootedFrame.root_degree`, `C13.OrdinaryRootedFrame.overlapTraces_eq` in [RootedCoreHelpers](../../lean/CoveringDesigns/C13_7_4/Structural/RootedCoreHelpers.lean); `C13.OrdinaryRootedFrame.global_common_mem`, `C13.OrdinaryRootedFrame.global_private_mem` in [OverlapFrames](../../lean/CoveringDesigns/C13_7_4/Structural/OverlapFrames.lean) |
| Lemma 11 | `C13.IsSixCore`, `C13.commonTraceFamily_isSixCore`, `C13.own_short_not_mem_sixCore`, `C13.sixCore_replacement_rigidity`, `C13.sixCore_unique_in_overlap` in [CoreRecognition](../../lean/CoveringDesigns/C13_7_4/Structural/CoreRecognition.lean); its private fixed identities `C13.foreignTrace_same_incompatible` and `C13.replacedCore_separates_column`; `C13.traceTransition_mem_overlap`, `C13.traceTransition_preserves_core` in [OverlapAlignment](../../lean/CoveringDesigns/C13_7_4/Structural/OverlapAlignment.lean) |
| Lemma 12 | `C13.OrdinaryRootedFrame.own_trace_map_of_overlap_transport`, `C13.OrdinaryRootedFrame.shared_foreign_of_overlap_transport` in [SharedForeign](../../lean/CoveringDesigns/C13_7_4/Structural/SharedForeign.lean); `C13.core_preserving_map_companions`, `C13.core_preserving_spouseMate`, `C13.core_preserving_transverse`, `C13.core_preserving_shared_foreign` in [CoreAutomorphisms](../../lean/CoveringDesigns/C13_7_4/Structural/CoreAutomorphisms.lean); `C13.transverse_extension_unique_or_swap` in [CoreGluing](../../lean/CoveringDesigns/C13_7_4/Structural/CoreGluing.lean); `C13.privateFromCommon`, `C13.relabel_reconstructedPrivate`, `C13.reconstructedPrivate_common_transverse` in [PrivateReconstruction](../../lean/CoveringDesigns/C13_7_4/Structural/PrivateReconstruction.lean); `C13.private_alignment_of_shared_foreign` in [PrivateAlignment](../../lean/CoveringDesigns/C13_7_4/Structural/PrivateAlignment.lean) |
| Lemma 13 | `C13.identical_private_point_not_minimum`, `C13.identical_private_cores_impossible` in [HighPairs](../../lean/CoveringDesigns/C13_7_4/Structural/HighPairs.lean); `C13.privateTrace_covers_points`, `C13.identicalPrivateBlock_inter` in [SwapObstruction](../../lean/CoveringDesigns/C13_7_4/Structural/SwapObstruction.lean); `C13.identical_rows_of_private_alignment` in [AlignedRows](../../lean/CoveringDesigns/C13_7_4/Structural/AlignedRows.lean) |
| Lemma 14 | `C13.swapped_companion_not_minimum`, `C13.swapped_foreign_spouse_not_minimum`, `C13.swapped_addition_not_minimum`, `C13.swapped_degree_seven_spouse_not_minimum`, `C13.swapped_minimum_card_le_four`, `C13.spouse_swap_impossible` in [HighPairs](../../lean/CoveringDesigns/C13_7_4/Structural/HighPairs.lean); the private-pair intersections, endpoint injectivity, common-intersection identities and extra-pair identities in [SwapObstruction](../../lean/CoveringDesigns/C13_7_4/Structural/SwapObstruction.lean); `C13.normalization_common`, `C13.normalization_private`, `C13.normalization_conjugates_swap` in [PairNormalization](../../lean/CoveringDesigns/C13_7_4/Structural/PairNormalization.lean); `C13.aligned_swap_rows`, `C13.normalized_foreign_row` in [AlignedRows](../../lean/CoveringDesigns/C13_7_4/Structural/AlignedRows.lean); `C13.OrdinaryRootedFrame.degree_seven_avoids_two_completed` in [RootedDegrees](../../lean/CoveringDesigns/C13_7_4/Structural/RootedDegrees.lean); `C13.pair_degrees_seven_avoids_shared`, `C13.pair_degrees_seven_of_shared_shapes` in [AlignedDegrees](../../lean/CoveringDesigns/C13_7_4/Structural/AlignedDegrees.lean) |
| Proposition 15 | `C13.ordinary_pair_frames`, `C13.ordinary_high_pair_impossible`, `C13.minimum_pair_degree_seven` in [PairCompatibility](../../lean/CoveringDesigns/C13_7_4/Structural/PairCompatibility.lean) |
| Lemma 16 | `C13.minimum_triple_count`, `C13.quadruple_count_pos`, `C13.minimum_quad_count_one_or_three` in [C13 Basic](../../lean/CoveringDesigns/C13_7_4/Structural/Basic.lean) |
| Lemma 17 | `C13.exists_triplicate_frame_roots` in [FourPointFrames](../../lean/CoveringDesigns/C13_7_4/Structural/FourPointFrames.lean); `GPPT.TriplicateFrame`, `GPPT.three_minimum_stars_cover` in [Frames](../../lean/CoveringDesigns/C12_6_3/Structural/Frames.lean); `GPPT.TriplicateFrame.columns_injective_or_common` in [TriplicateClassification](../../lean/CoveringDesigns/C12_6_3/Structural/TriplicateClassification.lean); `GPPT.TriplicateFrame.additions_card`, `GPPT.TriplicateFrame.other_column_injective`, `GPPT.TriplicateFrame.additions_eq_common_mates` in [Triplicate](../../lean/CoveringDesigns/C12_6_3/Structural/Triplicate.lean) |
| Lemma 18 | `C13.FourPointVertex.ofTriplicate`, `C13.FourPointVertex.exists_aligned` in [FourPointFrames](../../lean/CoveringDesigns/C13_7_4/Structural/FourPointFrames.lean); `C13.exists_fourPointSystem`, `C13.FourPointSystem.private_traces`, `C13.FourPointSystem.selected_symm` in [FourPoint](../../lean/CoveringDesigns/C13_7_4/Structural/FourPoint.lean); `C13.short_ne_markedRow` in [FourPointCounting](../../lean/CoveringDesigns/C13_7_4/Structural/FourPointCounting.lean); `C13.markedRow_inter_self_triad`, `C13.markedRow_inter_other_triad`, `C13.selected_mem_of_trace_inter_singleton`, `C13.selected_eq_of_rows_eq` in [SelectedFrame](../../lean/CoveringDesigns/C13_7_4/Structural/SelectedFrame.lean) |
| Lemma 19 | `C13.short_ne_markedRow`, `C13.triad_markedRow_injective` in [FourPointCounting](../../lean/CoveringDesigns/C13_7_4/Structural/FourPointCounting.lean); `C13.FourPointSystem.rootStarUnion_decomposition`, `C13.FourPointSystem.rootStarUnion_card`, `C13.FourPointSystem.edge_card_four` in [FourPointConstant](../../lean/CoveringDesigns/C13_7_4/Structural/FourPointConstant.lean) |
| Lemma 20 | `C13.FourPointSystem.local_allowed`, `C13.FourPointSystem.indexed_column_dichotomy`, `C13.FourPointSystem.constant_column_global` in [FourPointColors](../../lean/CoveringDesigns/C13_7_4/Structural/FourPointColors.lean); `C13.K4.local_pattern_dichotomy_of_mem`, `C13.K4.proper_opposite_edges_of_mem` in [K4Coloring](../../lean/CoveringDesigns/C13_7_4/Structural/K4Coloring.lean) |
| Lemma 21 | `C13.FourPointSystem.short_additions_of_constant`, `C13.FourPointSystem.edge_degree_two_of_constant`, `C13.FourPointSystem.rootStarUnion_degree_thirteen`, `C13.constant_column_impossible` in [FourPointConstant](../../lean/CoveringDesigns/C13_7_4/Structural/FourPointConstant.lean); `C13.trace_family_degree_two`, `C13.common_rows_degree_one` in [FourPointCounting](../../lean/CoveringDesigns/C13_7_4/Structural/FourPointCounting.lean); `C13.residual_two_blocks_impossible` in [ResidualCount](../../lean/CoveringDesigns/C13_7_4/Structural/ResidualCount.lean) |
| Lemma 22 | `C13.two_indices_avoiding`, `C13.FourPointSystem.matchingSelected_injective`, `C13.FourPointSystem.canonical_marked_mem_of_proper`, `C13.FourPointSystem.proper_columns_impossible` in [FourPointProper](../../lean/CoveringDesigns/C13_7_4/Structural/FourPointProper.lean); `C13.markedRow_one_inter_two`, `C13.fourPointGlobalBlock_injective`, `C13.fourPointGlobalBlock_opposite_inter`, `C13.exists_four_point_matching`, `C13.four_pair_geometry_obstruction` in [FourPointMatching](../../lean/CoveringDesigns/C13_7_4/Structural/FourPointMatching.lean) |
| Proposition 23 | `C13.fifth_minimum_outside`, `C13.bad_quadruple_excluded` in [FourPointExclusion](../../lean/CoveringDesigns/C13_7_4/Structural/FourPointExclusion.lean) |
| Assembly of the lower bound | `C13.lower_bound_of_pair_quad_obstructions` in [FivePointCount](../../lean/CoveringDesigns/C13_7_4/Structural/FivePointCount.lean), instantiated with the proved pair and quadruple obstructions in [CoveringNumber](../../lean/CoveringDesigns/C13_7_4/Structural/CoveringNumber.lean) |

The formal proof constructs coordinates from the given covering, proves
the alignment between its links, and transports each required block back
into that covering.

### Dependency and axiom checks

The prerequisites are proved in the [eleven-point component](../11-5-2/README.md)
and the [twelve-point component](../12-6-3/README.md). The latter's separate
completion classification is described in its
[catalogue-completeness section](../12-6-3/proof.md#11-kernel-checked-catalogue-completeness).
Its catalogue data,
completion-verification modules and catalogue-specific
[Figure 6 bridge](../../lean/CoveringDesigns/C12_6_3/CatalogueBridge.lean)
are outside the thirteen-point proof's import closure.

The [canonical theorem audit](../../lean/audits/C13_7_4.lean) restates
Theorem 1 directly in terms of finite subsets, block sizes and coverage.
It requires exactly `propext`, `Classical.choice` and `Quot.sound` as the
public theorem's axiom dependencies. It also checks that the proof reaches
the proved structural GPPT and Stanton prerequisites, and excludes the
catalogue and completion-enumeration declarations from the theorem's
project dependencies. The audit also checks that the imported environment
contains none of the specified catalogue or completion-classification
declarations. Intermediate structural lemmas have
transitive `#guard_standard_axioms` checks. These allow any subset of the
three standard axioms and reject admissions or native assertions used in
a checked proof.

Fixed coordinate identities, the prescribed relabellings, the exceptional
family's geometry and the explicit witness are checked by ordinary kernel
reduction. The scalar check in Lemma 7 has six integer cases. The thirteen-point
argument enumerates no family of covering completions and uses no native
assertions or search certificates.

The Lean audits check the formal declarations. The table above records the
correspondence of this mathematical exposition with those declarations and
their proof steps; Markdown prose is not itself an input to Lean's kernel.

## Appendix B. Verification and retained artifacts

### Verify from source

Use Lean 4.34.1, specified in [lean-toolchain](../../lean/lean-toolchain),
and Mathlib v4.34.1 with its source dependencies. For a fresh source
distribution, follow the dependency setup instructions in the
[shared verification guide](../../technical-details.md). The
[Lake configuration](../../lean/lakefile.toml) and
[dependency manifest](../../lean/lake-manifest.json) specify the required
local dependency paths. With those dependencies installed, run these
commands from the repository root:

```sh
LEAN_NUM_THREADS=1 lake -d lean build +CoveringDesigns.C13_7_4:olean
lake -d lean env lean lean/audits/C13_7_4.lean
```

The first command builds the public thirteen-point module and its imported
prerequisites, generating Lean's compiled module files locally. Lake may
reuse up-to-date build artifacts; `LEAN_NUM_THREADS=1` limits concurrency
to reduce peak memory use. The second command runs the
[canonical theorem audit](../../lean/audits/C13_7_4.lean). It checks the
explicit covering-number statement, the exact foundational axioms and
the dependency conditions described in Appendix A. Successful completion
of both commands verifies the formal result in the supplied source tree.

The construction can also be checked independently using the supplied
[Python source](../../scripts/verify_cover.py):

```sh
python3 scripts/verify_cover.py data/ljcr-30.json
```

This uses only Python's standard library and checks block sizes,
distinctness and coverage for the thirty-block construction. The retained
[construction report](../../results/verify30.json) records thirty distinct
seven-element blocks, all 715 four-subsets covered and zero uncovered
subsets. It identifies the retained one-based input and its hash. The
transcriptions are linked below, together with an account of their retrieval.
These data checks supplement the kernel-checked witness and do not verify
the Lean lower-bound proof.

### Retained construction and provenance

The known thirty-block construction was transcribed on **11 October 2026**
from the [La Jolla Covering Repository](https://ljcr.dmgordon.org/cover/show_cover.php?k=7&t=4&v=13)
entry as returned by the web search index, which reported a crawl
approximately two months earlier. Direct retrieval from LJCR was
unsuccessful.

The [one-based transcription](../../data/ljcr-30-one-based.txt) and its
[zero-based conversion](../../data/ljcr-30.json) are preserved. The validity
of the construction is checked locally, independently of the availability
of the source website.

### Development and source-check dates

The contribution of the thirteen-point component is the structural
compatibility argument excluding every covering with at most 29 blocks,
together with its Lean formalization, completed locally on **12 October
2026**. The project's limited source check on **11 October 2026** found
externally reported bounds 28–30. That dated comparison does not establish
publication priority or external review.
