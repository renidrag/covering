# Lower bounds and exact values for $C(2k-c,k,3)$

**Rob Gardiner**

## Abstract

We prove $C(20,11,3)=12$ and quantitative bounds for $C(2k-c,k,3)$.
In particular, $C(2k-2,k,3)\ge13$ for $k\ge17$,
$C(2k-2,k,3)=14$ for $k\ge35$, $C(2k-3,k,3)=14$ for $k\ge59$, and
$C(2k-c,k,3)=14$ for $c\ge2, k\ge25c$. Small block budgets force many
low-degree points. Pairs occurring in exactly two blocks impose shared-block
constraints; combining these with incidence Gram rank gives the exclusions.
The twenty-point proof uses a boundary-rank argument, while the family bounds
use partitioning or Caro–Tuza selection, with centered support completion at
the two offset-two boundary cases. Known constructions supply attainment.
The conclusions and structural prerequisites are formalised in Lean. Historical
priority and optimality of the thresholds are not asserted.

## Introduction

An **ordinary $(v,k,t)$ covering** is a finite set $\mathcal C$ of distinct
$k$-element subsets (blocks) of a $v$-element point set such that every
$t$-element subset is contained in at least one block. Write $C(v,k,t)$
for its minimum possible block count. We use $t=3$ except in point links
and explicitly named auxiliary bounds. Repeated occurrences of a block
are not counted as different blocks in an ordinary family.
All covering parameters and block budgets are integers; whenever a triple
covering is considered, $3\le k\le v$. Polynomial differences and matrix
entries below use signed integer or real arithmetic.

### Background and contribution

The lower-bound arguments and Lean formalisation presented here were
developed by Rob Gardiner with AI assistance. The twelve-block witness,
affine construction methods and selection/rank ingredients retain their
historical attributions. The [source account](sources.md) separates these
antecedents, adaptations and priority limitations. In particular, qualitative
fixed-offset eventual exactness follows from classical mathematics; the
quantitative ranges below are the claims whose priority remains unresolved.

The common mechanism is a tension between incidence counts and incidence
rank. A small block budget forces many points to occur in only six blocks.
Pairs occurring in just two blocks force those **actual blocks** to cover
the ground set. Counting across their exclusive parts constrains how such
pairs can share supporting blocks. Once these configurations are excluded,
the incidence Gram matrix has nonnegative pair excess over three. Boundary
rank, a degree partition, or a quantitative selection theorem then forces
more independent rows than the block budget permits.

The twenty-point argument uses boundary rank to *force* a saturated pair
and shared-block counting to exclude it. The large-parameter arguments first
exclude saturation by capacity, then apply rank. These are different uses
of the same mechanism, not an induction from the numerical case.

### Proof outline

1. Incidence and point links give degree floors and many degree-six points
   in a small covering (§2).
2. A pair in exactly two blocks forces their union to be the whole ground
   set. Assigning saturated cross-pairs to their actual supporting blocks
   gives a capacity obstruction (§3).
3. For twenty points, boundary rank forces such a pair, and a sharper
   shared-block count excludes it (§§4–5). For the families, saturation is
   excluded first; partitioned rank or selection and strict rank then force
   more blocks (§§6–7). The two boundary cases use the small number of
   possible high-point supports and a shared-support capacity bound (§7.4).
4. A displayed twelve-block witness and weighted affine constructions give
   the upper bounds (§8). Section 10 assembles the main theorem.

The optional equality refinement in §9 is not a prerequisite for the
strongest thresholds. [Appendix A](#appendix-a-lean-correspondence-and-dependency-contracts)
records statement-by-statement Lean correspondence and dependency checks.
[Appendix B](#appendix-b-verification-and-supporting-modules) gives verification
commands and the included supporting modules.

## 1. Results and their dependencies

**Theorem 1.** The following statements hold, labelled (a)–(e) in order:

\[
\begin{aligned}
C(20,11,3)&=12,\\
13\le C(2k-2,k,3)&\le14 &&(k\ge17),\\
C(2k-2,k,3)&=14 &&(k\ge35),\\
C(2k-3,k,3)&=14 &&(k\ge59),\\
C(2k-c,k,3)&=14 &&(c\ge2,\ k\ge25c).
\end{aligned}
\]

Every equality includes an actual attaining ordinary family, on arbitrary
finite point labels. The interval at $k=17$ asserts no thirteen-block
construction. These are sufficient ranges, with no assertion of optimal
thresholds. In addition, every ordinary $(2k-2,k,3)$ covering satisfies

\[
(k+2)|\mathcal C|\ge14(k-1)\qquad(k\ge9). \tag{1}
\]

The twenty-point exclusion is an independent boundary-rank and shared-block
argument (§5). The uniform-offset exclusion uses partitioned strict rank
(§6); the sharper offset-two and offset-three exclusions use Caro–Tuza
selection, strict Gram rank and two-level incidence counting (§7), following
the structural argument of Horsley–Singh. Attainment comes from existing
constructions (§8), separately from all lower exclusions. Equality rigidity
explains a boundary phenomenon (§9), but is not needed for the strongest
thresholds.

**Dependency boundary.** We prove the specialised incidence, saturation,
boundary-rank, partition and selection lemmas used below, including a short
deletion proof of Caro–Tuza in the required multigraph form. The background
is finite counting and elementary finite-dimensional linear algebra:
rank-nullity, the rank bound for a matrix product, positive definiteness,
and the fact that a zero quadratic value for a positive semidefinite real
matrix implies membership in its kernel. The last follows by orthogonal
diagonalisation. The binary affine construction is explained in §8; the
twelve-block witness is displayed and checked by finite computation.
This is an explicit account relative to those standard foundations, not a
claim to reprove all background mathematics. No Mills theorem or historical
table is a proof premise. Section 7 states the exact graph assumptions;
no universal residual bound of three is assumed.

## 2. Incidence and low-degree points

Let $V$ have $v=2k-c$ points and let $\mathcal C$ be an ordinary
triple covering with $b=|\mathcal C|$. Define

\[
d(x)=|\{B\in\mathcal C:x\in B\}|,\qquad
\mu(x,y)=|\{B\in\mathcal C:x,y\in B\}|\quad(x\ne y).
\]

Both identities below require only uniformity, not coverage. Double counting gives

\[
\sum_xd(x)=kb,\qquad \sum_{y\ne x}\mu(x,y)=(k-1)d(x). \tag{2}
\]

Deleting $x$ from its containing blocks produces a pair covering on
$v-1$ points with block size $k-1$ and **exactly** $d(x)$ blocks:
reinserting $x$ proves injectivity. This exact count matters throughout.

### Lemma 2. Point and pair degree floors

For an ordinary triple covering on $v=2k-c$ points,
if $c\ge2, c<k$, every distinct pair has multiplicity at least two.
If $c\ge2, k\ge8c-7$, every point has degree at least six. The latter
range implies $c<k$ and all needed link parameters are admissible.

*Proof.* For the first assertion, coverage supplies a block through each pair
(extend it to a triple). If there were only one such block, it could not
contain all its $v-2>k-2$ possible third points. For the second, consider a point link,
with $n=2k-c-1$ points and blocks of size $k-1$, and suppose it has at
most five blocks. Each point of the link has degree at least two, since one
containing $(k-1)$-block cannot cover its $n-1>k-2$ companions. If all
degrees were at least three, then

\[
3n-5(k-1)=k-3c+2>0
\]

would contradict incidence counting. A degree-two point therefore lies in
two link blocks whose union is the whole link. Their intersection has size
$c-1$, and their two exclusive parts have size $k-c$. The remaining
at most three blocks must cover all $(k-c)^2$ cross-pairs. Put

\[
F(a)=\lfloor a^2/4\rfloor.
\]

A block with disjoint traces of sizes $u,w$, with $u+w\le a$, covers
at most $uw\le F(a)$ cross-pairs: $4uw\le(u+w)^2\le a^2$, and
the product is integral. The two blocks through the degree-two point
contain no cross-pair. Thus $(k-c)^2\le3F(k-1)$.
This is impossible: writing $k=8(c-1)+1+h$, $h\ge0$, gives

\[
4(k-c)^2-3(k-1)^2=4(c-1)^2+8(c-1)h+h^2>0.
\]

In particular the floor six holds at offset two for $k\ge9$. Whenever
it holds, let $L=\{x:d(x)=6\}$ and $\ell=|L|$. All other degrees are
at least seven, so

\[
7v\le kb+\ell. \tag{3}
\]

A small block budget consequently forces many degree-six incidence rows.

## 3. Saturation, actual blocks and cross capacity

A pair is **saturated** if its multiplicity is two. For such a pair $p,q$,
its two actual blocks
$B,D$ cover $V$: apply triple coverage to the pair and each other point.
Consequently

\[
B\cup D=V,\quad |B\cap D|=c,\quad
X=B\setminus D,\ Y=D\setminus B,\quad |X|=|Y|=k-c. \tag{4}
\]

For $c>2$, $X\cup Y$ is the complement of the **entire** intersection,
not merely of the chosen endpoints $p,q$. The converse of (4) is not
asserted: two blocks intersecting in $c$ points need not determine a
saturated pair.

Partition the other actual blocks into $P$ containing only $p$, $Q$
containing only $q$, and $N$ containing neither. Write their cardinalities
as $u,w,n$. Then

\[
u+w+n=b-2,\qquad d(p)=u+2,\quad d(q)=w+2. \tag{5}
\]

Let $T\subseteq X\times Y$ consist of saturated cross-pairs, and put
$s=|T|$. Each $(x,y)\in T$ has two actual supporting blocks $U,W$.
They are neither $B$ nor $D$, their union is $V$, and neither can
contain both $p,q$. Thus there is a unique orientation with $U\in P$,
$W\in Q$. This is one simultaneous assignment $T\longrightarrow P\times Q$.

### Lemma 3. Bounded fibres of the actual-block assignment

For the assignment just defined, each fibre has at most $F(c)$ elements; hence

\[
s\le F(c)uw. \tag{6}
\]

*Proof.* For a nonempty fibre above $(U,W)$, saturation gives $|U\cap W|=c$.
The fibre lies in
$(X\cap U\cap W)\times(Y\cap U\cap W)$, whose two trace sizes sum to
at most $c$. Their product is at most $F(c)$. An unused image has an
empty fibre, so no intersection hypothesis on arbitrary $P\times Q$
pairs is needed. At $c=2$, $F(c)=1$, recovering injectivity; at general
offset injectivity is not justified. Points of $U\cap W$ outside $X\cup Y$
only reduce the available capacity.

### Lemma 4. Saturated-pair capacity

Assume $c\ge2, c<k$, triple coverage,
uniform block size $k$, and a saturated pair. With $r=\lfloor k/2\rfloor$,

\[
3(k-c)^2+r(u+w)\le(b-2)F(k)+F(c)uw. \tag{7}
\]

*Proof.* The pair floor two implies that the cross multiplicity sum $S$
is at least $3(k-c)^2-s$. Count $S$ through the actual blocks. Blocks
in $P\cup Q$ have trace sum at most $k-1$, while those in $N$ have
trace sum at most $k$; $B,D$ contribute zero. Since
$F(k)-F(k-1)=r$, (5) and (6) give (7). This lemma has no small-budget
or point-degree premise. The subtraction $b-2$ is legitimate because
the two distinct supporting blocks exist.

Here are the precise exclusions needed later. Under the point floor six,
$u,w\ge4$. At offset two, when $r\ge b-6$, (5) also gives $u,w\le r$, and

\[
uw-r(u+w)\le16-8r.
\]

Subtracting the right side yields
$(u-4)(w-r)+(4-r)(w-4)\le0$. Substitution in (7) excludes:

| Offset | Assumed budget | Range excluding saturation | Positive gap, $k=2r$ / $k=2r+1$ |
|---|---:|---:|---|
| 2 | $b\le12$ | $k\ge17$ | $2r^2-16r-4$ / $2r^2-14r-13$ |
| 2 | $b\le13$ | $k\ge33$ | $r^2-16r-4$ / $r^2-15r-13$ |
| 3 | $b\le13$ | $k\ge57$ | $r^2-28r-5$ / $r^2-27r-20$ |

For the first row the minimum permitted $r$ values are 9 and 8 in the
even and odd cases, giving gaps 14 and 3. For the second they are 17 and
16, giving gaps 13 and 3; for the third, 29 and 28, giving gaps 24 and 8.
Each quadratic increases thereafter. For the
third row, $F(3)=2, 4\le u,w\le7, r\ge28$, and the needed reduction is

\[
2uw-r(u+w)\le32-8r,
\]

because its difference from the right side is
$(u-4)(2w-r)+(w-4)(8-r)\le0$.

There is also a uniform exclusion requiring no point floor. If $b\le13$,
then $u+w\le11$ and $uw\le30$. Dropping $r(u+w)\ge0$ in (7) and
using $4F(a)\le a^2$ gives

\[
k^2-24kc-18c^2\le0.
\]

For $k=25c+h$, the left side is $7c^2+26ch+h^2>0$.
Thus saturation is impossible for $c\ge2, k\ge25c, b\le13$.

## 4. The Gram matrix and a boundary-rank lemma

An incidence matrix has points as rows, blocks as columns, and entry
$R_{xB}=1$ if $x\in B$, zero otherwise. Its **Gram matrix** is
$RR^{\mathsf T}$: diagonal entries are point degrees and off-diagonal
entries are pair multiplicities. A real symmetric matrix is **positive
semidefinite** (PSD) when its quadratic form is nonnegative on every vector;
it is positive definite when that form is positive on every nonzero vector.

Suppose the actual pair multiplicities are at least three. On $L$, let
$R$ be the restricted incidence matrix, with the $b$ actual blocks
as columns, and let $E_{xx}=0, E_{xy}=\mu(x,y)-3$ for $x\ne y$.
Then $E$ is symmetric and nonnegative, and

\[
RR^{\mathsf T}=3I+E+3J. \tag{8}
\]

Here $I$ is the identity matrix and $J$ the all-ones matrix.
The full excess row at a degree-six point sums to
$6(k-1)-3(v-1)=3(c-1)$; restriction to $L$ cannot increase it.

For a symmetric nonnegative matrix $E$ with zero diagonal, its **support
graph** has an edge between distinct vertices $x,y$ exactly when $E_{xy}>0$.
Zero diagonal means **loopless**. The edge weight is $E_{xy}$; weighted degree
is its row sum. A path follows edges, and a connected component is a maximal
set joined by paths. Restricting to a vertex subset gives the **induced**
graph, with degrees recomputed there. With natural weights this is also a
multigraph: the weight counts parallel edges. We use **support** of an
incidence row for the set of actual blocks containing that point.

### Lemma 5. Rank at the boundary of diagonal dominance

Let $R$ be any real $\ell$-by-$b$ matrix.
Suppose $\rho>0$, $E$ is symmetric, entrywise nonnegative and loopless,
$\delta_x\ge0$, $\sum_yE_{xy}+\delta_x=\rho$, $P$ is positive
semidefinite, and $RR^{\mathsf T}=\rho I+E+P$. If
$Z=\{x:\delta_x=0\}$, then

\[
2\ell\le2b+|Z|,\qquad \ell\le2b. \tag{9}
\]

*Proof.* Set $A=\rho I+E$. The identity

\[
z^{\mathsf T}Az=\sum_x\delta_xz_x^2+
\sum_{x<y}E_{xy}(z_x+z_y)^2 \tag{10}
\]

proves positivity, including at equality in diagonal dominance; any ordering
of the rows can be used for $x<y$. A kernel
vector vanishes at positive deficits and alternates along every positive
edge. One coordinate determines it on each connected component of the
support graph. Components meeting a positive deficit contribute nothing;
each remaining component has at least two vertices, since its row sum is
$\rho>0$. Evaluation at one representative of each such component is
injective on the kernel. Thus $2\dim\ker A\le|Z|$.
Positivity also gives $\ker(A+P)\subseteq\ker A$. Rank-nullity and the
$b$-column factorisation prove (9). No rank monotonicity under arbitrary
matrix addition is being used. Empty row sets cause no exception.

At $c=2$, the excess matrix $E$ in (8) has row sums at most three.
Take $\delta_x=3-\sum_yE_{xy}\ge0$ and $P=3J$ in the boundary lemma.
Equations (3) and (9) give
$14(k-1)\le(k+2)b$ **conditionally** on the actual pair floor three.

## 5. The independent twenty-point exclusion

### Proposition 6. The twenty-point lower bound

Every ordinary $(20,11,3)$ covering has at least twelve blocks.

*Proof.* For $v=20,k=11$, the elementary link proof in §2 specialises to a
$(19,10,2)$ covering. At most five link blocks would either give
$3\cdot19\le5\cdot10$, or leave two nine-sets whose 81 cross-pairs
are covered by at most three blocks of capacity 25. Both are impossible.
Thus $d(x)\ge6$ and $120\le11b$, excluding $b\le10$. This local
argument is also proved directly in the independent Lean component.
If $b=11$, exactly one point $h$ has degree seven and the
other nineteen have degree six.

Suppose first there is no saturated pair. All pair multiplicities are then
at least three. In (8), set $\delta_x=\mu(x,h)-3$ for $x\ne h$.
Equation (2) gives

\[
\sum_yE_{xy}=3-\delta_x,\qquad
\sum_{x\ne h}\delta_x=70-3\cdot19=13.
\]

Since $0\le\delta_x\le3$, at least five deficits are positive, so
$|Z|\le14$. The boundary lemma gives rank at least $19-7=12$, impossible
with eleven columns. A saturated pair therefore exists.

Orient it as $p,q$ with $d(q)=6$. In §3, $X,Y$ are nine-sets,
$|Q|=4, u=|P|\in\{4,5\}, |N|=5-u$. With $s$ saturated cross-pairs,

\[
243-s\le S\le25(u+4)+30(5-u)=250-5u,
\qquad s\ge5u-7. \tag{11}
\]

Injectivity gives $s\le4u$, but the shared actual blocks give more.
If $q$ had another saturated partner $z\in X$, its block besides $B$
would be forced by union and intersection to equal $Y\cup\{q,z\}$.
This actual $Q$-block has cross product nine instead of the allowed 25.
The loss sixteen in (11) gives $s\ge5u+9>4u$, a contradiction. The
case $z\in Y$ is symmetric. Thus $\mu(q,z)\ge3$ for every residual point.
Exactly one of $B,D$ contains such a point, so it belongs to at least two
of the **same four** $Q$-blocks.

For a fixed $A\in P$, its ten residual points therefore give
$\sum_{W\in Q}|A\cap W|\ge20$. If $r_A$ is the number of distinct $Q$-blocks paired with $A$ by the
assignment, injectivity identifies this with the number of cross-pairs
assigned to $A$. Each such intersection has size two; any other intersection has
size at most ten because $W$ omits $p$. Hence

\[
20\le2r_A+10(4-r_A),\qquad r_A\le2.
\]

The integer conclusion is essential. Counting the same injective assignment
by its first coordinate gives $s\le2u$, contradicting $s\ge5u-7$ for
$u=4,5$. This excludes eleven blocks. The existing twelve-block witness
in §8 completes $C(20,11,3)=12$, without any large-$k$ theorem.

## 6. Partitioned strict rank and the uniform offset

We first record the strict rank fact used here and in §7. Suppose a real
matrix $R$ has Gram decomposition
$RR^{\mathsf T}=\operatorname{diag}(a_x)+E+P$, where $E$ is symmetric,
entrywise nonnegative and has zero diagonal, and $P$ is positive
semidefinite. If $\sum_y E_{xy}<a_x$ for every row, then the number
of rows is at most the number of columns. Indeed, for any vector $z$,
the inequality $2z_xz_y\ge-z_x^2-z_y^2$ gives

\[
z^{\mathsf T}(\operatorname{diag}(a_x)+E)z
\ge\sum_x\left(a_x-\sum_yE_{xy}\right)z_x^2.
\]

The right side is positive for nonzero $z$. Adding $P$ preserves positive
definiteness, so the Gram matrix has full row rank. Empty row sets are
allowed. This is the unit-weight case of the library's weighted strict
Gram-rank theorem; weak dominance alone would not suffice.

### Lemma 7. Partitioned strict rank

Let $I,J$ be finite sets, $R\in\mathbb R^{I\times J}$,
$q\ge1$ an integer, $\rho>0$, and $w:I\times I\to\mathbb Z$ symmetric,
nonnegative and zero on the diagonal. Assume an integer $D$ satisfies
$\sum_yw(x,y)\le D<q\rho$, that $P$ is positive semidefinite, and

\[
RR^{\mathsf T}=\rho I+w+P.
\]

Then $|I|\le q|J|$. Empty sets and empty parts are allowed.

*Proof.* Choose a labelling of the vertices by $q$ colours minimising the sum of
weights of monochromatic unordered edges. Moving one vertex cannot lower
this finite minimum, so its weight into its own class is at most its weight
into any class. Consequently $q$ times its internal weight is at most its
total weight, hence its internal weight is strictly less than $\rho$.
On a colour class the restricted remainder is positive semidefinite
(extend a vector by zero to check its quadratic form). The strict rank
fact just proved makes that class have at most $|J|$ rows.
One may sum class cardinalities; equivalently, as in Lean, choose a largest
class. Ranks of overlapping column spaces are never added. The strict
inequality $D<q\rho$, not weak dominance, is the decisive hypothesis.

In (8) use $q=c, \rho=3, D=3(c-1)$. The excess entries are integers,
so the lemma gives $\ell\le cb$, and (3) becomes

\[
7(2k-c)\le(k+c)b. \tag{12}
\]

Now let $c\ge2, k\ge25c$ and suppose $b\le13$. The degree-floor
lemma applies; the uniform saturation exclusion in §3 upgrades actual
pair multiplicities from two to three. Equation (12) implies $k\le20c$,
a contradiction. Thus $b\ge14$. This proof does not use the
Horsley–Singh adapter.

## 7. Actual multiplicities and the sharper thresholds

### Proposition 8. The bound from actual point and pair floors

The following structural bound applies even to uniform families not assumed
to cover triples. Suppose $v+c=2k, c\ge2, c<k, k>6$, and the actual
point and pair multiplicities are at least six and three. Put $d=3(c-1)$.
Then

\[
b\ge\left\lceil Q_c(k)\right\rceil,\qquad
Q_c(k)=\frac{(2k-c)(14k+2d-12)}{2k^2+(d-1)k+d(d+1)}. \tag{13}
\]

### 7.1. The selection theorem and its proof

**Lemma 9 (Caro–Tuza selection in the required form).** Let $W$ be a finite
vertex set, $a$ a positive integer, and $w:W\times W\to\mathbb N$
symmetric with $w(x,x)=0$. Thus the graph is undirected and loopless;
zero weights are nonedges and positive weights count parallel edges.
Put $D_x=\sum_{y\in W}w(x,y)$. There is a subset $S\subseteq W$ such that

\[
\sum_{y\in S}w(x,y)<a\quad(x\in S),\qquad
|S|\ge\left\lceil\sum_{x\in W} f_a(D_x)\right\rceil,
\]

where, for nonnegative real $t$,

\[
f_a(t)=\begin{cases}1-t/(2a)&0\le t\le a,\\
(a+1)/(2(t+1))&t\ge a.
\end{cases}
\]

The formulas agree at $t=a$. Empty graphs, empty selections and arbitrary
parallel-edge multiplicities are allowed; no regularity or simplicity
assumption is made. This is [Horsley–Singh, Theorem 12](sources.md#selection-and-rank),
credited there to Caro and Tuza. The following proof follows Horsley's
maximum-degree deletion argument and the existing verified implementation.

*Proof.* For nonnegative $t$, $0\le f_a(t)\le1$. The scalar step is

\[
f_a(X-y)-f_a(X)\ge\frac{y(a+1)}{2X(X+1)}
\quad(X\ge a,\ 1\le y\le X). \tag{S}
\]

If $X-y\ge a$, the left side equals
$y(a+1)/(2(X+1)(X-y+1))$, and $X-y+1\le X$ proves (S).
If $X-y\le a$, subtract the right side of (S) from the left and
multiply by the positive denominator $2aX(X+1)$. The result is

\[
(X+1)(X-a)(a+y-X)+a(y-1)(X-a)\ge0.
\]

Now delete a vertex $z$ of maximum degree $D\ge a$. For a remaining
vertex $x$, write $X=D_x\le D$ and $y=w(x,z)$, so $0\le y\le X$.
If $y=0$, its potential contribution does not change. If $X<a$, the
gain is $y/(2a)$, at least $y(a+1)/(2D(D+1))$ because
$D(D+1)\ge a(a+1)$. If $X\ge a$ and $y>0$, integrality gives
$y\ge1$; (S) and $X\le D$ give the same lower estimate.
Symmetry and the zero diagonal imply $\sum_{x\ne z}w(x,z)=D$.
The total gain is therefore at least
$D(a+1)/(2D(D+1))=f_a(D)$, exactly the contribution removed with $z$.
Thus deletion cannot decrease $\sum_x f_a(D_x)$.

Repeat while some current degree is at least $a$, always using degrees
in the **current induced graph**. Each deletion reduces the finite vertex
set. In the final set $S$, all induced degrees are below $a$ and its
potential is at most $|S|$, while at least the original potential.
Rounding gives the theorem. No assumption equates an induced degree
with its original value.

The library also verifies Horsley's extension to symmetric nonnegative
real weights with zero diagonal. Its additional hypothesis is precise:
a positive edge between two vertices whose degrees
are at least $a$ must have weight at least one. Nonedges between such
vertices remain allowed. This hypothesis is inherited on restriction,
since degrees only decrease; the same proof works. We need only the
natural-weight statement above, which satisfies it automatically.

### 7.2. Selection, strict rank and incidence counting

*Proof of Proposition 8.* Return to the uniform family satisfying the actual floors in (13).
Use the full excess graph with weights $\mu(x,y)-3$ off the diagonal
and zero on the diagonal. These are nonnegative integers. Its degree at $x$
is $(d(x)-6)(k-1)+d$, by (2) and $v=2k-c$; the scalar $d=3(c-1)$
is the defect, distinct from the point degree $d(x)$.
Set $a=3$. On the selected set its incidence Gram matrix is
$\operatorname{diag}(d(x)-3)+E+3J$. Since $d(x)-3\ge3$ and internal
excess is **strictly** below three, the strict rank lemma in §6 bounds
the selected size by $b$. Hence the potential is at most $b$.
If $n_0,n_1$ count points of degrees six and seven,
nonnegativity of all other selection weights gives

\[
An_0+Hn_1\le b,\qquad A=\frac2{d+1},\quad H=\frac2{d+k}. \tag{14}
\]

Neither low class nor the selected set has to be nonempty. Let
$e=kb-6v\ge0$; higher-degree points contribute at least two to $e$.
When $k\ge d+2$, $A\ge2H\ge0$, and these counts imply
$An_0+Hn_1\ge Av-(A-H)e$. To see this pointwise, put
$t=d(x)-6\ge0$ and give the point weight $A,H,0$ according as
$t=0,t=1,t\ge2$. That weight is at least $A-(A-H)t$:
there is equality for $t=0,1$, and for $t\ge2$ the right side is
at most $2H-A\le0$. Sum over points and use $\sum t=e$.
Rearranging (14) gives

\[
b\ge\frac{v(6(A-H)+A)}{1+k(A-H)}=Q_c(k).
\]

Here $A-H\ge0$ because $k>6$, so the denominator $1+k(A-H)$ is positive.
When $k\le d+1$, incidence alone gives $b\ge6v/k\ge Q_c(k)$: after
positive-denominator multiplication the second inequality reduces to
$kA\le6$, and here $kA\le2$.
Thus (13) needs no additional $k\ge d+2$ premise. Its displayed denominator
is positive because $d\ge3$ and $k>6$, and taking
the ceiling is justified because $b$ is an integer. This is the
actual-multiplicity adaptation of the published selection/rank proof;
the published covering wrapper has additional universal residual-seed
hypotheses, which are not silently assumed here. No triple coverage was
used in this derivation: uniformity and the two actual multiplicity floors
are the exact family premises.

### 7.3. The numerical conclusions

**Corollary 10.** Every ordinary $(2k-2,k,3)$ covering has at least
thirteen blocks for $k\ge18$, and at least fourteen for $k\ge36$.
Every ordinary $(2k-3,k,3)$ covering has at least fourteen blocks for $k\ge59$.

*Proof.* At the required offsets the strict comparisons are

\[
\begin{aligned}
Q_2(k)-12&=\frac{2(k^2-16k-33)}{k^2+k+6}>0 &&(k\ge18),\\
Q_2(k)-13&=\frac{k^2-33k-72}{k^2+k+6}>0 &&(k\ge36),\\
Q_3(k)-13&=\frac{2k^2-107k-546}{2k^2+5k+42}>0 &&(k\ge59).
\end{aligned}
\]

Writing $k=18+h,36+h,59+h$, respectively, the numerator polynomials
inside the first factor two, and in the other two lines, become
$3+20h+h^2, 36+39h+h^2, 103+129h+2h^2$. This proves each entire
range, with strictness before integer rounding.

For the first line assume $b\le12$; for the others assume $b\le13$.
Section 3 excludes saturation at $k\ge17,33,57$, respectively. Together
with §2 this supplies the actual floors for that hypothetical small family,
and (13) contradicts its budget. These arguments prove these three selection-based
exclusions. They do **not** say every covering has pair floor three.
Indeed, throughout these ranges the universal residual one-cover number
$C(2k-c-2,k-2,1)=2$: its argument is strictly between one and two before
rounding, or equals two at $c=2$. Indeed, for $m<n\le2m$, one $m$-set cannot
cover all $n$ points, while two can: take one $m$-set and extend its
complement to another $m$-set. Here $m=k-2$ and $n=2k-c-2$.
Using three as that universal seed would
be false.

For completeness, (1) is unconditional. Here is a short consequence of
the bounds just proved, together with incidence. Since $kb\ge12(k-1)$,
integrality gives $b\ge11$ for $9\le k\le12$ and $b\ge12$ for
$13\le k\le17$. Section 7 gives $b\ge13$ for $18\le k\le35$
and $b\ge14$ for $k\ge36$. In these four ranges, respectively,
the difference $(k+2)b-14(k-1)$ is at least
$36-3k$, $38-2k$, $40-k$ and $42$, all nonnegative.
The original Lean declaration proves (1) independently by boundary rank
and saturation, using block floors 11, 12, 13 and 14 on the respective
ranges $[9,12]$, $[13,19]$, $[20,40]$ and $[41,\infty)$.
This rearranged exposition introduces no circular dependency: the
saturation lemmas used in §7.3 do not use (1).

### 7.4. Completing the two boundary cases

**Proposition 10a.** Every ordinary $(32,17,3)$ covering has at least
thirteen blocks, and every ordinary $(68,35,3)$ covering has at least
fourteen blocks. Consequently the two offset-two thresholds in Corollary 10
improve to $k\ge17$ and $k\ge35$.

*Proof.* Suppose the respective block counts are at most twelve and thirteen.
Inequality (1) and Corollary 10, respectively, force the counts to be exactly
$b=12$ and $b=13$. The saturation exclusions in §3 give pair multiplicity
at least three; §2 gives point degree at least six. We use the same argument
for both $(v,k,b)=(32,17,12)$ and $(68,35,13)$.

Let $L$ be the degree-six points, $\ell=|L|$, and $R$ their binary incidence
matrix with the $b$ actual blocks as columns. Put $E_{xy}=\mu(x,y)-3$ for
distinct low points, $E_{xx}=0$, and
$\delta_x=\sum_{y\notin L}(\mu(x,y)-3)$. Counting the companions of a low
point gives
\[
 RR^{\mathsf T}=3I+E+3J,\qquad \sum_yE_{xy}+\delta_x=3.
\]
In particular $0\le\delta_x\le3$. If $p$ counts the positive deficits,
the nullity inequality in Lemma 5, before replacing rank by the number of
columns, gives
\[
 \ell+p\le2\operatorname{rank}R. \tag{15}
\]

Centering preserves this rank. Indeed, set $A=3I+E$. The signless identity
in Lemma 5 shows that $z\in\ker A$ satisfies $\delta_xz_x=0$. Summing
$Az=0$ and using the row sums of $E$ then gives $6\sum_xz_x=0$.
Thus $\ker A\subseteq\mathbf1^\perp$. Since $A$ is positive semidefinite,
$\ker(A+\gamma J)=\ker A$ for every $\gamma\ge0$: a zero quadratic form
for a sum of two positive semidefinite matrices belongs to both kernels.
For $T=R-(6/b)J$ we have
\[
 TT^{\mathsf T}=A+(3-36/b)J,\qquad T\mathbf1=0.
\]
Here $b\ge12$, including equality, so $\operatorname{rank}T=
\operatorname{rank}R$. Write $u=b-\operatorname{rank}R$; then $u\ge1$.
Incidence gives $\ell\ge7v-kb$. Together with (15), this implies
$1\le u\le2$ in both cases.

Let $F$ consist of the degree-seven points having multiplicity exactly three
with every low point. Put $\eta=\sum_{y\notin L}(d(y)-7)$, so
$kb=7v-\ell+\eta$. At most $\eta$ high points have degree above seven,
and at most $3p$ high points have positive excess with a low point, because
the sum of all low-to-high excess is $\sum_x\delta_x\le3p$.
Consequently
\[
 |F|\ge v-\ell-\eta-3p
      \ge15v-2kb-6b+6u. \tag{16}
\]
The last inequality uses (15) and $\ell\ge7v-kb$. Thus $|F|\ge6u$ at
$(32,17,12)$, and $|F|\ge32+6u\ge38$ at $(68,35,13)$.

For $y\in F$, its actual binary block-support vector $w_y$ satisfies
$Tw_y=(3-42/b)\mathbf1$ and $\sum_i(w_y)_i=7$. Differences of two such
vectors lie in $\ker T\cap\mathbf1^\perp$, of dimension $u-1$: the
nonzero vector $\mathbf1$ lies in $\ker T$ and has nonzero coordinate sum.
When $u=1$ there is at most one support. When $u=2$ there are at most two,
since an affine line meets $\{0,1\}^b$ in at most two points (a varying
coordinate determines its line parameter and can take only two values).
These are counts of supports; all points sharing a support are retained.

Finally, a nonempty class of $g$ points with identical support of degree
$h$ in a uniform $k$-family with pair multiplicity at least $\lambda$ obeys
\[
 \lambda(v-g)\le h(k-g). \tag{17}
\]
Choose a representative. Its $h$ blocks contain the entire class, and every
outside point must occur in at least $\lambda$ of those blocks. Counting
outside incidences proves (17); the argument also permits indexed repeated
blocks. With $h=7,\lambda=3$, it gives $g\le5$ on 32 points and $g\le10$
on 68 points. Hence the first case has $|F|\le5u<6u$, and the second has
$|F|\le20<38$. Both contradict (16). Corollary 10 handles all larger $k$;
Proposition 11 supplies the unchanged upper bound fourteen. $\square$

## 8. Attainment: a known witness and weighted affine planes

### Proposition 11. Attaining witnesses and the fourteen-block upper bound

There is an ordinary $(20,11,3)$ covering with twelve blocks. For
$k\ge3$ and $2\le c\le k$, there is an ordinary $(2k-c,k,3)$ covering
with at most fourteen blocks, on arbitrary point labels.

*Proof.* The twenty-point upper bound uses the following retained family on labels
1 through 20. Each line is one block.

```text
 1  2  3  4  5  6  7  9 10 11 12
 1  2  3  4  5  6  8 13 14 15 16
 1  2  3  4  5  7  8 17 18 19 20
 1  4  6 10 11 15 16 17 18 19 20
 1  4  7  9 12 13 14 15 16 17 20
 1  4  8  9 10 11 12 13 14 18 19
 2  5  6  9 12 13 14 17 18 19 20
 2  5  7 10 11 13 14 15 16 18 19
 2  5  8  9 10 11 12 15 16 17 20
 3  6  7  8  9 11 12 15 16 18 19
 3  6  7  8 10 11 12 13 14 17 20
 3  9 10 13 14 15 16 17 18 19 20
```

These are twelve distinct eleven-subsets covering all
$\binom{20}{3}=1140$ triples. Cardinality, uniformity and coverage are
separately kernel-checked in [the witness declaration](../../lean/CoveringDesigns/C20_11_3/Witness.lean),
whose labels are shifted down by one. This is a finite verification of
one displayed family, not a search through candidate coverings.
The dated repository attribution is **Jan de Heer, 16 May 2005**; its
[public locator and provenance qualification](sources.md#constructions-and-point-links)
do not determine first discovery.

For all offsets use the binary vector space $\mathbb F_2^3$.
For each of its seven nonzero linear functionals $f$ and each
$\epsilon\in\mathbb F_2$, take the plane $f^{-1}(\epsilon)$.
Each plane has four points. The fourteen planes are distinct: the level
sets determine the kernel and hence the nonzero functional over
$\mathbb F_2$, and the two levels of one functional are disjoint.
Every nonempty set of at most three base points lies in a plane, because
its differences from one point span a space of dimension at most two;
a nonzero functional annihilating that space is constant on the set.
The empty set lies in any plane.

For $k=4a+j\ge3$, $0\le j<4$, choose nonnegative integral
weights on these points as follows:

| $j$ | Weights | Total | Maximum plane weight |
|---|---|---:|---:|
| 0 | $a-1$ at two distinct points, $a$ elsewhere | $8a-2$ | $4a$ |
| 1 | $a$ everywhere | $8a$ | $4a\le k$ |
| 2 | $a+1$ at two distinct points, $a$ elsewhere | $8a+2$ | $4a+2$ |
| 3 | $a+1$ at $0,e_1,e_2,e_3$, $a$ elsewhere | $8a+4$ | $4a+3$ |

Here $e_1,e_2,e_3$ are the standard basis vectors. A functional constant
on $0,e_1,e_2,e_3$ has constant zero and vanishes on a basis; it is zero.
Thus no plane contains all four. In the first row $a\ge1$; zero weights
are allowed, including $a=0,j=3$. Every total is $2k-2$.

Replace each base point by a disjoint fibre of its weight. A triple in the
expanded ground set projects to at most three base points, even if two or
three of its points share a fibre. A base plane contains the projection,
so its expansion contains the triple. Every expanded block has size at
most $k$. To pad a set of size $m\le k$ inside a ground set of size $v\ge k$,
choose $k-m$ points from its complement, which has $v-m\ge k-m$ points.
This extends it to size $k$ without losing coverage. Apply this to every
expanded plane inside the $2k-2\ge k$ ground set.
Take the set of resulting blocks. Padding can make two blocks equal:
deduplication preserves ordinary coverage and gives **at most** fourteen
blocks, not an automatic exact count.

For $2\le c\le k, k\ge3$, restrict this family to any $2k-c$ points,
intersect each block with that subset, pad each trace to size $k$, and
again deduplicate. Each target triple was contained in a source block,
so it remains in that block's trace and padded extension. These operations
cannot increase the count beyond fourteen. The inequalities
$k\le2k-c\le2k-2$ guarantee both the restriction and padding steps.
Relabelling gives the construction on any ground set of the required size.
In the theorem's equality ranges, the independent lower bound forces the
resulting family to have exactly fourteen distinct blocks.

## 9. A useful equality insight

The boundary lemma has a verified rigidity refinement. Under its hypotheses,
if $\ell=2b$, write $a$ for the number of support components entirely
contained in $Z$, and $A=\rho I+E$. The proof of §4 gives

\[
b\le\dim\ker(RR^{\mathsf T})\le\dim\ker A\le a\le |Z|/2\le\ell/2=b.
\]

All inequalities are equalities: $|Z|=\ell$, so every component contributes,
and each component has exactly two vertices.
Thus all deficits vanish and the support consists of $b$ disjoint edges
of weight $\rho$. Now assume $\rho=r-\lambda$, the same row balance,
common row sum $r$, Gram matrix $(r-\lambda)I+E+\lambda J$,
$0\le\lambda<r$, and $b>0$. Paired rows have inner product $r$ and
squared norms $r$, so their
difference has squared norm zero and they coincide. Choose one representative of each pair,
forming a square matrix $M$. It satisfies

\[
MM^{\mathsf T}=(r-\lambda)I+\lambda J,\qquad M\mathbf1=r\mathbf1.
\]

The first identity makes $M$ invertible. Multiplying by $\mathbf1$ and
using the second shows $M^{\mathsf T}\mathbf1=q\mathbf1$, with
$q=(r-\lambda+\lambda b)/r$. Total row and column sums give $q=r$, hence
$\lambda(b-1)=r(r-1)$. With $r=6,\lambda=3$, this forces $b=11$.
Thus equality in the coarse rank count is structurally exceptional.
The precise verified specialisation assumes $k\ge3$, uniformity on
$2k-2$ points, actual pair floor three and $\ell=2b$. It yields
$b=11$, zero deficits and paired identical supports in the given blocks.
It does not need triple coverage or a floor on all point degrees.
For a triple cover with $k\ge9$, the additional equality
$(k+2)b=14(k-1)$ forces $\ell=2b$ by (3) and (9).
No conclusion excluding all other points or classifying a symmetric
design at $k=12$ is asserted here. This optional equality insight is not a premise of §7.

## 10. Proof of Theorem 1

Proposition 6 gives the universal lower bound twelve on twenty points;
Proposition 11 supplies the displayed twelve-block covering. This proves (a).

For $k\ge17$, Proposition 10a gives the lower bound thirteen at offset two,
and Proposition 11 gives the upper bound fourteen. This proves (b), without
asserting a thirteen-block construction. For $k\ge35$, Proposition 10a improves
the lower bound to fourteen, proving (c). The offset-three exclusion for
$k\ge59$ similarly combines with Proposition 11 to prove (d).

For (e), assume $c\ge2$ and $k\ge25c$. The degree-floor lemma applies,
and §3 excludes saturation in any proposed covering with at most thirteen
blocks. The partitioned-rank argument in §6 then rules out that budget.
Thus at least fourteen blocks are necessary. The hypotheses imply
$k\ge3$ and $2\le c\le k$, so Proposition 11 supplies an ordinary covering
with at most fourteen blocks. Its size must therefore be exactly fourteen.
All constructions and bounds permit arbitrary finite point labels.

For the parameter table in the README, put $c=2k-v$. Then $c\ge2$ is
$v\le2k-2$, and $k\ge25c$ is $25v\ge49k$. Together they imply $k\ge50$.
Consequently (e) is precisely the guarded strip
$k\ge50,\ \lceil49k/25\rceil\le v\le2k-2$. The separate thresholds in
(c) and (d) improve the uniform strip at offsets two and three.
The supporting inequality (1) was proved in §7.3. $\square$

<a id="appendix-lean-correspondence-and-dependency-contracts"></a>

## Appendix A. Lean correspondence and dependency contracts

All module and declaration names below have the prefix `CoveringDesigns.`;
each linked module is an exact import path after replacing `/` by `.`.
`Family α = Finset (Finset α)` has distinct blocks.
`IsCover C k 3` means uniform size $k$ and coverage of every three-subset.
Every final lower bound assumes only the displayed cardinality, parameter
range and `IsCover`; every exactness contract includes both an existential
ordinary family of the stated size and the universal lower bound.
The point type is arbitrary and finite. Structural interfaces usually list
`[DecidableEq α]` explicitly, as do the twenty-point API and the older
`TwoKMinusTwo.Bounds` and `TwoKMinusTwoEquality.Bounds` lower bounds
(including `lower_inequality`). The newer offset-two/general-offset final
bounds and family attainment/exactness interfaces require only `[Fintype α]`
and obtain decidable equality classically where needed. This is a
representation requirement, not a restriction on the labels.

Audit keys below refer to full-contract checks and transitive axiom checks:
**A20** = [C20_11_3](../../lean/audits/C20_11_3.lean),
**A2** = [TwoKMinusTwo](../../lean/audits/TwoKMinusTwo.lean),
**AE** = [TwoKMinusTwoEquality](../../lean/audits/TwoKMinusTwoEquality.lean),
**AT** = [TwoKMinusTwoTightening](../../lean/audits/TwoKMinusTwoTightening.lean),
**AC** = [TwoKMinusC](../../lean/audits/TwoKMinusC.lean),
**AG** = [TwoKMinusCGeneral](../../lean/audits/TwoKMinusCGeneral.lean),
**AS** = [CaroTuza](../../lean/audits/CaroTuza.lean),
**AL** = [MulticoverLargeDefect](../../lean/audits/MulticoverLargeDefect.lean),
**AW** = [Weighted](../../lean/audits/Weighted.lean),
**AP** = [C17_9_5](../../lean/audits/C17_9_5.lean),
**AM** = [Multicover](../../lean/audits/Multicover.lean), and
**AR** = [PointReduction](../../lean/audits/PointReduction.lean).

### Main conclusions

| Claim | Exact import | Declarations | Audited contract |
|---|---|---|---|
| Theorem 1(a), Proposition 6: twenty-point lower bound | [C20_11_3.LowerBound](../../lean/CoveringDesigns/C20_11_3/LowerBound.lean) | `lower_bound_20_11_3` | A20: 20 points, ordinary (11,3) cover imply at least 12 blocks. |
| Theorem 1(a), Proposition 11: twenty-point attainment and exactness | [C20_11_3.Witness](../../lean/CoveringDesigns/C20_11_3/Witness.lean), [C20_11_3](../../lean/CoveringDesigns/C20_11_3.lean) | `upper_bound_20_11_3_on`, `covering_number_20_11_3_on`, `covering_number_20_11_3` | A20: arbitrary-label and Fin 20 exactness; expanded in Audit20_11_3.covering_number_explicit. |
| Unconditional inequality (1) | [TwoKMinusTwo.Bounds](../../lean/CoveringDesigns/TwoKMinusTwo/Bounds.lean) | `TwoKMinusTwo.lower_inequality` | A2: $k\ge9$, $v=2k-2$, IsCover only; AuditTwoKMinusTwo.lower_explicit expands it. |
| Theorem 1(b,c), Proposition 10a: sharpened offset-two bounds | [TwoKMinusTwoTightening.Bounds](../../lean/CoveringDesigns/TwoKMinusTwoTightening/Bounds.lean) | `TwoKMinusTwoTightening.thirteen_le_card`, `TwoKMinusTwoTightening.fourteen_le_card`, `TwoKMinusTwoTightening.exactness`, `TwoKMinusTwoTightening.covering_number` | AT: $k\ge17$ / $k\ge35$, $v=2k-2$; actual attainment and expanded covering conditions. |
| Corollary 10: selection-based offset-two bounds | [TwoKMinusC.OffsetTwo](../../lean/CoveringDesigns/TwoKMinusC/OffsetTwo.lean) | `TwoKMinusC.OffsetTwo.thirteen_le_card`, `TwoKMinusC.OffsetTwo.fourteen_le_card`, `TwoKMinusC.OffsetTwo.exactness`, `TwoKMinusC.OffsetTwo.covering_number` | AC: $k\ge18$ / $k\ge36$, $v=2k-2$; exactness includes attainment. |
| Theorem 1(e), §6: uniform-offset lower bound | [TwoKMinusCGeneral.UniformLower](../../lean/CoveringDesigns/TwoKMinusCGeneral/UniformLower.lean) | `TwoKMinusCGeneral.fourteen_le_card_uniform` | AG: $c\ge2$, $k\ge25c$, $v=2k-c$, IsCover only. |
| Theorem 1(d), Corollary 10: offset-three lower bound | [TwoKMinusCGeneral.OffsetThreeLower](../../lean/CoveringDesigns/TwoKMinusCGeneral/OffsetThreeLower.lean) | `TwoKMinusCGeneral.fourteen_le_card_offset_three` | AG: $k\ge59$, $v=2k-3$, IsCover only. |
| Theorem 1(d,e), Proposition 11: general family exactness | [TwoKMinusCGeneral.Exactness](../../lean/CoveringDesigns/TwoKMinusCGeneral/Exactness.lean) | `TwoKMinusCGeneral.exactness_uniform`, `TwoKMinusCGeneral.covering_number_uniform`, `TwoKMinusCGeneral.exactness_offset_three`, `TwoKMinusCGeneral.covering_number_offset_three` | AG: both ranges with actual 14-block families; AuditTwoKMinusCGeneral.uniform_explicit and three_explicit expand the definitions. |

### Pivotal lemmas

| Step | Exact import | Declarations | Audited hypotheses and scope |
|---|---|---|---|
| Incidence and independent point link | [C20_11_3.Incidence](../../lean/CoveringDesigns/C20_11_3/Incidence.lean) | `C20_11_3.pair_sum`, `C20_11_3.cross_pair_degree_sum`, `C20_11_3.lower_bound_19_10_2`, `C20_11_3.degree_profile` | A20: pair sum needs uniformity; cross sum is finite counting; profile needs 20 points, IsCover (11,3), exactly 11 blocks. |
| Lemma 2: general point/pair floors | [TwoKMinusCGeneral.Incidence](../../lean/CoveringDesigns/TwoKMinusCGeneral/Incidence.lean) | `TwoKMinusCGeneral.link_lower_bound`, `TwoKMinusCGeneral.degree_ge_six`, `TwoKMinusCGeneral.pair_ge_two` | AG: point floor $c\ge2,8c\le k+7$; pair floor $c\ge2,c<k$; additive cardinality and covering premises. The link has $v+c+1=2k$ and block size $k-1$. |
| Offset-two floors | [TwoKMinusTwo.Incidence](../../lean/CoveringDesigns/TwoKMinusTwo/Incidence.lean) | `TwoKMinusTwo.degree_ge_six`, `TwoKMinusTwo.pair_ge_two` | A2: $v=2k-2$, IsCover; $k\ge9$ / $k\ge3$. |
| Actual supports | [TwoKMinusCGeneral.Geometry](../../lean/CoveringDesigns/TwoKMinusCGeneral/Geometry.lean) | `TwoKMinusCGeneral.saturated_pair_blocks`, `TwoKMinusCGeneral.cross_partner_exists` | AG: additive cardinality, covering and saturation (or the exact two-block star); conclusion retains membership in the actual endpoint classes. No converse. |
| Lemma 3: bounded fibres | [TwoKMinusCGeneral.Assignment](../../lean/CoveringDesigns/TwoKMinusCGeneral/Assignment.lean) | `TwoKMinusCGeneral.exists_cross_assignment`, `TwoKMinusCGeneral.saturated_cross_card_le` | AG: exact star $\{B,D\}$; fibres bounded by $F(c)$, with intersection size $c$ asserted only on the saturated domain. The total extension off that domain has no geometric meaning. |
| Lemma 4: capacity and exclusions | [TwoKMinusCGeneral.Capacity](../../lean/CoveringDesigns/TwoKMinusCGeneral/Capacity.lean), [TwoKMinusCGeneral.Saturation](../../lean/CoveringDesigns/TwoKMinusCGeneral/Saturation.lean) | `TwoKMinusCGeneral.saturated_capacity`, `TwoKMinusCGeneral.no_saturation_uniform`, `TwoKMinusCGeneral.no_saturation_offset_three` | AG: capacity needs $c\ge2,c<k$, IsCover and a distinct saturated pair; no budget/point floor. Exclusions add $b\le13$ and $k\ge25c$ / $c=3,k\ge57$. |
| Offset-two exclusions | [TwoKMinusTwo.Bounds](../../lean/CoveringDesigns/TwoKMinusTwo/Bounds.lean) | `TwoKMinusTwo.no_saturation_twelve`, `TwoKMinusTwo.no_saturation_thirteen` | A2: $k\ge17,b\le12$ / $k\ge33,b\le13$, with covering and cardinality. |
| Lemma 5: boundary kernel | [BoundaryRank.Signless](../../lean/CoveringDesigns/BoundaryRank/Signless.lean), [BoundaryRank.Nullity](../../lean/CoveringDesigns/BoundaryRank/Nullity.lean) | `BoundaryRank.signless_sum_squares`, `BoundaryRank.ker_add_le_of_posSemidef`, `BoundaryRank.two_mul_nullity_le_zero_count`, `BoundaryRank.gram_card_bound` | A20: precisely the nonnegative, loopless, constant-positive-diagonal hypotheses of §4; PSD required for kernel inclusion. |
| Twenty-point rank | [C20_11_3.Rank](../../lean/CoveringDesigns/C20_11_3/Rank.lean) | `C20_11_3.low_gram_rank_ge_twelve`, `C20_11_3.exists_saturated_pair` | A20: rank needs 20 points, uniform size 11, nineteen degree-six points, one degree-seven point and actual pair floor three; no block budget. The second theorem derives the profile and saturation alternative from an 11-block cover. |
| Twenty-point assignment and loss | [C20_11_3.SaturatedAssignment](../../lean/CoveringDesigns/C20_11_3/SaturatedAssignment.lean), [C20_11_3.SaturatedLoss](../../lean/CoveringDesigns/C20_11_3/SaturatedLoss.lean) | `C20_11_3.exists_cross_assignment`, `C20_11_3.second_partner_trace` | A20: actual two supporting blocks, complementary nine-sets; second saturated partner gives a trace product of nine. Injection only on the saturated cross domain. |
| Shared-block budget | [C20_11_3.SaturatedPartition](../../lean/CoveringDesigns/C20_11_3/SaturatedPartition.lean), [C20_11_3.SaturatedBudget](../../lean/CoveringDesigns/C20_11_3/SaturatedBudget.lean), [C20_11_3.Saturated](../../lean/CoveringDesigns/C20_11_3/Saturated.lean) | `C20_11_3.shared_intersection_sum`, `C20_11_3.row_partner_bound`, `C20_11_3.assignment_card_le_twice`, `C20_11_3.no_saturated_pair` | A20: the same four Q-blocks, row sum at least 20, used intersections 2 and all intersections at most 10 yield at most two partners; final exclusion derives these premises. |
| Conditional offset-two rank | [TwoKMinusTwo.Rank](../../lean/CoveringDesigns/TwoKMinusTwo/Rank.lean) | `TwoKMinusTwo.low_gram`, `TwoKMinusTwo.low_card_le`, `TwoKMinusTwo.conditional_rank` | A2: low-row bound needs $k\ge3$, uniformity, $v=2k-2$, actual pair floor; conditional inequality additionally uses $k\ge9$ and covering to derive the point floor. |
| Strict rank | [Weighted.Matrix](../../lean/CoveringDesigns/Weighted/Matrix.lean) | `Weighted.gram_card_le_of_weighted_row_sum_lt` | AW: symmetric nonnegative E, positive scaling weights, strict weighted row allowance, PSD remainder and exact Gram. Section 6 uses scaling weights one and loopless E, a sufficient special case. |
| Partition | [Combinatorics.WeightedPartition](../../lean/CoveringDesigns/Combinatorics/WeightedPartition.lean) | `WeightedPartition.exists_balanced_partition`, `WeightedPartition.exists_large_part` | AP: finite type, integer symmetric loopless weights and positive number of parts; balance even allows signed weights. Rank uses the nonnegative case. |
| Lemma 7: partitioned rank and application | [Weighted.PartitionedRank](../../lean/CoveringDesigns/Weighted/PartitionedRank.lean), [TwoKMinusCGeneral.Rank](../../lean/CoveringDesigns/TwoKMinusCGeneral/Rank.lean) | `Weighted.partitioned_gram_card_le`, `TwoKMinusCGeneral.low_row_le`, `TwoKMinusCGeneral.low_card_le`, `TwoKMinusCGeneral.conditional_rank` | AG: matrix assumptions exactly §6. The family rank inequality needs uniformity, $v+c=2k,c\ge2$ and actual floors six/three; no covering or $c<k$ premise. |
| Lemma 9: selection proof | [CaroTuza.Function](../../lean/CoveringDesigns/CaroTuza/Function.lean), [CaroTuza.Graph](../../lean/CoveringDesigns/CaroTuza/Graph.lean), [CaroTuza.Selection](../../lean/CoveringDesigns/CaroTuza/Selection.lean) | `CaroTuza.decrement`, `CaroTuza.potential_erase_le`, `CaroTuza.exists_selection`, `CaroTuza.exists_nat_selection` | AS: positive integer threshold, finite symmetric nonnegative loopless weights; real version also needs positive high–high edges at least one. Exactly §7.1. |
| Selection-to-rank and two-level count | [MulticoverLargeDefect.Selection](../../lean/CoveringDesigns/MulticoverLargeDefect/Selection.lean), [MulticoverLargeDefect.Counting](../../lean/CoveringDesigns/MulticoverLargeDefect/Counting.lean) | `MulticoverLargeDefect.natExcess_degree`, `MulticoverLargeDefect.independent_card_le`, `MulticoverLargeDefect.potential_bound`, `MulticoverLargeDefect.selection_bound`, `MulticoverLargeDefect.two_level_bound` | AL: indexed actual subset floors and nonnegative coefficients; strict selected excess, then $A\ge2H\ge0$ for counting. Section 7.2 is their $s=1$ instance. |
| Proposition 8: structural bound and actual-family adapter | [MulticoverLargeDefect.LowerBound](../../lean/CoveringDesigns/MulticoverLargeDefect/LowerBound.lean), [TwoKMinusC.LargeDefect](../../lean/CoveringDesigns/TwoKMinusC/LargeDefect.lean) | `MulticoverLargeDefect.lower_bound_of_multiplicities`, `TwoKMinusC.actual_subset_floors`, `TwoKMinusC.actual_floors_bound`, `TwoKMinusC.actual_floors_real`, `TwoKMinusC.actual_floors_inequality` | AL/AC: adapter needs exactly uniformity, $v+c=2k,c\ge2,c<k,k>6$ and actual point/pair floors six/three. Both counting branches retained. |
| Corollary 10: coefficients and strict thresholds | [TwoKMinusC.Algebra](../../lean/CoveringDesigns/TwoKMinusC/Algebra.lean), [TwoKMinusC.OffsetTwoArithmetic](../../lean/CoveringDesigns/TwoKMinusC/OffsetTwoArithmetic.lean), [TwoKMinusCGeneral.OffsetThreeArithmetic](../../lean/CoveringDesigns/TwoKMinusCGeneral/OffsetThreeArithmetic.lean) | `TwoKMinusC.defect_eq`, `TwoKMinusC.denominator_pos`, `TwoKMinusC.value_eq_Q`, `TwoKMinusC.twelve_lt_Q_two`, `TwoKMinusC.thirteen_lt_Q_two`, `TwoKMinusCGeneral.thirteen_lt_Q_three` | AC/AG: signed defect and positive denominators; comparisons strictly greater than 12/13 before rounding. |
| Proposition 10a: centering and retained rank budget | [BoundaryRank.Completion](../../lean/CoveringDesigns/BoundaryRank/Completion.lean) | `BoundaryRank.centered_completion` | AT: finite real matrix, nonempty columns, positive constant diagonal, symmetric nonnegative loopless excess, nonnegative deficits, constant row sum, exact Gram and $b\lambda\ge r^2$; empty row type allowed. |
| Proposition 10a: few binary supports | [BoundaryRank.BinaryCompletion](../../lean/CoveringDesigns/BoundaryRank/BinaryCompletion.lean) | `BoundaryRank.completion_card_le_one`, `BoundaryRank.binary_completion_card_le_two` | AT: nonempty column type, T1=0, column corank at most one/two, fixed image and coordinate sum; second case requires binary coordinates. |
| Proposition 10a: support-class capacity | [BoundaryRank.CloneCapacity](../../lean/CoveringDesigns/BoundaryRank/CloneCapacity.lean) | `BoundaryRank.indexed_clone_capacity`, `BoundaryRank.clone_card_le_five`, `BoundaryRank.clone_card_le_ten` | AT: uniform indexed blocks, nonempty identical-support class with stated degree and pair floor; empty classes handled in the endpoint corollaries. |
| Proposition 10a: high-point count and endpoint exclusions | [TwoKMinusTwoTightening.Incidence](../../lean/CoveringDesigns/TwoKMinusTwoTightening/Incidence.lean), [TwoKMinusTwoTightening.Endpoints](../../lean/CoveringDesigns/TwoKMinusTwoTightening/Endpoints.lean) | `TwoKMinusTwoTightening.regularHigh_count_bound`, `TwoKMinusTwoTightening.no_twelve_32_17`, `TwoKMinusTwoTightening.no_thirteen_68_35` | AT: ordinary uniform families with actual point/pair floors six/three; final covering wrappers derive all floors. No full component classification. |
| Occurrences and deduplication | [Multicover.Family](../../lean/CoveringDesigns/Multicover/Family.lean) | `Multicover.ofFamily_card`, `Multicover.ofFamily_subsetDegree`, `Multicover.ofFamily_uniform`, `Multicover.deduplicate_card_le`, `Multicover.deduplicate_isCover_one` | AM; AC.occurrence_transport: one occurrence per distinct original block preserves every multiplicity. Deduplication preserves ordinary coverage, not arbitrary higher multiplicity. |
| Proposition 11: weighted expansion and upper construction | [TwoKMinusTwo.Expansion](../../lean/CoveringDesigns/TwoKMinusTwo/Expansion.lean), [TwoKMinusTwo.AffineWeights](../../lean/CoveringDesigns/TwoKMinusTwo/AffineWeights.lean), [TwoKMinusTwo.Construction](../../lean/CoveringDesigns/TwoKMinusTwo/Construction.lean) | `TwoKMinusTwo.pad_indexed`, `TwoKMinusTwo.weighted_expansion`, `TwoKMinusTwo.weight_sum`, `TwoKMinusTwo.weight_plane_le`, `TwoKMinusTwo.small_base_subset`, `TwoKMinusTwo.upper_bound` | A2: nonnegative fibres, projected sets of size at most three, block sizes at most k before padding, $k\ge3$; result has at most 14 distinct blocks. |
| Reduction and general attainment | [PointReduction.Family](../../lean/CoveringDesigns/PointReduction/Family.lean), [TwoKMinusCGeneral.Attainment](../../lean/CoveringDesigns/TwoKMinusCGeneral/Attainment.lean) | `PointReduction.family_reduce_points`, `TwoKMinusCGeneral.upper_bound` | AR/AG: target size between k and source size. General upper bound uses $v+c=2k,2\le c\le k,k\ge3$ and arbitrary target labels. |
| Equality insight only | [BoundaryRank.Equality](../../lean/CoveringDesigns/BoundaryRank/Equality.lean), [TwoKMinusTwoEquality.Matrix](../../lean/CoveringDesigns/TwoKMinusTwoEquality/Matrix.lean), [TwoKMinusTwoEquality.Rigidity](../../lean/CoveringDesigns/TwoKMinusTwoEquality/Rigidity.lean) | `BoundaryRank.gram_equality`, `TwoKMinusTwoEquality.square_parameters`, `TwoKMinusTwoEquality.boundary_parameter`, `TwoKMinusTwoEquality.low_equality_rigidity` | AE: exactly §9. Matrix parameter equation allows $\lambda=0$ and needs positive column count; general pairing includes empty types. No all-points-paired classification. |

The generic structural bound in AL takes an indexed uniform family,
subset size $s$, and a floor sequence $g$: coefficients below $s$ are
nonnegative, actual multiplicities dominate $g(j)$ for $s\le j\le2s$,
and $g(s)<\binom{k}{s}$, $1\le a_s<g(s)$, $a_s\le d$.
Here $s=1$, $g(1)=6$, $g(2)=3$ (zero elsewhere),
$a_0=a_1=3$, $d=6(k-1)-3(v-1)=3(c-1)$ and $\binom{k}{1}=k$.
These verify all its premises. Its separate covering wrapper requires
universal residual bounds; this application does not use that wrapper.

### Logical independence and representation checks

The twenty-point entry imports only its LowerBound, Witness and standard
axiom guard. LowerBound imports its local Rank and Saturated modules;
Rank imports local Incidence and BoundaryRank.Nullity. Witness imports
Foundations.Relabelling. None imports a TwoKMinus family, another numerical
exactness theorem, a classification, selection, or a research script.
Some later family modules reuse elementary helpers housed in C20_11_3;
they do not import its numerical exclusion or witness.

UniformLower imports general Rank and Saturation; it does not use the
large-defect adapter. OffsetThreeLower imports the actual-floor adapter,
offset-three arithmetic and Saturation; it does not use partitioned rank.
OffsetTwo similarly composes its adapter/arithmetic with the unchanged
offset-two saturation and construction modules. Equality rigidity is not
needed by these sharper thresholds. These boundaries are checked by the
unchanged [library audit policy](../../scripts/audit_library.py).

In §7 each original block becomes exactly one indexed occurrence, so the
rank column count is still $b$. In §8 different padded occurrences can
coincide; taking their finite image gives at most the occurrence count.
Only an independent lower bound turns this into exact attainment. Natural
subtractions in the final Lean parameters are justified by the stated
ranges; the internal general-offset contracts use $v+c=2k$. All scalar
differences and Gram entries in this account are signed.

The displayed proof of (1) is reorganised using the strongest lower bounds;
the independent A2 contract predates that composition. The optional AE
contracts for thresholds 19/40 and the A2 thresholds 20/41 remain unchanged
development history, not extra premises of the main argument. The classical
coarse eventual-exactness deduction in
[sources](sources.md#qualitative-eventual-exactness) has no corresponding
claimed declaration here.

The four affine patterns in §8 use $k=4a+j$ for readability. Lean instead
writes $k=3+4a+j$ to keep every weight expression natural: in that order
the patterns are $a+1_{\{0,e_1,e_2,e_3\}}$, $a+1_{V\setminus\{x,y\}}$,
$a+1$, and $a+1+1_{\{x,y\}}$, for two distinct base points $x,y$.
These are the same four patterns with shifted residues. Lean proves
coverage of smaller projections by extending them to a three-set; §8
uses the equivalent annihilating-functional argument. Section 6 sums the
class bounds, while Lean selects a largest class. These are explanatory
reorganisations, not additional hypotheses or strengthened contracts.

Only the foundational axioms `propext`, `Classical.choice`, `Quot.sound`
are permitted by the audits, with the existing exact sets required where
specified. Compilation and record auditing are distinct from the mathematical
claims made in prose. [Appendix B](#appendix-b-verification-and-supporting-modules)
describes the verification commands and included supporting modules.


## Appendix B. Verification and supporting modules

The Lean proofs, their supporting project modules, audit contracts and
verification tools are included in this repository. Follow the
[verification guide](../../technical-details.md) to install the pinned Lean
and Mathlib dependencies. Then, from the repository root, run:

```sh
./covering check
./covering verify
./covering audit
```

`check` validates sources and retained data; `verify` compiles the proofs and
runs the theorem-contract and foundational-axiom audits. `audit` validates
the resulting records against the current inputs without recompiling.
The full verification covers all included results. The guide also lists
focused verification targets for these results and their prerequisites.

The six public entry modules are
[`C20_11_3`](../../lean/CoveringDesigns/C20_11_3.lean),
[`TwoKMinusTwo`](../../lean/CoveringDesigns/TwoKMinusTwo.lean),
[`TwoKMinusTwoEquality`](../../lean/CoveringDesigns/TwoKMinusTwoEquality.lean),
[`TwoKMinusC`](../../lean/CoveringDesigns/TwoKMinusC.lean),
[`TwoKMinusTwoTightening`](../../lean/CoveringDesigns/TwoKMinusTwoTightening.lean), and
[`TwoKMinusCGeneral`](../../lean/CoveringDesigns/TwoKMinusCGeneral.lean).
Together with their transitive project imports they comprise the following
96 included source modules. In this table paths are relative to
`lean/CoveringDesigns/`; “entry” means the `.lean` file beside that directory.
The equality entry supports optional §9 and the preserved component stages.

| Directory or module group | Required files (each with suffix `.lean`) |
|---|---|
| `C20_11_3` | entry, Incidence, LowerBound, Rank, Saturated, SaturatedAssignment, SaturatedBudget, SaturatedGeometry, SaturatedLoss, SaturatedPartition, Witness |
| `TwoKMinusTwo` | entry, AffineWeights, Arithmetic, Bounds, Capacity, Construction, Expansion, Geometry, Incidence, Rank |
| `TwoKMinusTwoTightening` | entry, Bounds, Endpoints, Incidence |
| `TwoKMinusTwoEquality` | entry, Bounds, Matrix, Rigidity |
| `TwoKMinusC` | entry, Algebra, LargeDefect, OffsetTwo, OffsetTwoArithmetic |
| `TwoKMinusCGeneral` | entry, Arithmetic, Assignment, Attainment, Capacity, Exactness, Geometry, Incidence, OffsetThreeArithmetic, OffsetThreeLower, Rank, Saturation, UniformLower |
| `Foundations` | Basic, Bounds, Intersecting, Links, Relabelling, StandardAxioms |
| `BoundaryRank` | BinaryCompletion, CloneCapacity, Completion, Equality, Nullity, Signless |
| `Weighted` | Counting, Matrix, PartitionedRank |
| `Combinatorics` | WeightedPartition |
| `CaroTuza` | Function, Graph, Selection |
| `Equality` | FiniteSum, Slack |
| `HigherIncidence` | Binomial, Counting, Matrices, Parameters, Subsets |
| `Horsley` | Matrix |
| `HorsleySingh` | Counting, Matrices, SubsetLinks |
| `LargeDefect` | Algebra |
| `Multicover` | Basic, Counting, Family, Links, Schoenheim |
| `MulticoverIncidence` | Counting, LowerBound, Matrices, Parameters |
| `MulticoverLargeDefect` | Counting, LowerBound, Selection |
| `AffineConstructions` | Geometry, Transformations |
| `PointReduction` | Basic, Bounds, Family |
| `Schoenheim` | LowerBound |

The twelve audit files linked in the proof appendix are included under
[`lean/audits/`](../../lean/audits/), together with their imports. These audits
also exercise other applications and examples, so the repository includes
23 additional project modules beyond the proof closure: `Applications.ZeroDefect`, `C17_9_5`
and `C17_9_5.LowerBound`; the entries `CaroTuza`, `Multicover`,
`MulticoverLargeDefect`, `PointReduction`, `Weighted`; `CaroTuza.Examples`,
`HigherIncidence.LowerBound`, `HorsleySingh.Examples`,
`HorsleySingh.LowerBound`, `HorsleySingh.Parameters`, `LargeDefect.LowerBound`,
`LargeDefect.Selection`, `Multicover.Examples`, `Multicover.Multiset`,
`MulticoverIncidence.Family`, `MulticoverLargeDefect.Examples`,
`MulticoverLargeDefect.Family`, `PointReduction.Examples`, `Weighted.Examples`
and `Weighted.Pairs`. In particular, the partition lemma's existing audit
is housed in `C17_9_5`; that numerical result is not a mathematical premise.

Build support includes [`lean-toolchain`](../../lean/lean-toolchain),
[`lakefile.toml`](../../lean/lakefile.toml),
[`lake-manifest.json`](../../lean/lake-manifest.json),
[`dependencies.json`](../../lean/dependencies.json), and the pinned Mathlib
and package dependencies they specify. The proof appendix also links the
[`audit_library.py`](../../scripts/audit_library.py) policy. The CLI, runners,
input manifests and retained data needed by that workflow are included.
Verification records are generated when the commands run; no prior record
is a proof premise. The twelve-block witness is embedded in
[`C20_11_3/Witness.lean`](../../lean/CoveringDesigns/C20_11_3/Witness.lean)
and displayed in the proof account.
