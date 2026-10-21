# C(18,10,3) = 12 and five Schönheim lifting bounds

**Rob Gardiner**

## Abstract

We prove that every covering of the triples of 18 points by 10-element
blocks needs at least 12 blocks. A historical 12-block construction
establishes equality. The lower proof combines saturated-pair capacity
counting, a matching obstruction, equality in a signless rank bound, and
an incidence count in two exceptional blocks. Schönheim's point-link
lifting theorem, retaining every intermediate ceiling, then gives lower
bounds 21, 35, 57, 90 and 138 for C(19,11,4), C(20,12,5), C(21,13,6),
C(22,14,7) and C(23,15,8), respectively. All six conclusions are formalised
in Lean. The lower proof uses neither a classification of minimum coverings
nor a computational exclusion.

## 1. Introduction: statement, scope and provenance

An ordinary family $\mathcal C$ is a finite set of distinct subsets of a
finite point set $V$. It is a $(v,k,t)$ covering if $|V|=v$, every block
has size $k$, and every $t$-subset of $V$ is contained in a block.
The covering number $C(v,k,t)$ is the minimum size of such a family.

**Theorem 1 (exact seed).** On every 18-point set, every ordinary
$(18,10,3)$ covering has at least 12 blocks, and a covering with exactly
12 distinct blocks exists. Thus

$$
C(18,10,3)=12.
$$

The theorem assumes only the point count and covering conditions. An indexed
version of its lower bound also permits repeated block occurrences: replace
an indexed family by its ordinary image family, whose cardinality is at most
the number of occurrences. The main proof below treats ordinary families;
its block indices are the actual members of $\mathcal C$. Distinct points
with identical block supports remain distinct points.

### Background and contribution

The historical construction supplies the upper bound. The contribution
presented here is the structural exclusion of 11 blocks, its reusable
rank-equality and support-obstruction lemmas, and the Lean formalisation,
developed by Rob Gardiner with substantial AI assistance. Schönheim is
credited for the lifting theorem; the five higher-strength inequalities are
consequences of the seed and that theorem.

The argument assumes standard finite counting and real linear algebra:
rank–nullity, Gram matrices and positive semidefinite matrices. The specialised
incidence, rank and support arguments are proved below. The
[source account](sources.md) gives the construction attribution, the dated
comparison with earlier bounds, and source-access limitations. Those
historical questions are not premises of the proof.

### Proof outline

Lemma 2 reduces an 11-block cover to two degree profiles. Lemma 3 excludes
pairs of multiplicity 2. Lemmas 4–5 leave one equality case in a rank bound;
Lemma 6 extracts five pairs of equal incidence rows. Lemmas 7–8 count the
two exceptional blocks and force an uncovered triple. Proposition 9 gives
the attaining construction, completing Theorem 1. Theorem 10 and
Corollary 11 give the lifting consequences.

The [correspondence appendix](#appendix-a-lean-correspondence) maps these
statements to their Lean declarations. Verification and reuse boundaries
are in [Appendix B](#appendix-b-reuse-boundaries-and-verification).

## 2. Incidence floors and the only degree profiles

Write $I=\mathcal C$ for the block index set and define

$$
S_x=\{i\in I:x\in B_i\},\qquad
d(x)=|S_x|,\qquad \mu(x,y)=|S_x\cap S_y|.
$$

**Lemma 2 (incidence floors and profiles).** Every $(18,10,3)$ covering
has $d(x)\ge6$ for every point, $\mu(x,y)\ge2$ for distinct points, and
at least 11 blocks. If it has 11 blocks, its degree profile is either
$6^{17}\cdot8$ or $6^{16}\cdot7^2$.

**Proof.** First, $C(17,9,2)\ge6$. Suppose a pair covering has at most
5 blocks. Every point has degree at least 2: the blocks through it must
cover 16 other points in residual 8-sets. If a point has degree 2, those
two residual sets partition the other 16 points. Their 64 cross-pairs must
be covered by the remaining at most 3 blocks. A 9-set covers at most
20 cross-pairs, since its two trace sizes sum to at most 9. This would give
$64\le60$. Thus every point would have degree at least 3, contradicting
$51\le9|\mathcal C|\le45$.

Deleting a point from each block through it gives an ordinary $(17,9,2)$
link. Deletion is injective on these blocks, since reinsertion recovers
the original block. Hence $d(x)\ge6$. Double-counting incidences gives
$10|\mathcal C|=\sum_xd(x)\ge108$, so $|\mathcal C|\ge11$.
If $|\mathcal C|=11$, then

$$
\sum_x(d(x)-6)=110-108=2.
$$

The nonnegative integer excesses give precisely the two stated profiles.
Finally, the blocks through a pair must cover the other 16 points in
residual 8-sets, so every pair occurs in at least 2 blocks. ∎

Call a pair **saturated** if its multiplicity is exactly 2. From now through
§7, assume for contradiction that $\mathcal C$ has 11 blocks.

## 3. Excluding saturated pairs

**Lemma 3 (pair floor).** An 11-block $(18,10,3)$ covering has no saturated
pair. Consequently every distinct point pair has multiplicity at least 3.

**Proof.** The three steps below retain actual point and block identities.

### 3.1 Residual geometry and actual index assignments

Let $pq$ be saturated, supported at indices $i,j$. Triple coverage forces
$B_i\cup B_j=V$, while uniformity gives $|B_i\cap B_j|=20-18=2$.
Consequently

$$
B_i=\{p,q\}\cup X,\qquad B_j=\{p,q\}\cup Y,
$$

where $X,Y$ are disjoint 8-sets partitioning $V\setminus\{p,q\}$.
Also $d(p)+d(q)-2=|S_p\cup S_q|\le11$. Both degrees are at least 6,
so orient the pair with $d(q)=6$; then $d(p)\in\{6,7\}$.

The other 9 indices split into $P$ (through $p$ only), $Q$ (through $q$
only) and $N$ (through neither). Put $n=d(p)-2\in\{4,5\}$. Then
$|P|=n$, $|Q|=4$ and $|N|=5-n$. The two common blocks cover no pair
in $X\times Y$. A block in $P$ or $Q$ has cross-pair capacity at most
20, and a block in $N$ has capacity at most 25. If $s$ counts saturated
cross-pairs, all other cross-pairs have multiplicity at least 3. Thus

$$
192-s\le\sum_{x\in X,y\in Y}\mu(x,y)
\le20(n+4)+25(5-n)=205-5n,
\qquad s\ge5n-13.
$$

For a saturated cross-pair $xy$, coverage of $pxy$ and $qxy$ requires
one of its two supporting indices in $P$ and the other in $Q$. They are
distinct because neither common $pq$ block contains $xy$. Saturated
geometry applied to $xy$ says that their block intersection is exactly
$\{x,y\}$. Assign $xy$ to this ordered pair in $P\times Q$. Equal
assigned pairs have equal intersections and therefore equal cross-pairs,
with their unique $X\times Y$ orientation. The assignment is injective,
so $s\le4n$. The size-2 intersection assertion applies to assigned
saturated pairs, not to arbitrary pairs of blocks in $P\times Q$.

### 3.2 Twelve units of lost capacity and integer fibre bounds

Suppose $qz$ is another saturated pair, with $z\in X$ after interchanging
sides if necessary. One supporting block is $\{p,q\}\cup X$; the other
is forced to be $\{q,z\}\cup Y$. The latter belongs to $Q$ and has
residual trace sizes 1 and 8. Its cross-pair capacity is 8 instead of 20,
a loss of 12. Thus $s\ge5n-1>4n$ for $n\in\{4,5\}$, a contradiction.
The endpoint $q$ has no second saturated partner.

Every residual point therefore occurs in at least 3 blocks through $q$,
exactly one of which is a common $pq$ block. It occurs in at least 2 of
the 4 blocks in $Q$. A fixed block $A$ in $P$ has 9 residual points,
so $\sum_{D\in Q}|A\cap D|\ge18$. If $r$ saturated cross-pairs are
assigned to $A$, their $Q$ coordinates are distinct and those $r$
intersections have size 2. All other intersections have size at most 9,
because $p$ is absent from every block in $Q$. Hence

$$
18\le2r+9(4-r)=36-7r.
$$

The integer $r$ is at most 2. Summing this rounded bound for each block
in $P$ gives $s\le2n$. The case $n=5$ would require $12\le s\le10$.
Thus every saturated pair has two degree-6 endpoints. Applying the same
argument with either endpoint as $q$ shows that neither has another
saturated partner. The residual partition of every saturated edge has at
least $5\cdot4-13=7$ saturated cross-edges.

### 3.3 Matching and occurrence packing

Saturated edges form a matching on at most 17 low-degree points, so there
are at most 8 edges. If any edge exists, its at least 7 residual
cross-edges force exactly 8. Reapply the local result at each edge:
all 7 other edges cross its residual partition.

A block supporting that edge is one of its two common blocks and contains
exactly one endpoint of each other edge. It cannot support another edge.
Counting pairs $(e,i)$ with $e$ saturated and $e\subseteq B_i$ therefore
gives $2\cdot8\le11$, a contradiction. Every pair has multiplicity at
least 3. ∎

## 4. Signless rank and all high-point cases

Let $L$ be the degree-6 points, $\ell=|L|$, and let $R$ be their real
binary incidence matrix over the 11 block indices. Define

$$
E_{xx}=0,\qquad E_{xy}=\mu(x,y)-3\quad(x\ne y\text{ in }L),
\qquad \delta_x=\sum_{h\notin L}(\mu(x,h)-3).
$$

**Lemma 4 (boundary-rank estimate).** For an 11-block covering as above,
$E$ is symmetric and entrywise nonnegative, the deficits $\delta_x$ are
nonnegative integers, and

$$
RR^{\mathsf T}=3I+E+3J,\qquad E\mathbf1+\delta=3\mathbf1.
$$

Writing $Z=\{x\in L:\delta_x=0\}$, one has

$$
\operatorname{rank}R\ge\ell-\lfloor|Z|/2\rfloor,
\qquad 2\ell\le22+|Z|.
$$

Here $I$ in the matrix identity is the identity matrix and $J$ is the
all-ones matrix.

**Proof.** Lemma 3 gives nonnegativity. Each low point lies in 6 blocks,
each with 9 companions. Subtracting the baseline multiplicity 3 for
each of the other 17 points gives $6\cdot9-17\cdot3=3$, proving the
row balance. The diagonal Gram entries are 6 and the off-diagonal entries
are $\mu(x,y)$, proving the matrix identity. In particular
$0\le\delta_x\le3$.

For $A=3I+E$, the row balance gives the signless identity

$$
z^{\mathsf T}Az=\sum_x\delta_xz_x^2+
\frac12\sum_{x,y}E_{xy}(z_x+z_y)^2.
$$

Thus $A$ and $3J$ are positive semidefinite. Kernel vectors of $A$
vanish at positive deficits and alternate along edges where $E_{xy}>0$;
conversely these restrictions imply membership in $\ker A$.
Each component of the support graph entirely inside $Z$ contributes at
most one free coordinate and uses at least 2 vertices: every zero-deficit
row has positive edge sum 3. A component meeting a positive deficit
contributes none. An odd cycle can reduce, but cannot increase, the
dimension. Consequently $2\dim\ker A\le|Z|$.

Positive semidefiniteness gives
$\ker(RR^{\mathsf T})\subseteq\ker A$, and the real Gram identity gives
$\operatorname{rank}(RR^{\mathsf T})=\operatorname{rank}R$. Rank–nullity
proves the first inequality; the 11 columns of $R$ give the second. ∎

**Lemma 5 (the surviving high-point case).** An 11-block covering must
have two degree-7 points $h,g$, with $\mu(h,g)=6$.

**Proof.** With one degree-8 point, $\ell=17$ and
$\sum_x\delta_x=8\cdot9-17\cdot3=21$. Since each deficit is at most
3, at least 7 are positive. Thus $|Z|\le10$ and Lemma 4 gives
$\operatorname{rank}R\ge12$, impossible.

With two degree-7 points, put $m=\mu(h,g)$. Then $3\le m\le7$.
Summing incidences from the high points to the low points gives
$\sum_x\delta_x=30-2m$. Lemma 4 gives the following possibilities.

| $m$ | $\sum_x\delta_x$ | Maximum $\lvert Z\rvert$ | Rank lower bound |
|---:|---:|---:|---:|
| 3 | 24 | 8 | 12 |
| 4 | 22 | 8 | 12 |
| 5 | 20 | 9 | 12 |
| 6 | 18 | 10 | 11 |
| 7 | 16 | 8, using even deficits | 12 |

For the last row, two supports of size 7 and intersection size 7 are
equal. Thus $\delta_x=2(\mu(x,h)-3)$ is even and at most 3, hence at
most 2. A total of 16 forces at least 8 positive deficits. This does not
identify $h$ and $g$ as points. Only $m=6$ remains. ∎

## 5. Extracting every equality consequence

**Lemma 6 (equality core).** In the case of Lemma 5, the 16 low points
partition into five pairs and six single points. Each pair has identical
block supports, deficit 0 and mutual multiplicity 6. Points in different
pairs have multiplicity 3. Each single point has deficit 3 and its row
of $E$ is zero. Moreover $\operatorname{rank}R=11$.

**Proof.** The total deficit 18 implies $|Z|\le10$. Write
$q=\dim\ker(RR^{\mathsf T})$, $a=\dim\ker A$, and let $c$ be the number
of support-graph components entirely inside $Z$. The proof of Lemma 4 gives

$$
5\le q=16-\operatorname{rank}R\le a\le c
\le\lfloor|Z|/2\rfloor\le5.
$$

Every inequality is an equality. Hence $|Z|=10$, the six positive deficits
all equal 3, and $q=a=c=5$. Their corresponding rows of $E$ have sum 0
and nonnegative entries, so those rows and, by symmetry, columns vanish.
Thus $Z$ is closed under support-graph edges.

The five components inside $Z$ are nonisolated and exhaust its ten vertices,
so each has exactly two vertices. Its edge has weight 3 by row balance.
Equivalently, restriction of $\ker A$ to $\mathbb R^Z$ is injective,
has dimension 5 and alternates on graph edges; the equality argument
applies to this restricted set, rather than all 16 rows.

Rank–nullity gives rank 11, and the kernel inclusion is equality.
Paired incidence rows are equal for a separate reason: the specified
$3J$ remainder makes their squared norms and mutual inner product all 6.
Their difference has squared norm $6+6-2\cdot6=0$. Graph pairing for an
arbitrary positive semidefinite remainder would not suffice for this step.

These five pairs and six single points exhaust the actual low points.
Between different pairs the $E$-entry is 0, giving multiplicity 3. ∎

## 6. Counting the two exceptional blocks

Put $H=S_h$ and $G=S_g$. Their sizes are 7 and their intersection has
size 6, so $H\setminus G=\{a\}$ and $G\setminus H=\{b\}$ for distinct
block indices $a,b$.

**Lemma 7 (two absent paired classes).** Exactly three of the five
paired classes in Lemma 6 occur in both blocks $B_a,B_b$. The other
two classes occur in neither block.

**Proof.** Set $K=H\cap G$. For a low point $x$, write
$z_x=\mathbf1_{a\in S_x}+\mathbf1_{b\in S_x}$. The disjoint support
decomposition gives

$$
\mu(x,h)+\mu(x,g)=2|S_x\cap K|+z_x=6+\delta_x.
$$

A zero-deficit point meets both high supports in exactly 3 indices:
both counts are at least 3 and their sum is 6. Parity forces $z_x$ to
be 0 or 2. Its paired point has the same support and makes the same
choice. Each of the six deficit-3 points instead has odd sum 9, so
$z_x=1$.

Let $p$ count paired classes present in both exceptional blocks. Count
incidences in those two blocks over all 18 actual points, counting a point
twice if it occurs in both. The high points contribute 2, the six single
low points contribute 6, and each present paired class contributes 4.
Uniformity therefore gives

$$
20=2+6+4p,\qquad p=3.
$$

Exactly two of the five paired classes avoid both blocks. ∎

This count is an actual-column constraint. If $P_i$ are the five paired
supports and $Q_j$ the six single supports, then at every block index $c$
it uses

$$
\mathbf1_{c\in H}+\mathbf1_{c\in G}
+2\sum_i\mathbf1_{c\in P_i}+\sum_j\mathbf1_{c\in Q_j}=10.
$$

The factor 2 counts two actual points. The argument works for occurrence
indices even when block values repeat; the column margin cannot be inferred
from arbitrary real Gram data alone.

## 7. Actual supports force an uncovered triple

**Lemma 8 (support obstruction).** Under the conclusions of Lemmas 5–7,
there are distinct actual points $h,x,y$ with
$S_h\cap S_x\cap S_y=\varnothing$.

**Proof.** Choose $x,y$ from the two different paired classes absent
from $B_a,B_b$. Their supports have size 6, mutual intersection size 3,
and each meets $H$ in 3 indices. Thus

$$
|S_x\cup S_y|=6+6-3=9,\qquad S_x\cup S_y=I\setminus\{a,b\}.
$$

For finite sets $H\subseteq I$ and $S\cup T=I\setminus A$, with
$A\subseteq I$, inclusion–exclusion gives

$$
|H\cap S\cap T|+|H|=|H\cap S|+|H\cap T|+|H\cap A|.
$$

Here $H$ contains $a$ and not $b$, so
$|H\cap S_x\cap S_y|+7=3+3+1=7$. The intersection is empty.
The chosen low points lie in different paired classes and outside
$\{h,g\}$, so $h,x,y$ are distinct. ∎

Triple coverage requires a block containing $h,x,y$, contradicting Lemma 8.
Uniform block sizes and this final use of triple coverage are essential:
pair multiplicities and the rank estimate alone do not finish the proof.

## 8. Historical attainment

**Proposition 9 (attainment).** The following 12 distinct blocks on
$\{0,\ldots,17\}$ form a $(18,10,3)$ covering.

| Block | Points |
|---:|---|
| 1 | 0, 1, 2, 3, 4, 9, 10, 11, 12, 13 |
| 2 | 0, 1, 3, 5, 8, 9, 10, 12, 14, 17 |
| 3 | 0, 1, 5, 6, 7, 9, 10, 14, 15, 16 |
| 4 | 0, 2, 4, 5, 6, 9, 11, 13, 14, 15 |
| 5 | 0, 2, 4, 7, 8, 9, 11, 13, 16, 17 |
| 6 | 0, 3, 6, 7, 8, 9, 12, 15, 16, 17 |
| 7 | 1, 2, 3, 6, 7, 10, 11, 12, 15, 16 |
| 8 | 1, 2, 5, 7, 8, 10, 11, 14, 16, 17 |
| 9 | 1, 3, 4, 5, 7, 10, 12, 13, 14, 16 |
| 10 | 1, 3, 4, 6, 8, 10, 12, 13, 15, 17 |
| 11 | 2, 3, 5, 6, 8, 11, 12, 14, 15, 17 |
| 12 | 4, 5, 6, 7, 8, 13, 14, 15, 16, 17 |

**Proof.** Each displayed block has 10 distinct points and the 12 blocks
are distinct. Direct finite checking shows that every one of the
$\binom{18}{3}=816$ triples is contained in a displayed block. Lean proves
these assertions by ordinary kernel reduction of this explicit list.
Transport along a bijection gives a covering of exactly the same size on
any 18-point set. ∎

The historical construction uses labels 1–18; the displayed labels are
shifted by one to agree with the included
[Lean witness](../../lean/CoveringDesigns/C18_10_3/Witness.lean) on `Fin 18`. The source credits “JCD article” and carries the timestamp
1996-11-14 17:08:00, which is source metadata rather than an established
discovery date. Attribution is **Daniel M. Gordon / La Jolla Covering
Repository, CC BY 4.0**. The construction is known; the
[source account](sources.md#historical-attaining-construction) preserves its provenance.
Checking this attaining witness is separate from the structural lower proof;
it is not a search for or an enumeration of hypothetical 11-block coverings.

**Proof of Theorem 1.** Lemma 2 gives at least 11 blocks. If there were
exactly 11, Lemma 3 would give pair multiplicity at least 3. Lemmas 4–5
would force the two-high-point case with mutual multiplicity 6. Lemmas 6–8
would then produce an uncovered triple, a contradiction. Every covering
therefore has at least 12 blocks. Proposition 9 supplies exactly 12 blocks
on every 18-point set. ∎

## 9. Schönheim lifting and the five consequences

**Theorem 10 (Schönheim point-link lifting).** Let $1\le t\le k\le v$.
If every ordinary $(v-1,k-1,t-1)$ covering on arbitrary finite point sets
has at least $L$ blocks, then every ordinary $(v,k,t)$ covering has at least
$\lceil vL/k\rceil$ blocks.

**Proof.** For each point $x$, delete $x$ from every block containing it.
Deletion is injective on that subfamily because adjoining $x$ reconstructs
the block. The image is a $(k-1)$-uniform family on the other $v-1$ points,
with exactly $d(x)$ blocks. Every $(t-1)$-subset $T$ of those points extends
to the $t$-subset $T\cup\{x\}$; coverage supplies a block through $x$
containing it. Thus the image covers $T$, including the empty subset when
$t=1$. The universal premise gives $d(x)\ge L$. Double-counting yields
$k|\mathcal C|=\sum_xd(x)\ge vL$. Since $k>0$, integer rounding gives
$|\mathcal C|\ge\lceil vL/k\rceil$. This is Schönheim's incidence argument;
see [sources](sources.md#schonheim-lifting). ∎

**Corollary 11 (five lifting bounds).** Every ordinary covering at the
following parameters satisfies the stated lower bound:

$$
\begin{aligned}
C(19,11,4)&\ge21,& C(20,12,5)&\ge35,& C(21,13,6)&\ge57,\\
C(22,14,7)&\ge90,& C(23,15,8)&\ge138.
\end{aligned}
$$

**Proof.** Set $L_0=12$ by the lower half of Theorem 1. At step
$s=1,\ldots,5$, a point link has parameters $(17+s,9+s,2+s)$, exactly
those of the preceding step. Theorem 10 applies, retaining each ceiling:

$$
L_s=\left\lceil\frac{(18+s)L_{s-1}}{10+s}\right\rceil.
$$

| $s$ | Parameter | Exact fraction | Division with remainder | $L_s$ |
|---:|---|---|---|---:|
| 0 | (18,10,3) | structural lower seed | — | 12 |
| 1 | (19,11,4) | $19\cdot12/11=228/11$ | $20+8/11$ | 21 |
| 2 | (20,12,5) | $20\cdot21/12=420/12$ | 35 | 35 |
| 3 | (21,13,6) | $21\cdot35/13=735/13$ | $56+7/13$ | 57 |
| 4 | (22,14,7) | $22\cdot57/14=1254/14$ | $89+8/14$ | 90 |
| 5 | (23,15,8) | $23\cdot90/15=2070/15$ | 138 | 138 |

The sequence is 12, 21, 35, 57, 90, 138. ∎

Every entry is universal over covering families and can therefore be used
in the next point link. The seed is a proved theorem, not a table assumption.
Collapsing the iteration to one subset-count ratio would give only
21, 35, 56, 88, 135; the intermediate rounding matters. No construction
attaining the five higher bounds is supplied, so these are lower bounds
rather than exact values. The [dated comparison](sources.md#dated-earlier-comparison)
and historical-priority discussion are separate from this deduction.

## Appendix A. Lean correspondence

The principal lower contract is:

```lean
theorem lower_bound_18_10_3 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 18) (hC : IsCover C 10 3) : 12 ≤ C.card
```

`CoveringDesigns.covering_number_18_10_3_on` combines arbitrary-label
attainment and the universal lower bound. Its `Fin 18` specialisation is
`covering_number_18_10_3`. The indexed lower adapter takes arbitrary finite
occurrence indices, uniformity and full triple coverage; it derives the
lower bound by taking the ordinary image family. No degree, pair or rank
assumption appears in these contracts.

Module paths below are relative to
[`lean/CoveringDesigns`](../../lean/CoveringDesigns). Declarations in
`C18_10_3` modules use namespace `CoveringDesigns.C18_10_3` unless stated
otherwise.

| Mathematical statement | Lean module and declarations |
|---|---|
| Theorem 1, lower bound and repeated-occurrence adapter | [`C18_10_3.LowerBound`](../../lean/CoveringDesigns/C18_10_3/LowerBound.lean): `CoveringDesigns.lower_bound_18_10_3`, `CoveringDesigns.indexed_lower_bound_18_10_3` |
| Theorem 1, exactness | [`C18_10_3`](../../lean/CoveringDesigns/C18_10_3.lean): `CoveringDesigns.covering_number_18_10_3_on`, `CoveringDesigns.covering_number_18_10_3` |
| Lemma 2, link floor and profiles | [`C18_10_3.Incidence`](../../lean/CoveringDesigns/C18_10_3/Incidence.lean): `lower_bound_17_9_2`, `degree_ge_six`, `pair_ge_two`, `eleven_le_card`, `degree_excess_sum`, `degree_profiles` |
| Lemma 3, local capacities and fibre rounding | [`C18_10_3.SaturatedLocal`](../../lean/CoveringDesigns/C18_10_3/SaturatedLocal.lean): `saturated_local` |
| Lemma 3, matching and packing | [`C18_10_3.SaturatedMatching`](../../lean/CoveringDesigns/C18_10_3/SaturatedMatching.lean): `all_other_edges_cross`, `supporting_index_unique`, `no_saturated_pair`, `pair_ge_three` |
| Lemma 4, actual incidence and rank estimate | [`C18_10_3.LowRows`](../../lean/CoveringDesigns/C18_10_3/LowRows.lean): `row_binary`, `row_sum`, `row_gram`, `row_balance`, `deficit_total_identity`, `low_zero_bound` |
| Lemma 5, high-point cases | [`C18_10_3.RankCases`](../../lean/CoveringDesigns/C18_10_3/RankCases.lean): `one_high_impossible`, `high_seven_deficits`, `high_pair_eq_six` |
| Lemma 6, full equality and actual pairing | [`C18_10_3.Core`](../../lean/CoveringDesigns/C18_10_3/Core.lean): `core_equality`, `core_pairing` |
| Lemmas 7–8, finite support obstruction | [`Foundations.PairedSupportObstruction`](../../lean/CoveringDesigns/Foundations/PairedSupportObstruction.lean): `CoveringDesigns.SupportObstruction.exceptional_count`, `CoveringDesigns.SupportObstruction.paired_support_obstruction` |
| Lemmas 7–8, derivation from covering hypotheses | [`C18_10_3.Exceptional`](../../lean/CoveringDesigns/C18_10_3/Exceptional.lean): `zero_deficit_intersections`, `two_high_impossible` |
| Proposition 9, explicit family and arbitrary labels | [`C18_10_3.Witness`](../../lean/CoveringDesigns/C18_10_3/Witness.lean): `CoveringDesigns.knownBlocks12_18_10_3`, `knownBlocks12_18_10_3_distinct`, `knownCover12_18_10_3_card`, `knownCover12_18_10_3_isCover`, `knownCover12_18_10_3_on_card`, `knownCover12_18_10_3_on_isCover`, `upper_bound_18_10_3_on` (all in `CoveringDesigns`) |

The correspondence retains the following representation details and proof
adaptations.

- Lemma 2's elementary link proof is the specialisation at $k=10$ of the
  existing [`TwoKMinusTwo.link_lower_bound`](../../lean/CoveringDesigns/TwoKMinusTwo/Incidence.lean).
  The adapter discharges its point-count and $k\ge9$ hypotheses.
- The rank estimate uses [`BoundaryRank.Nullity`](../../lean/CoveringDesigns/BoundaryRank/Nullity.lean),
  especially `two_mul_nullity_le_zero_count` and `gram_card_bound`.
  Equality is applied on the closed zero-deficit set through
  [`BoundaryRank.RestrictedEquality`](../../lean/CoveringDesigns/BoundaryRank/RestrictedEquality.lean):
  `restricted_component_pairing` and `restricted_kernel_pairing`.
- `core_pairing` returns an equivalence from
  `((Fin 5 × Bool) ⊕ Fin 6)` onto the actual low points. This proves
  exhaustiveness, disjointness and distinctness while retaining equal-support
  points separately. Equality of paired incidence rows is proved from the
  specified Gram entries, not inferred from graph pairing alone.
- The covering adapter derives the column margin in §6 from uniformity
  and that equivalence. The support obstruction uses the subtraction-free
  inclusion–exclusion identity in
  [`Foundations.SupportObstruction`](../../lean/CoveringDesigns/Foundations/SupportObstruction.lean),
  with support differences supplied by
  [`Foundations.SupportDifferences`](../../lean/CoveringDesigns/Foundations/SupportDifferences.lean).
- The general occurrence-packing inequality used in Lemma 3 is
  [`CoveringDesigns.IncidencePacking.packing`](../../lean/CoveringDesigns/Foundations/IncidencePacking.lean).
  Its two incidence assumptions are derived before application.

The public lifting import is
[`CoveringDesigns.Applications.C18103Lifts`](../../lean/CoveringDesigns/Applications/C18103Lifts.lean).
Its declarations use namespace `CoveringDesigns.Applications.C18103Lifts`.
For example, the last numerical contract is:

```lean
theorem lower_bound_23_15_8 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 23) (hC : IsCover C 15 8) : 138 ≤ C.card
```

| Mathematical statement | Lean declaration |
|---|---|
| Theorem 10, one-step link count | [`CoveringDesigns.Schoenheim.lift_lower_bound`](../../lean/CoveringDesigns/Schoenheim/LowerBound.lean) |
| Iterated ceiling recurrence | [`CoveringDesigns.Multicover.bound` and `bound_succ`](../../lean/CoveringDesigns/Multicover/Schoenheim.lean) |
| Universal seed lifted by induction | [`lower_bound`](../../lean/CoveringDesigns/Applications/C18103Lifts/LowerBound.lean) |
| All six numerical values | [`ceilings`](../../lean/CoveringDesigns/Applications/C18103Lifts/Corollaries.lean) |
| Corollary 11, C(19,11,4)≥21 | [`lower_bound_19_11_4`](../../lean/CoveringDesigns/Applications/C18103Lifts/Corollaries.lean) |
| Corollary 11, C(20,12,5)≥35 | [`lower_bound_20_12_5`](../../lean/CoveringDesigns/Applications/C18103Lifts/Corollaries.lean) |
| Corollary 11, C(21,13,6)≥57 | [`lower_bound_21_13_6`](../../lean/CoveringDesigns/Applications/C18103Lifts/Corollaries.lean) |
| Corollary 11, C(22,14,7)≥90 | [`lower_bound_22_14_7`](../../lean/CoveringDesigns/Applications/C18103Lifts/Corollaries.lean) |
| Corollary 11, C(23,15,8)≥138 | [`lower_bound_23_15_8`](../../lean/CoveringDesigns/Applications/C18103Lifts/Corollaries.lean) |

The induction proves the bound `Multicover.bound 12 (18+s) (10+s) s`
for arbitrary natural $s$, starting with the unconditional seed and using
ordinary Schönheim lifting at every successor. The parameter 12 supplies
the starting value of this recurrence; the covering premise still has
ordinary multiplicity 1. The five numerical contracts specialise to
$s=1,\ldots,5$ without a supplied seed or decidable-equality parameter.
Classical reasoning supplies decidable equality internally. Ordinary
kernel-checked `decide` proves the numerical ceiling conjunction.

## Appendix B. Reuse boundaries and verification

### Mathematical interfaces and dependencies

The restricted graph lemma assumes a closed set $Z$ of nonisolated
vertices, a real subspace vanishing outside $Z$ and alternating on graph
edges, $|Z|=2|\kappa|$, and subspace dimension at least $|\kappa|$.
It returns paired components on $Z$. The signless specialisation requires
a positive constant $\rho$, symmetric entrywise nonnegative loopless $E$,
nonnegative deficits, row balance, no edges from zero to positive deficit,
and the stated zero-count and dimension bounds. The covering application
derives these assumptions.

The core lemma uses a real matrix with 16 rows and 11 columns, natural
deficits totalling 18, row balance 3, and Gram matrix $3I+E+3J$.
Its actual-row pairing and row equality are distinct conclusions. The
finite support obstruction additionally uses actual binary supports and
the column margin of §6. These extra conditions explain why an arbitrary
matrix satisfying only the rank inequality does not imply a covering
contradiction.

The seed imports link counting, saturation geometry, signless nullity and
constant-parameter matrix results. The last supply positivity of the
constant matrix and equality of rows from Gram entries. The public exactness
entry adds the witness and relabelling. The lifting proof imports the seed's
lower proof and `Multicover.Schoenheim`; it uses the recurrence and ordinary
lifting, not the witness, a numerical C(20,11,3) lower theorem or a
higher-multiplicity covering assumption.

The separately reusable
[`BoundaryRank.SquareDuality`](../../lean/CoveringDesigns/BoundaryRank/SquareDuality.lean)
and [`C18_10_3.SquareSupport`](../../lean/CoveringDesigns/C18_10_3/SquareSupport.lean)
interfaces remain audited, but neither is imported by the public seed proof
or the lifting proof. Square extraction and column duality are not steps in
the argument above. The seed audit includes these interfaces, so its
verification closure is larger than the public proof's import closure.

### Reproducing verification

After the setup in the [shared verification guide](../../technical-details.md),
run these commands from the repository root:

```text
./covering check
./covering verify 18-10-3
./covering verify c18103-lifts
./covering audit 18-10-3
./covering audit c18103-lifts
```

`check` validates source boundaries, retained input hashes and explicit data;
it does not compile Lean. Each `verify` compiles the dependency closure and
the theorem/axiom audit. Each subsequent `audit` validates the recorded
evidence against the current inputs; it is not another compilation. Changed
proof inputs or verification runners can make an earlier record stale, in
which case a fresh verification is required before claiming current evidence.
Use `./covering verify` and `./covering audit` for the whole library.

The [seed audit](../../lean/audits/C18_10_3.lean) fixes full theorem types,
expands ordinary and indexed covering conditions, and checks transitive
axioms. The [lifting audit](../../lean/audits/C18103Lifts.lean) checks all
seven public theorem contracts and the expanded covering conditions for
the five numerical conclusions. The final covering theorems and their
expanded restatements use exactly `propext`, `Classical.choice` and
`Quot.sound`; helper theorems may use a subset. Admissions, additional
axioms, native proof assertions and external exclusion certificates are
excluded by the source and theorem audits.

The complete construction and its attribution are given in §8 and
[sources](sources.md#historical-attaining-construction). Lean contains and
verifies the explicit block list directly; neither a data checker nor a
historical source claim is a proof premise. Workflow tests and resource
controls test verification infrastructure separately from the mathematical proofs.
