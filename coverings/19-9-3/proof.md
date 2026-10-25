# C(19,9,3)=17

**Rob Gardiner, with AI assistance.**

## Abstract

We prove C(19,9,3)=17. If 16 blocks covered all triples, their minimum
point links would force 8 points with the plane structure of AG(3,2).
The other 11 points cannot complete the covering. Rade Belic's known
17-block construction gives the matching upper bound.

## Main theorem and proof outline

**Theorem.** C(19,9,3)=17.

More explicitly, if |V|=19 and blocks B_i⊆V each have size 9 and cover
every triple, then there are at least 17 blocks. A covering with 17
distinct blocks exists on every such set V.

We allow repeated block occurrences, indexed by a finite set I. Distinct
points remain distinct even when their supports coincide. This proves the
lower bound for both indexed and ordinary families.

The proof uses the included classification of (18,8,2) coverings with
7 blocks, stated in §1. Sections 2–5 force eight minimum points and
fourteen affine-plane traces. Section 6 classifies the remaining
point supports; §7 excludes their completion by two counting arguments.
Section 8 gives Belic's construction. [Sources](sources.md) records the
earlier results and construction credit; the appendix links the argument
to the Lean declarations.

## 1. The seven-block classification used here

The included [seven-block classification](../seven-block/proof.md) says
that every indexed (18,8,2) covering with seven occurrences has sixteen
points of degree three and two of degree four. Label the occurrences by
the nonzero vectors of F₂³, written 1,…,7 in binary. The degree-three
supports are the Fano lines 123,145,167,246,257,347,356. Up to relabelling,
the degree-four supports are H=2467, G=3567 (Type I), or H=G=3567
(Type II), with the fibre sizes below. This is the a=2 instance of the
included classification; no other value of a is needed.

A fibre consists of the actual points with one fixed support. The table
records its size and the intersections of each low line with H and G.

| Low line | Type I: size; H∩L, G∩L | Type II: size; H∩L=G∩L |
|---|---|---|
|123|3; 2, 3|3; 3|
|145|3; 4, 5|3; 5|
|167|2; 67, 67|2; 67|
|246|2; 246, 6|3; 6|
|257|2; 27, 57|2; 57|
|347|2; 47, 37|2; 37|
|356|2; 6, 356|1; 356|

Here “67” denotes a two-element set. Equal point supports retain their
full fibre multiplicity. The theorem applies to indexed coverings; no
block-image injectivity is an input.

## 2. Minimum points and literal trace rules

Write S_x={i:x∈B_i}, d(x)=|S_x|, μ(x,y)=|S_x∩S_y| and
τ(x,y,z)=|S_x∩S_y∩S_z|. Pair and triple claims concern distinct points.

**Lemma 1 (floors).** Every d(x)≥7 and every μ(x,y)≥3.

**Proof.** The link at x consists of d(x) indexed eight-sets covering pairs
on eighteen points. Each point of this link needs at least three
occurrences, since two residual seven-sets cannot cover seventeen partners.
Thus its incidence count is 8d(x)≥18·3=54, excluding six or fewer.
The occurrences through a parent pair must cover its seventeen other
points in seven-sets, so 7μ(x,y)≥17. ∎

Write εₓ=d(x)−7. At sixteen occurrences the degree count gives

    Σₓ εₓ = 16·9−19·7 = 11.

For each x the local count is Σᵧ≠ₓ μ(x,y)=8d(x); at a minimum point it gives
Σᵧ≠ₓ(μ(x,y)−3)=2.

Assume sixteen occurrences from now on. The excess eleven leaves at least
eight minimum points M={x:d(x)=7}. Their links are seven-block (18,8,2) coverings.
The classification in §1 gives exactly two exceptional neighbours
p_x,q_x with μ=4; all other sixteen neighbours have μ=3 and are called
ordinary.

Apply §1 at a minimum root x: the eighteen other points have their
classified supports within the actual occurrence set S_x. Comparing these
intersections at different roots gives the following literal trace rules.

1. Two different low supports meet in exactly one position; identical
   low supports meet in three. Low/low intersection two is impossible.
2. If x,y are minimum, μ(x,y)=3 and τ(x,y,u)=2, then u is exceptional
   at both roots. Moreover, at x there are exactly two such u, namely
   p_x,q_x. Both are exceptional at y, so their unordered exceptional
   pairs agree.
3. For μ(x,y)=3 with x minimum, among u∉{x,y}, exactly either two points have τ(x,y,u)=3
   and none has τ=2, or one point has τ=3 and two have τ=2. The latter
   occurs precisely on the three size-two low lines meeting both H,G in
   two positions. Call these three lines the **middle lines** for this proof.
4. If x,y are minimum and μ(x,y)=4, their link types agree. Indeed Type I
   permits no third point with τ(x,y,u)=4. Type II permits exactly one,
   its other exceptional neighbour. The same count viewed at y proves
   type agreement, and in Type II identifies that same third point.

Each high four-support contains a unique Fano line. In Type I that line
has fibre size two and the two high supports contain different lines;
in Type II their common contained line has fibre size one. These lines
are different from all three middle lines.

## 3. Three minimum roots cannot have triple multiplicity three

**Lemma 2 (three-root compatibility).** In the hypothetical sixteen-block
cover, no triple of minimum points has multiplicity three.

### 3.1 Three mutually ordinary roots

First suppose x,y,z are minimum with all three pair multiplicities three
and with T=S_x∩S_y∩S_z of size three. Each pair intersection is T. Hence
their supports partition the occurrence positions into

    T (size 3), X=S_x\T (4), Y=S_y\T (4), Z=S_z\T (4), N (1).   (1)

If another point w contained T, then, writing n_w=|S_w∩N|≤1,

    d(w)=3+Σ_{r∈{x,y,z}}(μ(r,w)−3)+n_w≤7.

The floor seven would make w minimum, all three displayed excesses one,
and n_w=1. This gives w three exceptional neighbours, a contradiction.
So the intersection of the three actual blocks indexed by T is exactly
{x,y,z}.

Rule 3 now forces the second alternative at each root: there are precisely
two points p,q occurring in two of the positions of T, and all fourteen
remaining points occur in one. These are the same actual points in all
three links. Rule 2 makes p,q exceptional at all three roots; every other
point is ordinary there. Each of the sixteen residual points therefore
occurs in exactly two positions of each of X,Y,Z. For p,q this is 4−2;
for the other fourteen it is 3−1. Consequently

    d(p)=8+n_p, d(q)=8+n_q;
    d(w)=7+n_w for the other fourteen points.                    (2)

In particular p,q are not minimum. A minimum residual point avoids N.

Group the fourteen ordinary residual points by their unique position in T.
At each of the three roots, the two other Fano lines through a given
position of T cut its four outside positions into a complementary pair
of two-sets. Thus each point in a group chooses one of two complementary
two-sets in each of X,Y,Z. For two points in the same group, one of which
is minimum, their pair multiplicity is

    1+2·(number of equal two-set choices among X,Y,Z).             (3)

The minimum point avoids N. The floor three and upper four force exactly
one equal choice. If the group has size s and a minimum point w lies in
fibre sizes g_X(w),g_Y(w),g_Z(w), summing agreement with its s−1 companions
gives the **exact, non-reused count**

    Σ_{D∈{X,Y,Z}}(g_D(w)−1)=s−1.                                (4)

Each companion is counted once, at its unique agreeing choice.

There are two possibilities for the actual two-set traces of p,q on T.

**Equal traces.** Name T={a,b,c}, with both traces {b,c}. The ordinary
group sizes are 6,4,4. In each outside group X,Y,Z the a-group splits 3+3.
A minimum point there would have six agreements with only five companions
in (4), impossible. All remaining minimum residual points lie in the
b- or c-group.

At each root, the outside two-sets of p,q belong to one of the b,c
matchings. For Type I they are complementary, and all four-point ordinary
groups split 2+2. For Type II they coincide; in that matching the ordinary
split is 1+3, with the singleton fibre on the same two-set as p,q; the
other four-point group splits 2+2. These facts are read from the complete
table above, allowing either b or c to be the distinguished matching.

Suppose a minimum w lies in a four-point group. Equation (4) says
Σ_D(g_D(w)−2)=0. For the Type-II groups in its own matching, a singleton
choice contributes −1 and a three-point choice +1; all other choices
contribute zero. Its intersections with p and q sum to

    μ(w,p)+μ(w,q)=8−2Σ_D(g_D(w)−2)=8.

Both are at most four, hence both equal four. If r_b counts the outside
groups whose p,q matching is b, parity gives, for w in the b-group,
μ(w,p)≡1+(3−r_b)≡r_b (mod 2). Thus r_b must be even. Similarly a
minimum in the c-group requires r_c even, but r_b+r_c=3. Both groups
cannot contain a minimum point. There are at most four residual minima,
and hence at most seven minima altogether, contradicting the minimum count in §2.

**Distinct traces.** Name them {a,c} for p and {b,c} for q. Only Type I
is possible. The ordinary group sizes are 5,5,4. At every root each
five-point group splits 3+2; p's outside two-set is the size-two choice
in the a-group, and q's is the size-two choice in the b-group. If w in
the a-group were minimum, (4) would give Σg_D(w)=7, so it takes a
three-point choice once and a two-point choice twice. Then μ(w,p)=1+4=5,
impossible. Likewise no b-group point is minimum. Again only the
four-point group can contribute residual minima, giving at most seven.

This excludes mutually ordinary minimum roots with τ=3.

### 3.2 The remaining excess-edge pattern

If a minimum triple with τ=3 had two or three excess edges, one vertex
would have both others exceptional, forcing τ=2 or 4. Thus it remains
to consider μ(x,y)=μ(x,z)=3, μ(y,z)=4, τ(x,y,z)=3.

Put T=S_x∩S_y∩S_z. Outside T, X=S_x\T is disjoint from Y=S_y\T and
Z=S_z\T, while |Y∩Z|=1. All three sets have size four; their union has
size eleven. Exactly two positions N lie outside all three root supports.

By Rule 4 the y,z links have the same type. In Type I, viewing x as a
low point in the y-link, the exceptional support of z contains its line.
That line has size-two fibre, so there is another point w on it. The same
literal T is the line in the z-link, giving the same w (Rule 3 says
exactly two third points have multiplicity three with x,y). Thus w
contains T, is ordinary to y,z, and meets X in at most one position.
Outside T it avoids Y∪Z, so d(w)≤3+1+2=6, impossible.

In Type II the unique other exceptional neighbour w of y is also the
other exceptional neighbour of z, by Rule 4. It contains all four
positions of S_y∩S_z. Its intersections with Y,Z are their one common
position; it meets X in at most one, and N in at most two. Hence d(w)≤7.
Equality is necessary and would give μ(w,x)=μ(w,y)=μ(w,z)=4 and d(w)=7,
again three exceptional neighbours at a minimum point. This finishes
Lemma 2. ∎

## 4. No excess edge joins minimum points

**Lemma 3.** Minimum points are pairwise ordinary. There are exactly eight.

**Proof.** Suppose x is minimum and an exceptional neighbour y is minimum.
In either link type, the four-support of y meets three low lines once,
three twice and its unique contained line three times. Lemma 2 puts at
most one minimum point on each low line and none on the contained line.
At most one minimum low point can meet y's support twice: each such
point u has μ(x,u)=3 and τ(x,u,y)=2. Rule 2, applied to the ordinary
minimum pair x,u, makes y exceptional at u and hence u exceptional at y.
Since x is already exceptional at y, two such u would give y three
exceptional neighbours.

There are therefore at most three minimum low points of the first kind
and one of the second. Adding at most two exceptional points gives at
most six minimum points other than x, contrary to |M|≥8. The count applies
to both link types.

Thus no such edge exists. At any minimum x all other minimum points now
occupy distinct low lines, of which there are seven. Hence |M|≤8, and
the lower count gives equality. ∎

The degree excess eleven then forces the other eleven points all to have
degree eight. All triples of minimum points have multiplicity one: their local supports
are different Fano lines, and Lemma 2 excluded coincidence.

## 5. The actual affine plane positions

**Lemma 4.** Fourteen actual occurrences meet M in the fourteen affine
planes of AG(3,2), one per plane. The other two occurrences avoid M.

**Proof.** At each x∈M the other seven minimum points occupy every Fano
line once. Each of its seven positions therefore contains exactly three
other minimum points. Every block meeting M meets it in four points.
The 56 minimum incidences give fourteen such occurrences. Every triple
of M lies in one, and different occurrences have different four-point
traces, since otherwise a minimum triple repeats.

For completeness, these fourteen traces form the unique 3-(8,4,1) system.
Fix a trace A. Besides A, no trace meets it in three points. Every pair
of A belongs to three traces, so twelve others meet A in two points.
The four point degrees seven leave no trace meeting A in one point;
the remaining trace is its complement. Thus traces come in complementary
pairs. At a fixed point 0, the seven traces through 0 are the Fano
triples on the other seven points, with 0 adjoined. Label those points by
the nonzero vectors of F₂³ so the triples are {u,v,u+v}. Their complements
are the seven other affine planes. This gives the asserted coordinates.

At every other minimum root, the seven pair intersections are all the
Fano lines in both descriptions, so the coordinates agree on the actual
occurrence positions. ∎

Write the fourteen positions as P(n,b)={x∈F₂³:n·x=b}, with nonzero
n∈F₂³ and b∈{0,1}. Write E₀,E₁ for the two occurrences avoiding M.
Each plane block has five nonminimum points and each E_i has nine.
The seven directions n themselves carry their usual Fano lines.

## 6. Every nonminimum column has one of three simple forms

**Lemma 5.** For a degree-eight point u outside M, exactly one occurs:

| Form | Plane occurrences through u | Empty-M occurrences through u | Minimum exceptions |
|---|---|---|---|
| A | both planes in each direction of a Fano line L | both E₀,E₁ | none |
| B | both planes in each direction of L, plus P(n,b), n∉L | exactly one E_i | the four points of P(n,b) |
| C | both planes in four directions H | neither | all eight |

**Proof.** If j is the number of E_i containing u, then u uses 8−j
plane positions. Summing μ(x,u)=3 or 4 over M gives
24+e(u)=4(8−j), so e(u)=8−4j. For j=0 or 2 all eight local degrees
are constant (four or three); for j=1 they split four of each.

For each direction n put χ_n(x)=(-1)^(n·x). These seven functions and the
constant function are orthogonal under averaging on F₂³: a nonconstant character
has four values +1 and four −1, and χ_nχ_m=χ_(n+m).
If f(x) counts the selected planes through x and N=8−j, then
2f−N is the sum of ±χ_n over the directions with exactly one selected
plane. Constant f therefore allows no single direction. When j=1,
2f−7 takes values ±1; its mean square is one, so orthogonality forces
exactly one single direction. Thus the column uses either three complete
parallel classes, three plus one plane, or four complete classes.

At a root with local degree three, the selected directions form a Fano
line by §1 and Lemma 4. This identifies the three complete directions
in forms A and B; in B choose a root off its single added plane. No
further restriction on the four directions in C is needed. ∎

## 7. The shorter completion obstruction

**Lemma 6.** Eleven actual points of forms A, B and C cannot fill fourteen
plane positions of size five and two exceptional positions of size nine
while covering every triple of distinct points. The exceptional block
images may coincide, and the four directions of a C point are arbitrary.

### 7.1 Counts and line weights

Let A,B,C count the three forms. Counting points and exceptional incidences gives

    A+B+C=11,     2A+B=18,     B+2C=4.                         (5)

Thus C≤2. Let w_L count A and B points with base line L, and put
f_d=Σ_{L∋d}w_L. Then Σw=11−C and f_d≤5. Since a line meets itself
three times and every other line once,

    2w_L+11−C = Σ_{d∈L}f_d ≤ 15,
    w_L ≤ floor((4+C)/2).                                  (6)

These weights count actual points, including distinct points with equal supports.

### 7.2 One capacity argument excludes C>0

Choose a C point c with direction set H. Of the three directions outside
H, at least one, d, is not a B extra direction: there are only B=4−2C≤2
B points. At either plane position in direction d, c is absent, at most
C−1 other C points occur, and no B extra occurs. Hence f_d≥6−C.

All A points with bases through d have the same base. Otherwise two
have distinct base lines meeting only at d; their triple with c has
no common plane position, because d∉H, and no exceptional position,
because c avoids both. The three actual points are distinct by their
forms or different bases.

Their number is therefore at most one line weight; if there are none,
the same upper bound holds. Adding at most B base points of form B gives

    6−C ≤ f_d ≤ floor((4+C)/2)+4−2C.

For C=1 this says 5≤4; for C=2 it says 4≤3. Thus C=0, A=7 and B=4.

### 7.3 The four B points

With C=0, the two plane rows in each direction have the same base
contribution. Their B-extra counts consequently agree; call the common
value m_d. Four extras give Σm=2, and f_d=5−m_d. Equation (6) gives

    2w_L = 4−Σ_{d∈L}m_d.                                  (7)

If two distinct directions carried m=1, a line through exactly one would
make the right side odd. Thus m_n=2 for one direction n and is zero
elsewhere. All B extras have direction n, every B base avoids n, and
w_L is one through n and two off n.

Each exceptional position contains the seven A points and two B points.
Choose B points x,y in different exceptional positions. They are distinct
because a B point uses exactly one such position. If their base lines
L,M differ, let L∩M={d}; then d≠n. Every common plane position has
direction d or n, regardless of their extra sides. They have no common
exceptional position.

Exactly two Fano lines avoid both d and n: three pass through each and
one through both. Each avoiding line has weight two, giving four actual
base points in disjoint line fibres. Neither x nor y is among them,
since their bases contain d. Only two other B points exist, so one of
the four is an A point z. Its base avoids d and n; the distinct triple
x,y,z is uncovered.

Therefore every cross-exceptional B pair has the same base. Since both
exceptional positions contain B points, all four bases agree. That line
has weight at least four, contradicting its weight at most two. ∎

## 8. Exactness and attainment

The preceding lemmas rule out 16 block occurrences. A smaller covering
must contain a block, since it covers every triple of the 19 points.
Repeating that block would give 16 occurrences without changing coverage
or block size. This is also impossible, so every covering has at least
17 blocks.

Rade Belic's historical construction is the following family on {1,…,19};
each row is one block.

```text
1 2 3 4 5 6 11 12 19
1 2 3 4 11 12 13 18 19
1 2 4 5 6 11 12 13 18
1 2 4 7 8 12 13 14 16
1 2 4 9 10 12 13 15 17
1 3 4 6 7 10 15 16 18
1 3 4 6 8 9 14 17 18
1 4 5 7 9 11 16 17 19
1 4 5 8 10 11 14 15 19
2 3 5 6 7 9 12 14 15
2 3 5 6 8 10 12 16 17
2 7 10 11 12 14 17 18 19
2 8 9 11 12 15 16 18 19
3 5 7 8 9 10 13 17 18
3 6 7 8 11 13 15 17 19
3 6 9 10 11 13 14 16 19
5 6 13 14 15 16 17 18 19
```

These 17 distinct blocks each have size 9 and cover all 969 triples. The
[retained block list](../../data/c1993-belic-witness.json)
and [Lean witness](../../lean/CoveringDesigns/C19_9_3/Witness.lean) give the same
family, with labels shifted by 1 in Lean. Relabelling gives a covering
on any set of 19 points. Together with the lower bound, this proves
C(19,9,3)=17. ∎

## Appendix A. Lean correspondence and verification

All names below are in `CoveringDesigns`, with `C19_9_3` indicated where
needed. The public entry is `CoveringDesigns.C19_9_3`.

| Proof step | Declaration or module |
|---|---|
| Floors, minimum count (§2) | `C19_9_3.pair_floor`, `degree_floor`, `eight_minimum_points` |
| Seven-block link classification (§1) | `SevenBlock.classification_ge_two`, at a=2 |
| Trace agreement and three-root exclusion (§§2–3) | `C19_9_3.literal_link_trace`, `literal_link_pair_trace`, `no_minimum_triple_three` |
| Eight minimum points (§4) | `C19_9_3.minimum_pair_ordinary`, `minimum_points_card`, `nonminimum_degree` |
| Affine recognition (§5) | `C19_9_3.actual_affine_configuration` |
| Remaining supports (§6) | `C19_9_3.actual_column_forms` |
| Line weights and completion obstruction (§7) | `SevenBlock.fano_incidence_identity`; `C19_9_3.WeakCompletion`, `actual_weak_completion`, `weak_completion_impossible`; assembled by `no_sixteen` |
| Padding and indexed lower bound (§8) | `IndexedPadding.lower_of_fixed_exclusion`, `C19_9_3.seventeen_le_card` |
| Attainment (§8) | `knownCover17_19_9_3_isCover`, `upper_bound_19_9_3_on` |
| Arbitrary-label exactness | `covering_number_19_9_3_on` |

The lower branch uses `SevenBlock.Core` at a=2, indexed counting, literal
link agreement and character orthogonality. It imports neither the
independent fifteen-block rank proof nor the a=1 Stanton adapter.
`WeakCompletion` assumes the three displayed forms, the two row sizes
and coverage of distinct triples; it imposes no distinctness of point
supports or exceptional block images, and no line inside a C support.
The adapter discards the stronger C conclusion of `actual_column_forms`.
The final covering contracts require only cardinality, uniformity and
coverage. The witness remains independent of the lower branch.

The focused C19 audit additionally compiles and checks the retained older
completion and fifteen-block rank results through separate verification
roots. Their full contracts remain included; they are not premises of the
shorter proof above. The supporting account's general core and all-a
Stanton adapter have their own complete audits.

Lean checks the literal construction by kernel reduction. Separate checks
connect it to the preserved data via [inputs.json](inputs.json); the file
parser and hashes are not proof premises. The final theorems use only
`propext`, `Classical.choice` and `Quot.sound`. The
[shared verification guide](../../technical-details.md) explains the commands
`./covering check`, `./covering verify 19-9-3` and `./covering audit 19-9-3`.
