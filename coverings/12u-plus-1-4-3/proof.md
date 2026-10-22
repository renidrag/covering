# Exact values for $C(12u+1,4,3)$, $1\le u\le8$

## Abstract

We reconstruct optimal ordinary quadruple coverings on 37, 49, 61, 73,
85 and 97 points from one conditional construction. The construction uses
two exact group-divisible designs, a 78-block covering on 13 points, and
a one-factorisation of the complete graph on six points. It retains actual
blocks and their labels. Its four classes attain the iterated Schönheim
lower bound. Small finite base designs and a shared substitution theorem
discharge every seed obligation in the six applications. A lossless external
projection of the distributed files is connected to these same labelled
families by Lean equalities; the conversion itself is not a verified JSON
parser. The existing thirteen-point filling and a retained historical
600-block twenty-five-point witness complete the finite range. For every
integer 4≤n<100 with n≡1 (mod 12), an actual ordinary family attains
n(n−1)²/24, and every such covering has at least that many distinct blocks.
The quotient is natural-number division, with divisibility proved explicitly.

These exact values were proved in earlier work. This is a reconstruction
and formalisation, with smaller constructions at the original six orders
than the dated LJCR snapshot specified in [sources.md](sources.md), not a
claim of new covering numbers or global priority for explicit lists.

## 1. Points and input contracts

Fix an integer \(u\ge3\). Set
\[
 Q=[u]\times[2],\quad X=Q\times[6],\quad V=X\cup\{\infty\}.
\]
The six-point groups are the fibres of \(X\to Q\); the twelve-point holes
are the fibres of \(X\to[u]\). A set is transverse to a partition when
it meets each part in at most one point. All block families are finite
sets, so their cardinalities count distinct blocks.

The four inputs are:

1. A family \(H\) of transverse quadruples on \(X\), in which every
   triple transverse to the six-point groups belongs to exactly one block.
2. A family \(G\) of triples transverse to the holes, in which every
   pair from different holes belongs to exactly one block.
3. An actual family \(L\) of 78 distinct quadruples covering every triple
   on \(([2]\times[6])\cup\{\infty\}\).
4. Five families \(F_r\) of pairs on \([6]\). Each \(F_r\) partitions
   the six points, and every pair belongs to exactly one \(F_r\).

The input families need no common symmetry, origin, automorphism or alignment.
The only identifications are the explicit product coordinates above and the
chosen common indexing of the five matchings. The same matching is used
on both six-point groups in the fourth class.

### Lemma 1 (seed cardinalities)

The contracts imply
\[
 |H|=54\binom{2u}{3},\qquad |G|=24u(u-1),\qquad |F_r|=3.
\]

Indeed, the number of transverse \(t\)-sets in \(m\) equal groups of
size \(w\) is \(\binom mtw^t\): choose the groups, then one point in
each. Exact incidence gives \(\binom kt |C|\) equal to that number.
Use \((m,w,k,t)=(2u,6,4,3)\) and \((u,12,3,2)\).
The partition condition gives \(2|F_r|=6\).

## 2. The construction

Embed \(H\) in \(V\) as class A. For each triple of \(G\), adjoin
\(\infty\) to obtain class B. In each hole together with \(\infty\),
place a copy of \(L\), giving class C. For class D, choose two different
holes \(h<k\), one six-point group in each, a matching index \(r\), and
one pair from each copy of \(F_r\); take the union of those two pairs.
Let \(\mathcal C=A\cup B\cup C\cup D\).

### Lemma 2 (uniformity and coverage)

Every member of \(\mathcal C\) has four distinct points, and every
triple of \(V\) belongs to a member of \(\mathcal C\).

For uniformity, the embeddings in A and C are injective, \(\infty\)
is absent from every GDD triple, and the two pairs in D lie in different
holes. For coverage, consider a triple containing \(\infty\). If its
other two points lie in one hole, use C; otherwise use G and hence B.
For a triple avoiding \(\infty\), use C if all points lie in one hole.
If its three six-point groups are distinct, use H and hence A. In the
remaining case two points lie in one six-point group and the third lies
in a different hole. Their pair determines a matching index; the unique
pair through the third point in that matching gives a block in D.
This exhausts all cases without any relation between H and G.

### Lemma 3 (budgets)

The four finite images have respective upper bounds
\[
 54\binom{2u}{3},\quad24u(u-1),\quad78u,\quad90u(u-1).
\]
For D there are \(\binom u2\) hole pairs, four choices of sides,
five matching indices and nine pair choices, giving
\(180\binom u2=90u(u-1)\). The other bounds follow immediately from
Lemma 1 and the number of filling copies. Their sum is
\[
 54\binom{2u}{3}+24u(u-1)+78u+90u(u-1)
   =6u^2(12u+1).
\]

## 3. Lower bound and sharpness

### Lemma 4 (Schönheim ceilings)

For \(v=12u+1\), the three successive ceilings are
\[
 \left\lceil\frac{v-2}{2}\right\rceil=6u,\qquad
 \left\lceil\frac{v-1}{3}\,6u\right\rceil=24u^2,\qquad
 \left\lceil\frac v4\,24u^2\right\rceil=6u^2(12u+1).
\]
The library's iterated Schönheim theorem therefore gives this last quantity
as a lower bound for every ordinary \((v,4,3)\) covering on any finite
point type of cardinality \(v\).

### Theorem 5 (conditional assembly)

Under the contracts in §1, \(\mathcal C\) is an ordinary covering with
exactly \(6u^2(12u+1)\) distinct blocks. Each class attains its stated
budget; all four source maps are injective and all six pairs of classes
are disjoint.

By Lemma 2, the lower bound applies to the actual union. Lemma 3 bounds
that union above by precisely the same number. Equality forces equality
at every class and union-cardinality inequality. Equality in the image
bound gives injectivity of each finite source map; equality in the union
bound gives disjointness. This sharpness argument proves distinctness
and separation without silently deduplicating an occurrence budget.

This is a directly proved even-case adaptation of the Hartman–Mills–Mullin
assembly. The domain of their cited odd-case theorem is not enlarged by
invocation; the coverage and counting arguments above are proved here.

## 4. Discharging the six seed pairs

### Lemma 6 (substitution)

Suppose a master family has unique coverage of its transverse \(t\)-sets.
For each master block, suppose a local family lies above that block, has
the required uniformity and transversality, and uniquely covers each
transverse \(t\)-set whose projection is contained in the block.
Then the union of the local families has exact transverse \(t\)-coverage.

Project a required set. Its unique master block selects the patch, and the
unique local incidence selects its block. Conversely any block covering the
set projects into that same master block, so both uniqueness statements
apply. In the constant-fibre specialisation, local labels are sent to the
increasingly ordered master block and the fibre coordinate is unchanged.
This is one theorem for binary inflation, H-design substitution, Latin
inflation and GDD substitution.

The formalisation uses the following small finite bases. Their required
incidences are checked in the kernel, independently of the selector tables
used to accelerate evaluation. In particular, the deletion-derived small
GDDs are checked directly here; the earlier derivation/deletion histories
remain provenance, rather than additional assumptions in the proof.

| u | H route | GDD route |
| ---: | --- | --- |
| 3 | Hanani H(6,3,4,3), binary H(4,2,4,3) substitution | Explicit retained cyclic 12-by-12 Latin triples |
| 4 | SQS(8), H(4,6,4,3) substitution | Checked 3-GDD \(2^4\), weight-six Latin inflation |
| 5 | Retained SQS(10), H(4,6,4,3) substitution | Checked 4-GDD \(3^5\), substitution of 3-GDD \(4^4\) |
| 6 | Mixed \(\{4,6\}\) 3-wise design on 12 points, H(4,6) and H(6,6) substitution | Checked 3-GDD \(2^6\), weight-six Latin inflation |
| 7 | Retained SQS(14), H(4,6,4,3) substitution | Checked 3-GDD \(2^7\), weight-six Latin inflation |
| 8 | Affine SQS(16), H(4,6,4,3) substitution | Checked 4-GDD \(3^8\), substitution of 3-GDD \(4^4\) |

The H(4,6) base uses the retained coordinate-sum list. The binary and
weight-six Latin lists are explicit small coordinate-sum lists. The mixed
12-point master has blocks of sizes four and six, so both required patch
contracts are supplied. In the GDD routes, the expanded hole sizes are
\(2\cdot6=12\) or \(3\cdot4=12\). Labels are respectively \(6x+a\)
and \(4x+a\). The 13-point filling and the five six-point matchings are
also checked in Lean. No literature-existence or external-validity premise
survives in any application.

## 5. Applications and actual files

Theorem 5 and Lemma 4 give
\[
 C(37,4,3)=1998,\ C(49,4,3)=4704,\ C(61,4,3)=9150,
\]
\[
 C(73,4,3)=15768,\ C(85,4,3)=24990,\ C(97,4,3)=37248.
\]
The general assembly remains conditional. No all-order seed-existence
statement is asserted.

The explicit public label map is
\[
 ((h,b),i)\longmapsto12h+6b+i,\qquad\infty\longmapsto12u.
\]
It is a bijection to \(\operatorname{Fin}(12u+1)\). Arbitrary finite
labels are handled by the existing relabelling interface, preserving the
actual family cardinality and its covering property.

The six authoritative JSON files are preserved unchanged. The input manifest
identifies their complete bytes by path and SHA256. The external projection
reads their `blocks` arrays, checks integer bounds and distinctness, and
reorders the actual rows into small named Lean literals. Its independent
boundary checker reparses those literals and compares the complete block
multisets with the JSON. This checks losslessness at the conversion boundary;
it is not a formal proof about a JSON parser.

Lean then proves each literal row piece equal to the relevant structural
piece, combines those equalities into an equality of row lists, and applies
`List.toFinset`. The resulting theorem identifies the exact projected family
with the explicitly labelled assembly. Thus coverage and exact cardinality
apply to the distributed blocks, not merely to some isomorphic optimal design.
Original file ordering and metadata are outside the mathematical family;
point labels are unchanged.

Deterministic regeneration checks, independent literal parsing, pinned input
hashes and verification fingerprints detect changed inputs and stale
projections. These integrity checks supplement the kernel-checked family
equality and never substitute for it.

## 6. The two small cases and the finite range

### Lemma 7 (the thirteen- and twenty-five-point base cases)

The exact values are \(C(13,4,3)=78\) and \(C(25,4,3)=600\), for
ordinary families on arbitrary finite types of the indicated cardinality.

Apply the general Schönheim recurrence with all three intermediate ceilings:

| n | First ceiling | Second ceiling | Third ceiling |
| ---: | ---: | ---: | ---: |
| 13 | ⌈11/2⌉ = 6 | ⌈12·6/3⌉ = 24 | ⌈13·24/4⌉ = 78 |
| 25 | ⌈23/2⌉ = 12 | ⌈24·12/3⌉ = 96 | ⌈25·96/4⌉ = 600 |

These give universal lower bounds. For thirteen points, use exactly
`SeedData.Filling.blocks`, whose existing `valid` and `size` theorems
prove coverage and 78 distinct blocks. No new copy or repeated finite check
is needed. For twenty-five points, the recovered list has 600 rows on
`Fin 25`. Each row's size and every triple's containment in its selected
row are checked by kernel reduction, using the existing selector soundness
interface. Splitting the check by the least point of a triple bounds
compilation cost without weakening the complete coverage obligation. The
selector indices are untrusted hints; Lean checks the resulting incidences.
The actual row-set has at most 600 members by `List.toFinset_card_le`.
The independent lower bound applied to its proved coverage gives at least
600, hence exactly 600 distinct blocks. No external validity claim is a
premise. The usual relabelling equivalence supplies arbitrary finite labels.

These are separate base cases. The general assembly and its arithmetic
retain u≥3. At u=2 the required GDD seed would have to cover pairs between
two holes by triples meeting three different holes, which is impossible.
Thus neither small result is obtained by weakening that seed contract.

### Theorem 8 (complete admissible finite range)

Let n be a natural number with 4≤n<100 and n%12=1, and let α be any finite
point type with |α|=n. Then 24 divides n(n−1)², and

\[
 (\exists\mathcal C\subseteq\tbinom{\alpha}{4},\ 
   \mathcal C\text{ covers every triple and }
   |\mathcal C|=n(n-1)^2/24)
\]
\[
 \text{and}\quad
 \forall\mathcal C\subseteq\tbinom{\alpha}{4},\ 
   \mathcal C\text{ covers every triple}\ \Longrightarrow
   n(n-1)^2/24\le|\mathcal C|.
\]

The conditions on n are equivalent to n being one of
13,25,37,49,61,73,85,97. Indeed n=12q+1, and the bounds force 1≤q≤8;
conversely each listed order satisfies all three conditions. This exhausts
the cases and excludes n=1 through ordinary admissibility. Divisibility
and the exact natural quotients are checked for those same eight cases.
Lemma 7 supplies the first two exactness statements; §5 supplies the six
unchanged assembly applications. Their values are respectively
78,600,1998,4704,9150,15768,24990,37248. Combining the cases proves the
stated arbitrary-label exactness. No seed, rank, catalogue or external
checker premise remains. The conditional assembly still supplies no
all-order seed-existence theorem.

### Actual-file correspondence for the base cases

For thirteen points, the authoritative JSON is the preserved
[78-block filling](../../data/quadruple-assembly/witnesses/blocks-13-4-3-78.json).
Its unchanged literal projection is `SeedData.Filling.rows` and the named
attaining family satisfies
`knownCover78_13_4_3 = SeedData.Filling.rows.toFinset` by reflexivity.
The independent boundary check now explicitly checks the complete
`blocks := rows.toFinset` declaration as well as all literal rows and joins.

For twenty-five points, the original [zstd artifact](../../data/quadruple-assembly/C-25-4-3.blocks.zst)
contains 2,400 uint8 bytes, row-major, with one-based labels. Subtracting
one from each entry, sorting each row and sorting all rows produces the
[normalized witness](../../data/quadruple-assembly/blocks-25-4-3-600.json).
The original point and block order remains recoverable from the unchanged
compressed bytes. Original and raw digests and copied provenance records
are pinned in the [input manifest](inputs.json). The explicit bijection is
j↦j−1 from {1,…,25} to {0,…,24}; no other point permutation is used.

`WitnessData.V25.Data` contains the deterministic literal projection of
those actual normalized blocks. Lean checks coverage and cardinality of
`WitnessData.V25.blocks`. The public equality
`knownCover600_25_4_3 = WitnessData.V25.rows.toFinset` identifies the
attaining family with precisely those literal blocks. Independent
transcription checks compare full multisets across original decompression,
normalization and projection; deterministic regeneration detects a stale
projection. Independent incidence enumeration also checks all 2,300 triples.
The mathematical theorem concerns the literal family. The external parsers,
compressed format and JSON metadata are not formalised, and hashes do not
substitute for the mathematical proof.

## Appendix: Lean reading route

The coherent entry point is `CoveringDesigns.QuadrupleAssembly`.
The supported structural contracts are `GroupDesign`, `HSeed`, `GDDSeed`,
`Factors`, `assembly_optimal`, `class_budgets`, `assembly_sharp`,
`sources_injective`, `classes_disjoint`, `ceilings` and `lower_bound`.
`productSubstitute_valid` is the shared seed-composition interface.
The six `WitnessData.Vv.correspondence` theorems identify the distributed
families; `WitnessData.Vv.optimal` gives their covering and cardinality.
The `covering_number_v_4_3_on` and `covering_number_v_4_3` declarations
provide the usual arbitrary-label and standard-label exactness contracts
for all eight values. The added declarations are mapped below; the six
assembly modules and their mathematical statements are unchanged.

| Mathematical statement | Lean declaration (under `CoveringDesigns`) |
| --- | --- |
| Lemma 7, retained ceilings | `QuadrupleAssembly.ceilings_13`, `ceilings_25`, `schoenheim_13`, `schoenheim_25` |
| Lemma 7, universal lower bounds | `lower_bound_13_4_3`, `lower_bound_25_4_3` |
| Actual small-case families | `knownCover78_13_4_3`, `knownCover600_25_4_3` and their `_optimal`, `_on_optimal` theorems |
| Actual literal-family identities | `knownCover78_13_4_3_correspondence`, `knownCover600_25_4_3_correspondence` |
| Lemma 7, arbitrary labels / Fin labels | `covering_number_13_4_3_on`, `covering_number_25_4_3_on`, and the variants without `_on` |
| Theorem 8, exact exhaustion | `QuadrupleAssembly.admissible_below_100_iff` |
| Theorem 8, exact division | `QuadrupleAssembly.formula_divisible_below_100` |
| Theorem 8, arbitrary labels / Fin labels | `covering_number_one_mod_twelve_below_100_on`, `covering_number_one_mod_twelve_below_100` |

`SmallCases` imports the unchanged filling, the new `WitnessData.V25`,
relabelling and general Schönheim. `FiniteRange` combines it with the
unchanged `Applications`. The whole component retains its independence from
other covering-result components except Schönheim. The audit checks full
types, explicit ordinary-family conditions, all public identities and
transitive axioms. The only permitted foundational axioms are `propext`,
`Classical.choice` and `Quot.sound`; individual statements may use fewer.

The proof uses the project's existing foundational-axiom policy. Finite
checks reduce in the Lean kernel; no native proof assertions, admissions,
external certificates or additional axioms are used. Execution histories
and resource measurements belong to the working research record, not this
mathematical account.
