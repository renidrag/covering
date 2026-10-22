# A structural proof of 41 ≤ C(14,5,3) ≤ 43

**Rob Gardiner, with AI assistance**

## Abstract

Every covering of the triples of a fourteen-point set by five-element
blocks has at least 41 blocks. A historical 43-block covering supplies the
upper bound. The lower proof first establishes a universal 27-occurrence
completion bound for an exact 2-(13,4,1) design, giving the parent lower
bound 40 and irredundancy at forty. A self-contained removable-block lemma
for fourteen-occurrence pair covers then identifies special parent blocks.
Private triples, disjoint excess charges and compatibility of several exact
links exclude forty. Only afterwards is the completion bound strengthened
to 28. All arguments allow indexed repeated occurrences. The formalisation
uses finite incidence counting, without coordinates, plane classification,
rank assumptions or exclusion certificates.

## Introduction and conventions

A **(v,k,t) covering** is an ordinary family of distinct k-subsets of a
v-point set that contains every t-subset in at least one block. Its minimum
size is C(v,k,t). We prove the stronger lower statement for a finite index
set I and a function i↦B_i; different indices may have equal block values.
Write b=|I|, d(x)=|{i:x∈B_i}|, and μ(T)=|{i:T⊆B_i}|. Deletion always removes
one index. A private triple of index i is a three-set contained in B_i and
in no B_j with j≠i. A family is irredundant when every index has one.

**Theorem 1 (main result).** On every fourteen-point set, any finite indexed
family of five-sets covering every triple has at least 41 occurrences.
There is an ordinary covering with exactly 43 distinct blocks. Consequently
41≤C(14,5,3)≤43. No covering with 41 blocks is asserted, and exactness is open
within this account.

**Background and contribution.** The proof below reconstructs and
formalises the structural completion and parent-compatibility argument.
The deletion lemma is a special case of Sane's general theorem on
projective failed designs. His
unread general proof is not a dependency: the needed special case is proved
here. The historical upper construction is attributed separately in
[the source account](sources.md). An unchanged table or incomplete literature
search does not establish priority for the lower bound.

**Proof outline.** Lemmas 2–5 prove completion≥27 and parent lower≥40.
Lemma 6 gives irredundancy at forty. Lemmas 7–10 establish deletion and
special blocks; Lemmas 11–12 give the two private-triple/charging restrictions.
Lemmas 13–15 establish compatibility of chosen minimum points. Theorem 16
excludes forty. Corollary 17 then proves completion≥28 by adjoining a point;
Proposition 18 checks the historical upper witness. The appendices specify
the Lean correspondence and verification boundaries.

## 1. Exact links and the original completion bound

Let X have thirteen points and let indexed four-sets L_j contain every pair
exactly once. Call triples contained in a line **collinear**; call the other
triples **noncollinear**. No coordinatisation is assumed.

**Lemma 2 (exact-link incidence).** There are thirteen line occurrences and
four through each point. Every pair has a unique containing line index.
Distinct lines intersect in exactly one point. There are 52 collinear and
234 noncollinear triples; a collinear triple has a unique containing line.

*Proof.* Pair incidence gives 6|J|=78. At a point, the three-point remainders
of its lines partition the other twelve points, so its degree is four.
Two distinct lines cannot share a pair; thus line values cannot repeat.
For a fixed line, the four points each have three other incident lines.
These twelve indices are distinct, exhausting all other lines, so every
other line meets it once. The thirteen lines supply 13·4=52 distinct
triples, out of 286 total. ∎

**Lemma 3 (no five-arc).** Every five-set contains a collinear triple.

*Proof.* Suppose A has no such triple. Every line meets A in at most two
points. At each a∈A the four lines joining it to A\{a} are distinct and
exhaust the four lines at a. Hence every line meeting A meets it twice.
Choose x∉A. The lines through x partition A into parts of size zero or two,
contradicting |A|=5. ∎

A **completion** is a finite indexed family of five-sets A_i covering all
234 noncollinear triples; it need not cover collinear triples. Put

    c_i = number of collinear triples in A_i,
    loss = Σ_i (c_i−1),
    excess = Σ_noncollinear T (μ(T)−1).

**Lemma 4 (capacity, slack and line obstruction).** For n completion
occurrences,

    loss + excess + 234 = 9n.                         (1)

For every pair P,

    3μ(P) = 9 + Σ_noncollinear T⊇P (μ(T)−1)
                 + Σ_collinear T⊇P μ(T).             (2)

Every completion has at least 27 occurrences.

*Proof.* Lemma 3 gives c_i≥1. Counting occurrence/triple incidences gives
Σ_i c_i+Σ_noncollinear μ(T)=10n; subtracting the n baseline collinear
incidences and 234 required incidences gives (1). For a pair P, its line
has two further points and there are nine points off the line. Each
five-block through P supplies three triples through P, proving (2).

Equation (1) first gives n≥26. If n=26, all c_i=1 and all noncollinear
multiplicities are one. The four collinear triple weights on any fixed
four-point line then have every pairwise sum divisible by three, by (2).
If three weights are a,b,c, the relations a+b≡a+c≡b+c≡0 mod 3 imply
2a≡0 and therefore a≡b≡c≡0; the fourth follows from another pair relation.
Each collinear triple belongs to its unique line, so every collinear
weight is divisible by three. But their sum is Σ_i c_i=26, contradiction.
The proof retains the located excess term in (2); individual weight
divisibility is not asserted when that term is positive. ∎

**Lemma 5 (parent floors and lower forty).** In every indexed (14,5,3)
cover, d(x)≥13 and μ(P)≥4 for every pair P. If d(x)=13, its point link is
an exact 2-(13,4,1) design, every pair through x has multiplicity four, and
every triple through x has multiplicity one. Every parent cover has at
least forty occurrences.

*Proof.* A pair has twelve triple extensions, and each incident block
supplies three; hence μ(P)≥4. The link at a point covers 78 pairs with
six per occurrence, so d(x)≥13. At equality its 78 pair incidences give
exact pair coverage. Alternatively, the thirteen parent pairs through x
have total multiplicity 4d(x)=52, so all have multiplicity four; the twelve
triple extensions of each such pair have total multiplicity twelve and
hence all have multiplicity one.

If b≤39, the sum Σ_x d(x)=5b≤195 is less than 14·14, so some point has
degree thirteen. Its b−13 avoiding occurrences cover all noncollinear
triples of its exact link: a block through x containing such a triple would
make it collinear. Lemma 4 gives b−13≥27, contradicting b≤39. ∎

**Lemma 6 (forty is irredundant).** A forty-occurrence parent cover has a
private triple at every index, and its block map is injective.

*Proof.* If an index had no private triple, deleting just that index would
leave a thirty-nine-occurrence cover, contrary to Lemma 5. Equal block values
at two indices cannot have a private triple. This argument is specific to
the forty budget; arbitrary larger coverings need not be irredundant. ∎

## 2. The fourteen-occurrence deletion lemma

**Lemma 7 (degree and pair-excess profile).** In fourteen indexed four-sets
covering all pairs of thirteen points, precisely four points have degree
five and the other nine have degree four. If H is that four-set, pairs in
H have multiplicity two and all other pairs have multiplicity one.

*Proof.* Write r_x for degree, ε_x=r_x−4, and f_xy=μ({x,y})−1 for x≠y,
with f_xx=0. Counting gives

    ε_x≥0,  Σ_x ε_x=4,  Σ_y f_xy=3ε_x.

An excess edge has both endpoints in H={x:ε_x>0}. Empty H contradicts the
sum; one high point cannot support an excess edge. With two high points,
their excess degrees must agree, forcing ε=2,2 and pair multiplicity seven,
which exceeds either degree six. With three, the positive partition is
2,1,1. At the degree-six point a the two incident excesses are 3,3 and the
third excess is zero. The four indices containing ab and the four containing
ac are contained among six indices through a; at least two contain both,
contradicting multiplicity one for bc. These are all cases with fewer than
four positive excesses. Thus |H|=4 and all ε on H equal one.

Let n_s count actual indices meeting H in s points. Point and pair incidence
give

    Σ_s n_s=14,  Σ_s s n_s=20,  Σ_s binom(s,2)n_s=12. (3)

The last equality counts six base pairs in H plus six excess units. In
particular n_1=−4+3n_3+8n_4, so n_1 cannot be zero: the equation
3n_3+8n_4=4 has no nonnegative integer solution.

Choose a block meeting H in just a. All its pairs have multiplicity one,
so each other block meets it in at most one point. The sum of these thirteen
intersection sizes is 5+3·4−4=13, so each is one. For y∈H\{a}, its pairs
with the three low points use three distinct indices. Its other two indices
must meet the chosen block at a. Thus μ(ay)=2. The remaining three excess
edges on H have each two-term sum two; these three equations force every
one of them to be one. This proves the pair profile. ∎

**Lemma 8 (an actual removable occurrence).** H occurs as a block. Deleting
one index with that value leaves an exact 2-(13,4,1) design.

*Proof.* If H never occurs, n_4=0. From (3),
n_2=12−3n_3 and n_0=6−n_3, so n_3≤4 and n_0≥2. Choose an all-low block D.
Other blocks meet it at most once and their intersection sizes sum to
4·4−4=12. Among thirteen other indices exactly one is disjoint from D.
For each high point y, the four unique pairs from y to D use four distinct
indices. Of its five indices exactly one is disjoint from D; uniqueness
makes it the same index for every y. Its four-set is H, contradiction.

Deleting any one index with block H subtracts one from each pair in H and
nothing from other pairs. Lemma 7 leaves pair multiplicity one throughout.
There is no claim of a unique removable index: an exact design with one
line repeated fits the hypotheses. Deleting all copies would be wrong. ∎

This is the self-contained order-three special case of the known
projective failed-design antecedent credited to Sane in [sources.md](sources.md).

## 3. Special parent blocks and charges

In the remaining parent arguments, V denotes the fourteen-point ground set.

**Lemma 9 (special blocks).** In a parent cover, each degree-14 point y has
an actual special block K_y. Triples through y have multiplicity two exactly
when contained in K_y, and multiplicity one otherwise. For z≠y, pair yz has
multiplicity five exactly when z∈K_y, and four otherwise. The block value
K_y is uniquely determined. It contains no degree-13 point. If z∈K_y has
degree fourteen, then K_z=K_y.

*Proof.* Apply Lemmas 7–8 to the fourteen four-set occurrences of y's link.
Adjoining y to the actual H occurrence gives K_y. The link degree and pair
profiles give precisely the asserted parent pair and triple profiles. The
pair profile identifies K_y\{y} intrinsically. A degree-13 point in K_y would
make its pair with y have multiplicities both four and five. Finally, if
z∈K_y has degree fourteen, pair yz forces y∈K_z. For every other v∈K_y,
the repeated triple yzv forces v∈K_z. Both blocks have size five, so they
are equal. At forty, Lemma 6 also makes their occurrence index unique. ∎

**Lemma 10 (private triples and grouping).** In an irredundant parent cover,
each special block contains at most two degree-14 points. Its private
triples use only points of degree at least fifteen. Degree-14 points are
partitioned by their special block indices; chosen private triples of
different special indices are distinct.

*Proof.* By Lemma 9 there is no degree-13 point in a special block. A
private triple containing one of its degree-14 points would be one of that
point's multiplicity-two triples, impossible. Its three private points thus
have degree at least fifteen, leaving room for at most two degree-14 points.
The grouping identity in Lemma 9, and injectivity from irredundancy, give
uniqueness of the actual containing special index. Equal chosen private
triples at two indices would contradict privacy. ∎

**Lemma 11 (no minimum-point-free forty cover).** A forty-occurrence cover
has a degree-13 point.

*Proof.* Otherwise all degrees are at least fourteen, with total excess
200−196=4. At most four points have degree at least fifteen; at least ten
have degree fourteen. Lemma 10 requires at least five special indices and
five distinct private triples on at most four high points. There are at
most binom(4,3)=4 such triples, contradiction. ∎

**Lemma 12 (disjoint five-unit and eight-unit charges).** Fix a degree-13
point x in an irredundant parent cover. For each special block K, let M be
its set of degree-14 points, m=|M|, c its collinear-triple count in x's link,
and Q the set of its noncollinear triples meeting M. Then m is one or two,
each T∈Q has residual multiplicity two, and

    c−1+|Q| ≥ 5  if m=1;    c−1+|Q| ≥ 8  if m=2.     (4)

The Q sets of different special indices are disjoint. Their charges sum
to at most the residual loss plus excess. For a forty-occurrence cover,
there is at most one special block and at most two degree-14 points.

*Proof.* All special blocks avoid x by Lemma 9. Any triple of K is collinear,
belongs to Q, or avoids M. Hence

    10 ≤ c+|Q|+binom(5−m,3),
    9 ≤ (c−1)+|Q|+binom(5−m,3),                       (5)

where c≥1 by Lemma 3. This gives both charges without classifying five-set
collinear counts. The eight-unit inequality suffices; an equality assertion
is unnecessary for the proof.

A charged triple meets a degree-14 point of its special block, so has
parent multiplicity two by Lemma 9. It is noncollinear in x's link, so no
occurrence through x contains it; its residual multiplicity is also two.
If the same triple were charged at another special block, one of its
marked points would belong to both. Lemma 9 and irredundancy force the
same occurrence index. Thus each excess summand is used once. Loss summands
also use distinct residual occurrence indices. The two sums are separate
parts of (1), so there is no repeated charging.

At forty the residual has 27 occurrences; (1) gives loss+excess=9. If g_1
and g_2 count special indices with one and two marked points, respectively,
(4) yields 5g_1+8g_2≤9. In particular there is at most one special index,
and Lemma 10 gives at most two degree-14 points. ∎

## 4. Compatibility of selected minimum points

The following statements concern any chosen set Z of degree-13 points.
They require neither a forty budget nor irredundancy, and do not assume
that Z is the entire set of minimum points.

**Lemma 13 (trace restriction and frame).** If a block misses a point of Z,
it meets Z in at most two points. If |Z|≥3, some unique block contains Z,
and every other block meets Z in at most two points.

*Proof.* Suppose B misses x∈Z. Lemma 3 in x's exact link supplies a
collinear triple T⊆B. The parent block formed from its line and x is a
different occurrence also containing T. Thus T cannot meet Z, since every
triple meeting a degree-13 point has multiplicity one. Its three points
outside Z leave at most two points of Z in B. If |Z|≥3, cover a triple in Z.
The resulting block must contain all of Z by this restriction; its index
is unique because that triple has multiplicity one. ∎

**Lemma 14 (four-point compatibility).** If |Z|=4 and every point of Z has
degree thirteen, its frame is B*=Z∪{p} for some p∉Z with d(p)≥16.

*Proof.* Lemma 13 gives a unique frame B*=Z∪{p}. All other traces have
size at most two. Pair and point counts give

    n_2+6=24,    n_1+2n_2+4=52,

so n_2=18 and n_1=12. A two-Z block avoids p, since otherwise the triple
formed from p and its two Z points would repeat one in B*. The pairs pz,
z∈Z, each have multiplicity four. Their sixteen incidences comprise four
in B* and at most one in each one-Z block, with zero in two-Z blocks.
Thus all twelve one-Z blocks contain p.

Let r count the zero-Z occurrences through p. Then d(p)=13+r. Set
R=V\(Z∪{p}), of size nine. For a pair Q⊆R, let n_1(Q), n_2(Q) count the
one-Z and two-Z blocks containing Q, and n_0p(Q) count zero-Z blocks
containing p and Q. Unique triples Q∪{z} give

    4 = n_1(Q)+2n_2(Q).

Thus n_1(Q) is even. Coverage of p∪Q gives
n_1(Q)+n_0p(Q)≥1, since the frame cannot contain Q and two-Z blocks avoid p.
Consequently 2≤n_1(Q)+2n_0p(Q). Sum over the 36 actual pairs in R. Each
one-Z block has three R points; each zero-Z block through p has four.
Therefore 72≤12·3+2·6r=36+12r, so r≥3 and d(p)≥16. ∎

**Lemma 15 (five chosen minimum points are impossible).** Every parent
cover has at most four degree-13 points.

*Proof.* Suppose W consists of five degree-13 points. Choose Z⊆W with
|Z|=4. Lemma 14 supplies an actual frame occurrence B*=Z∪{p} with d(p)≥16.
Lemma 13 applied to W supplies a block equal to W; every other occurrence
meets W in at most two points. Since B* contains four points of W, it is
that same occurrence. Hence p∈W, contradicting d(p)=13. If there are more
than five minimum points, choose any five and apply the same argument. ∎

## 5. Assembly, strengthened completion and upper construction

**Theorem 16 (unconditional lower bound 41).** Every indexed parent cover
has at least forty-one occurrences.

*Proof.* Lemma 5 excludes fewer than forty. Suppose b=40. Lemmas 6 and 11
supply irredundancy and a degree-13 point. Let z,m count degrees thirteen
and fourteen. Lemma 12 gives m≤2 and Lemma 15 gives z≤4. All other degrees
are at least fifteen, so

    200 = Σ_x d(x) ≥ 210−2z−m.

This forces z=4 and m=2. By Lemma 14 some point outside the four minimum
points has degree at least sixteen. Its additional unit gives
200≥211−2·4−2=201, contradiction. Both minimum-degree branches are covered,
and every structural hypothesis used here was derived from the cover. ∎

**Corollary 17 (universal completion bound 28).** For any indexed
2-(13,4,1) design, every finite indexed family of five-subsets covering all
its noncollinear triples has at least 28 occurrences.

*Proof.* Adjoin a new point x. Keep each completion occurrence and add an
independently indexed block {x}∪L_j for each of the thirteen lines. All
blocks have size five. A triple through x is covered by the line through
its other two points. An old collinear triple is covered by its augmented
line; an old noncollinear triple is covered by the completion hypothesis.
This is a fourteen-point triple cover with 13+n occurrences. Theorem 16
gives n≥28. This corollary is downstream of that theorem, never a premise
of it. Repeated completion blocks are allowed. ∎

**Proposition 18 (historical upper witness).** There is an ordinary
(14,5,3) covering with 43 blocks, on arbitrary fourteen-point labels.

*Proof.* The [retained data](../../data/c1453-historical-witness.json) lists
43 five-subsets with original labels 1 through 14. Its ordered 215 label
bytes have SHA-256
`173772ab8d73847ff258f4f5ae2859d0fbe7e312483e1afc23d58c721bd22f93`.
The supplied construction was independently checked for labels, block
sizes, distinctness and all binom(14,3)=364 triples. In Lean the same blocks
are shifted to labels 0 through 13 in `Fin 14`. Ordinary kernel reduction
proves list distinctness, family cardinality 43, block uniformity and
coverage of every triple. A bijection transports that actual ordinary
family to any fourteen-point type. This is finite verification of one
witness, not an exhaustive classification or a lower-bound certificate.
Its historical attribution is given in [sources.md](sources.md). ∎

Theorem 16 and Proposition 18 prove Theorem 1. Whether C(14,5,3) is 41, 42
or 43 is not resolved by these arguments.

## Appendix A. Lean correspondence

Names in the table have prefix `CoveringDesigns.C14_5_3`, unless explicitly
shown otherwise. Each module is under
[`lean/CoveringDesigns/C14_5_3/`](../../lean/CoveringDesigns/C14_5_3/).
All 156 public theorem contracts, including helpers and boundary examples,
are fixed by full type ascriptions in the [component audit](../../lean/audits/C14_5_3.lean).

| Statement | Module and principal declarations |
|---|---|
| Lemma 2 | `ExactLink`: `exact_line_count`, `exact_point_count`, `exact_unique_line`, `exact_line_intersection`, `exact_lines_meet`, `collinear_card`, `noncollinear_card` |
| Lemma 3 | `ExactLink`: `no_five_arc` |
| Lemma 4 | `Completion`: `completion_slack`, `completion_pair_identity`, `linewise_divisibility`, `completion_at_least_27` |
| Lemmas 5–6 | `Forty`: `point_floor`, `pair_floor`, `minimum_link_exact`, `minimum_pair_exact`, `minimum_triple_exact`, `lower_bound_40`, `forty_irredundant` |
| Lemma 7 | `AlmostExactCounts`: `high_points_card`, `high_degree_five`; `AlmostExactTraces`: `high_trace_moments`; `AlmostExactIntersections`: `one_high_pair_two`; `AlmostExactLink`: `almost_pair_profile` |
| Lemma 8 | `AlmostExactLink`: `almost_high_block`, `delete_index_balance`, `almost_exact_deletion` |
| Lemmas 9–10 | `ParentLinks`: `SpecialAt`, `exists_special`, `special_blocks_equal`, `special_avoids_minimum`; `SpecialBlocks`: `private_high`, `special_middle_le_two`, `special_group_count`, `distinct_private_triples` |
| Lemma 11 | `LowerBound`: `forty_has_minimum` |
| Lemma 12 | `CompletionCharges`: `block_charge_capacity`, `block_charge_five`, `block_charge_eight`, `disjoint_charge_budget`; `ParentCharges`: `residual_charge_excess`, `residual_charges_disjoint`, `special_charge_eight`, `minimum_special_count` |
| Lemma 13 | `MinimumTraces`: `minimum_trace_restriction`, `minimum_frame`, `minimum_trace_moments` |
| Lemma 14 | `MinimumCompatibility`: `four_minimum_frame`; `FourMinimum`: private `frame_point_sixteen`, public `four_minimum_forces_sixteen` |
| Lemma 15 | `FourMinimum`: `no_five_minimum`, `minimum_points_le_four` |
| Theorem 16 | `LowerBound`: `not_forty`, `indexed_lower_bound`, `lower_bound`; public `CoveringDesigns.lower_bound_14_5_3`, `CoveringDesigns.indexed_lower_bound_14_5_3` |
| Corollary 17 | `Completion28`: `completed_covers_new`, `completed_covers_collinear`, `completed_covers_noncollinear`, `completed_isCover`, `completion_at_least_28` |
| Proposition 18 | `Witness`: `CoveringDesigns.knownCover43_14_5_3_isCover`, `CoveringDesigns.knownCover43_14_5_3_card`, `CoveringDesigns.upper_bound_14_5_3_on` |
| Theorem 1 | Public `CoveringDesigns.covering_interval_14_5_3_on` and `CoveringDesigns.covering_interval_14_5_3` |

The private frame lemma retains the actual occurrence B*=Z∪{p}; the public
four-point interface returns only p and its degree bound. The five-point
exclusion uses the retained identity, so no separate five-point parity
argument is needed. Recommended external entry points are listed in the
[README](README.md#recommended-interfaces); the finer helpers remain available
and retain their existing contracts and audit checks.

### Exact contract scope and representation

`lower_bound_14_5_3` takes only a finite point type with cardinality fourteen
and `IsCover C 5 3`, and concludes `41 ≤ C.card`. The public indexed adapter
takes block uniformity and existence of a containing occurrence for every
triple. Neither contract takes degree floors, link exactness, rank,
irredundancy, a special-block assignment or a certificate as a premise.

`completion_at_least_28` takes arbitrary finite point and occurrence types,
point cardinality thirteen, `ExactDesign.IsDesign L 4 2 1`, and
`IsCompletion L B`. The latter means five-set uniformity and multiplicity
at least one for each noncollinear triple. `almost_exact_deletion` takes
only thirteen points, fourteen occurrences and `Multicover.IsCover B 4 2 1`;
it produces an actual index i and exact pair coverage on `{j // j ≠ i}`.
The special/private interfaces assume irredundancy where needed; the chosen
four- and five-minimum-point compatibility interfaces do not.

The formalisation reuses `indexedDegree`, `indexedSubsetDegree`,
`Multicover.subsetLink` and `ExactDesign.IsDesign`. `Incidence` adds only
missing finite trace/support identities. No second incidence or link
framework is introduced. An ordinary family is adapted by `Multicover.ofFamily`.
The adjoining-point construction uses `Option α` for points and a disjoint
sum of line and completion occurrence types.

### Imports and proof adaptations

The exact external project imports are `ExactDesign.Counting`,
`LabelledCliques.Extensions`, `Multicover.Family`, `Foundations.Relabelling`
and `Foundations.StandardAxioms`, with their existing prerequisites.
The lower proof route is

    Incidence → ExactLink → Completion → Forty
      → ParentLinks / SpecialBlocks / exact-link compatibility
      → ParentCharges + FourMinimum → LowerBound → Completion28.

The deletion modules run independently from `Incidence` and `ExactLink`;
`Witness` imports only relabelling. The public entry combines the lower
bound, completion consequence and witness. `Examples` adds boundary checks.
The audit registers the exact project import graph, preserves older
component independence, and prevents `LowerBound` from importing
`Completion28`, `Witness` or `Examples`.

Three deliberate shortenings are reflected in Lean. The three-high-point
case of deletion is handled uniformly by the actual support inequality
μ(ab)+μ(ac)≤d(a)+μ(bc), rather than enumerating labelled excess partitions.
The marked-subset count (5) replaces collinear-type classification and proves
both required lower charges. Compatibility uses a *chosen* minimum-point
set and the pointwise parity inequality of Lemma 14; no separate five- or six-point
case or union-of-covered-pairs construction is needed. Thus the lower proof
needs positivity of the collinear count, not its full optional classification.

## Appendix B. Verification boundaries

The [shared verification guide](../../technical-details.md) describes setup.
From the repository root:

```sh
./covering doctor
./covering check
./covering verify 14-5-3
./covering audit 14-5-3
./covering verify
./covering audit
```

`check` checks source boundaries, input hashes, the explicit witness and
other deterministic data; it does not verify Lean proofs. `verify` freshly
compiles the selected dependency closure and executes typed theorem and
transitive axiom audits. `audit` validates existing records and fingerprints
without claiming a new compilation. The focused audit includes expanded
ordinary, indexed and completion statements. The only permitted transitive
axioms are `propext`, `Classical.choice` and `Quot.sound`; the principal
interval and its expanded restatement use exactly these three.

Boundary examples exhibit a repeated indexed cover that is not irredundant,
a cover surviving deletion of one index, and failure after deleting all
copies of that block value. The almost-exact and forty-private adapters
also expose their hypotheses without an injectivity or structural premise.
Workflow tests check registration, dependency order, omitted contracts and
witness transcription failures; these tests are not mathematical proofs.
No native assertion or external exclusion certificate is part of this result.
