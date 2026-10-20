# Sources, attribution and the historical boundary

For [Lower bounds and exact values for $C(2k-c,k,3)$](README.md).

Historical assessment as of **19 October 2026**, carried forward from the
completed source reviews. References below are public bibliographic locators;
statements about what was inspected describe that dated assessment, not a
new literature search. Unread originals limit priority claims, not the
explicit arguments in [proof.md](proof.md).

## What this project claims

Rob Gardiner, with AI assistance, supplies this project's structural arguments and
Lean formalisations of the bounds and exact values stated in [proof.md](proof.md).
The twenty-point shared-block exclusion, bounded-fibre capacity argument,
affine support rigidity, saturated-matching compatibility, and their
compositions with partitioned rank and actual-multiplicity selection are
the project's arguments as presented here. **First
mathematical priority is not established.** Existing witnesses, affine
constructions, incidence counting, signless forms, partitioning and
selection/rank methods retain their established antecedents.

The 19 October assessment concerned the then-established ranges; the
20 October refinements to $17/31/59$ reuse those antecedents and add the
affine-support and matching arguments in proof §§7.4–7.8. No new historical
search is claimed for those refinements.

The inspected sources did not yield an earlier statement or complete earlier
implication of the lower twelve at $(20,11,3)$, the unconditional offset-two
inequality over its full range, or the full $18/36/59$ and $25c$ lower-bound
ranges. That reports the scope of a search, not a proof of novelty. In
particular, qualitative fixed-offset eventual exactness already follows
from classical mathematics, as explained below.

## Comparison with recorded table entries

The following entries were observed in the public
[Covering Repository form](https://www.coveringrepository.com/systems.aspx)
on **19 October 2026**, with $T=M=3$. They are dated reported bounds,
not a fresh retrieval in this documentation update or a claim of
historical priority. The history links identify the inspected entries.

| Parameters $(v,k,t)$ | Interval displayed in the dated observation | Consequence proved here |
|---|---:|---:|
| [$(20,11,3)$](https://www.coveringrepository.com/history.aspx?id=111388) | $11$–$12$ | $C(20,11,3)=12$ |
| [$(36,19,3)$](https://www.coveringrepository.com/history.aspx?id=112072) | $12$–$14$ | $13\le C(36,19,3)\le14$ |
| [$(38,20,3)$](https://www.coveringrepository.com/history.aspx?id=112153) | $12$–$14$ | $13\le C(38,20,3)\le14$ |
| [$(48,25,3)$](https://www.coveringrepository.com/history.aspx?id=112543) | $12$–$14$ | $13\le C(48,25,3)\le14$ |

These comparisons distinguish improvement over an inspected entry from
first discovery of a bound. A table may omit an earlier result. No old
interval is asserted here for every member of the infinite families.
In particular, the inspected form offered block sizes only through $25$;
it supplied no comparison for the boundary examples $(60,31,3)$, $(62,32,3)$,
$(115,59,3)$ or $(196,100,3)$. Their exact values follow from the proved
lower bounds and constructions, independently of repository entries.

The [parameter map](README.md#parameter-ranges-in-vkt) gives the complete
headline ranges. The existing twelve-block witness and the established
geometric construction methods retain the attributions below.

## Selection and rank

The precise multigraph selection theorem in proof §7.1 is credited to
**Y. Caro and Z. Tuza**, as stated in **D. Horsley and R. Singh**,
*New lower bounds for t-coverings*, Journal of Combinatorial Designs
**26** (2018), 369–386, [Theorem 12](https://arxiv.org/html/1706.06825v2).
Its graph is finite, undirected and loopless, with natural edge multiplicities.
It gives induced weighted degrees strictly below a positive integer threshold
and the ceiling of the explicit potential sum. Proof §7 states every one
of these hypotheses and proves the result in that form.

The supplied deletion proof follows **D. Horsley**,
*Generalising Fisher's inequality to coverings and packings*,
[§4, Lemma 7 and property (F2)](https://arxiv.org/html/1409.0485#S4),
the accessible weighted proof used in the project's Lean selection
formalisation. The full deletion argument needed here is included in
[proof §7.1](proof.md#71-the-selection-theorem-and-its-proof).
The [original Caro–Tuza publisher record](https://doi.org/10.1002/jgt.3190150110)
identifies the antecedent; its original proof was not obtained. This is
not represented as a literal translation of that original. The real-weight
extension is Horsley's and requires the positive high–high edge condition
spelled out in proof §7.1. The natural-weight application needs no extra
edge hypothesis.

Horsley–Singh's Lemmas 1, 3 and 5 develop the incidence Gram/excess/strict-rank
method; Theorem 15 combines selection and counting in the large-defect range.
Proof §7.2 gives the full $s=1$ actual-multiplicity argument, including the
incidence fallback when the two-level coefficient condition fails. It does
not substitute three for a universal residual seed: the universal one-cover
number at our residual parameters is two. The structural theorem and its
covering wrapper are distinguished in the
[Lean appendix](proof.md#appendix-lean-correspondence-and-dependency-contracts):
only the former is used by the actual-family adapter.

The minimum-monochromatic-weight argument in proof §6 is the classical
partition method associated with **L. Lovász**, *On decomposition of graphs*,
Studia Scientiarum Mathematicarum Hungarica **1** (1966), 237–238.
The original was not obtained; the attribution is based on a later
statement inspected in the source review. Here the finite weighted argument
is proved directly,
so no unread theorem is used as a premise.

The signless quadratic form and propagation of kernel coordinates are
standard linear algebra. A closely related inspected precedent is
**J. Chang's** [public mathematical source](https://github.com/jamesyc/covering/blob/main/paper/c24-14-4.tex),
§3, “One identity describes all linear relations”, and Appendix A on
cross-rectangle capacity and shared blocks. Its advertised parameters are
different; neither its external formal build nor chronological priority
was independently certified by this project. Proof §§4–5 supply the
argument used here, without importing Chang's result.

## Constructions and point links

The twelve-block witness is existing construction data. A dated observation
of the [Covering Repository](https://www.coveringrepository.com/systems.aspx),
with parameters $V=20,K=11,T=M=3$, records **Jan de Heer, 16 May 2005**, as
creator and construction date, and the Dan Gordon Covering Repository as
source. Its public [download locator](https://www.coveringrepository.com/download_system.aspx?id=113424)
and [history locator](https://www.coveringrepository.com/history.aspx?id=111388)
were recorded; the live download was not independently retrieved. The
family displayed in [proof §8](proof.md#8-attainment-a-known-witness-and-weighted-affine-planes)
was taken from the retained repository payload and matches
[Witness.lean](../../lean/CoveringDesigns/C20_11_3/Witness.lean), where all
1,140 triples are checked. Those twelve displayed blocks are sufficient to
reproduce the upper bound without the payload or either web endpoint.
The creator/date are repository metadata, not a determination of first
discovery or first publication; no new witness is claimed.

D. M. Gordon and D. R. Stinson's [handbook chapter, *Coverings*](https://dmgordon.org/papers/hcd.pdf),
Table 1.35, uses bold entries for exact values. Its unbold twelve at
$(20,11,3)$ is an upper bound, not an earlier lower-bound proof.

**D. M. Gordon, G. Kuperberg and O. Patashnik**, *New constructions for
covering designs*, Journal of Combinatorial Designs **3** (1995), 269–284,
[§III, Theorem 3; §§IV and VI.1](https://arxiv.org/html/math/9502238),
describe affine coverings and the restriction, padding and expansion
methods. The fourteen planes of $\mathrm{AG}(3,2)$ are established geometry.
Proof §8 supplies the four integral weight patterns, covers projections of
size at most three, and handles empty fibres and deduplication explicitly.
The exact all-parameter formulation and four patterns were not located as
an earlier statement, but the construction method is not new to this project.

The six-block point-link obstruction is also established. **D. T. Todorov**,
*On Some Covering Designs*, Journal of Combinatorial Theory, Series A
**39** (1985), 83–101, [publisher record](https://doi.org/10.1016/0097-3165(85)90084-6),
p.87, Theorem 4(B) with $s=1$, gives more than five pair-cover blocks when
the point-to-block-size ratio exceeds $9/5$. That case is credited there
to Stanton–Kalbfleisch–Mullin (1970), also citing Mills. For a point link
our ratio is $(2k-c-1)/(k-1)$, so the criterion is $k>5c-4$; at
offset two it gives the floor for $k\ge7$. The elementary proof used by
our Lean components uses the sufficient range $k\ge8c-7$, hence $k\ge9$
at offset two. This difference is a proof choice, not a claim to an optimal
or newly discovered link threshold.

## Qualitative eventual exactness

The explicit $25c$ strip must be distinguished from the classical conclusion
that each fixed offset eventually has value fourteen. Here is the complete
finite argument used for that historical comparison. It is a **paper-only
deduction**, not a claimed Lean declaration or a claim that its deliberately
coarse constant appeared in print. It is not a premise of the principal
results. Besides finite incidence counting, it uses the standard facts
that a linear functional on a nonempty compact polytope attains its maximum
at a vertex, Cramer's rule, and Hadamard's determinant inequality.

J. Schönheim, *On coverings*, Pacific Journal of Mathematics
**14** (1964), 1405–1411,
[original journal scan](https://msp.org/pjm/1964/14-4/pjm-v14-n4-p29-p.pdf).
Definitions are on p.1406; Theorem I and its incidence proof are on p.1407.
With $n=2K, k=K, l=3,\lambda=1, K\ge3$, its nested ceilings give

\[
C(2K,K,3)\ge
\left\lceil2\left\lceil\frac{2K-1}{K-1}
\left\lceil\frac{2K-2}{K-2}\right\rceil\right\rceil\right\rceil
\ge14. \tag{H1}
\]

For clarity, the nested bound follows by taking a point of at most the
average degree in an ordinary $(v,k,t)$ covering, $v\ge k\ge t\ge2$:
its link is a smaller covering and the incidence identity
$v\min_x d(x)\le kb$ gives $b\ge\lceil(v/k)C(v-1,k-1,t-1)\rceil$.
Iterate to strength one, where covering all points requires at least the
ceiling of their number divided by block size. This proves the displayed
bound using only ordinary links and finite counting.

The inner ceiling is at least three; the middle argument is at least
$6+3/(K-1)>6$, giving seven. All denominators are positive. At $K=3$
the bound can be stronger, which causes no exception.

Now suppose an ordinary triple covering on $v\ge k\ge3$ points has
$1\le b\le13$ blocks. Give each point its support $S\subseteq[b]$,
the indices of blocks containing it. Supports are nonempty. Any at most
three distinct support types have a common index: choose representatives
and extend to three distinct points if necessary. The same property handles
repetitions of a type. Let $M$ be the zero-one matrix of these support
columns and consider

\[
R=\max\{\mathbf1^{\mathsf T}x:Mx\le\mathbf1,\ x\ge0\}.
\]

This finite polytope is compact: every column is nonzero, so each coordinate
lies in $[0,1]$. The original type multiplicities divided by $k$ are
feasible, hence $v/k\le R$. At a maximizing vertex, if $r\ge1$ coordinates
are positive, the active block constraints have rank $r$ on those
coordinates; otherwise a small nonzero perturbation in both directions
preserves all constraints, contradicting extremality. Thus $r\le b\le13$,
and an invertible $r\times r$ zero-one matrix $A$ gives $Ax=\mathbf1$.
Cramer's rule makes $R=p/\Delta$, with $p$ integral and

\[
1\le\Delta=|\det A|\le r^{r/2}\le13^{13/2}<D:=13^7=62\,748\,517.
\]

The determinant estimate is Hadamard's inequality (each row has Euclidean
norm at most $\sqrt r$). No enumeration or optimisation of support
configurations is required.

If $R\ge2$, multiply the rational weights by a sufficiently large common
denominator $K\ge3$. They give integral type multiplicities on
$N=KR\ge2K$ points, with at most $K$ points in each of the $b$ blocks.
The preserved three-wise support intersection property covers every triple.
Restrict to $2K$ points, pad each block to size $K$, and deduplicate.
This contradicts (H1). Therefore $R<2$. Integrality of $p,\Delta$ gives

\[
\frac vk\le R\le2-\frac1\Delta\le2-\frac1D.
\]

For $v=2k-c$, any cover with at most thirteen blocks must consequently
have $k\le Dc$. Together with the affine upper construction in
[proof §8](proof.md#8-attainment-a-known-witness-and-weighted-affine-planes),
this proves the explicit classical consequence

\[
C(2k-c,k,3)=14\qquad(c\ge2,\ k\ge62\,748\,518c). \tag{H2}
\]

All transformations preserve ordinary coverage, with at most the original
number of distinct blocks. The hypotheses $v\ge k\ge3$ hold in (H2).
This deliberately coarse constant is not a threshold optimisation. It
does not imply $25c$, nor the entire $k\ge18,36,59$ ranges. Mills's
unread maximal-ratio results may yield a vastly better constant; no value
of the thirteen-block maximal ratio is attributed to him here without inspecting it.

Todorov 1985 p.84 also reports Mills's attainment of a maximal ratio for
a fixed block budget. If applicable at thirteen blocks and strength three,
that report gives the same qualitative ratio-gap explanation with
Schönheim. It remains secondary evidence for Mills's theorem; no numerical
value of the thirteen-block maximal ratio is assigned to him here.

## Preserved component stages

The specialised components remain valid and reusable. Their earlier
thresholds are development stages, rather than additional premises of the
current combined proof:

| Component | Preserved range or role |
|---|---|
| `TwoKMinusTwo` | Lower thirteen for $k\ge20$, exact fourteen for $k\ge41$, the unconditional inequality for $k\ge9$, and the upper construction for $k\ge3$. |
| `TwoKMinusTwoEquality` | Lower thirteen for $k\ge19$, exact fourteen for $k\ge40$, and the optional equality rigidity in proof §9. |
| `TwoKMinusC` / `TwoKMinusCGeneral` | The selection-based $18/36/59$ and uniform $25c$ ranges. |
| `TwoKMinusTwoTightening` | Centered support completion adds the 17/35 offset-two endpoints; earlier modules are unchanged. |
| `RankSlackCapacity` | Indexed threefold pair-cover lower bound fourteen and ordinary exactness for $k\ge33$, using affine fibres and support-class capacity. |
| `SaturatedMatching` | Ordinary exactness for $k\ge31$, adding affine-boundary rigidity and actual saturated-matching compatibility. |

The Lean appendix gives the operative declarations. A stronger paper
classification at the equality boundary is outside this account and is not
asserted by its Lean contracts.

## Remaining source-access limitations

The Todorov 1985 original was inspected in the completed source review.
At strength three its new classification concerns seven blocks. Its quoted
Mills obstruction has budget at most nine. No applicable deduction of our
eleven-, twelve- or thirteen-block exclusions was found. Later inspected
thirteen-block classifications concerned pairs, and the reported near-half
triple result concerned offset one; deleting points transfers upper bounds,
not those lower bounds.

Three relevant originals remain unread:

- **W. H. Mills**, *Covering designs I: Coverings by a small number of
  subsets*, Ars Combinatoria **8** (1979), 199–315.
- **W. H. Mills and R. C. Mullin**, *Coverings and packings*, in
  J. H. Dinitz and D. R. Stinson (eds.), *Contemporary Design Theory*,
  Wiley, 1992, 371–399, especially §4.
- **D. T. Todorov and V. D. Tonchev**, *On some coverings of triples*,
  C. R. Acad. Bulg. Sci. **35**(9) (1982), 1209–1211.

These gaps may affect priority and attribution, not validity of the
explicit proofs. The original Caro–Tuza and Lovász texts are additional
methodological source limitations; the required arguments are supplied in
proof.md from the verified reconstructions. The remaining historical priority
and threshold-optimality questions are
left open. No first-discovery or optimal-threshold claim is made.

## Consolidated offset-two proof, 20 October 2026

The final ordinary exactness interface is
[`SaturatedMatching.Exactness`](../../lean/CoveringDesigns/SaturatedMatching/Exactness.lean),
with threshold $k\ge31$. Its reusable actual affine-boundary and saturated-
matching arguments are proved in full in [proof §§7.5–7.8](proof.md#75-actual-affine-supports-and-the-dimension-boundary).
The independent indexed pair-cover interface
[`TwoKMinusTwoCapacity.Indexed`](../../lean/CoveringDesigns/TwoKMinusTwoCapacity/Indexed.lean)
retains the coverage premise of multiplicity at least three and
the separate range $k\ge33$; it does not require triple coverage. The
centering and clone-capacity argument of §7.4 still supplies the lower
thirteen at $k=17$. Earlier proved interfaces remain included at their
original scopes. None of these statements asserts that 31 is the optimal
threshold, or resolves any additional case below it.
