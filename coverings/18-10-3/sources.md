# Sources and attribution for C(18,10,3) and its lifting corollaries

Compiled 21 October 2026 from a source assessment made on **20 October 2026**.
The numerical comparisons below refer to that date; they are not a new
literature search or current-record check. The [mathematical proof](proof.md)
and its Lean declarations supply the proofs. These references supply
attribution, historical comparisons and the limits of the priority assessment.

## Contribution and evidence levels

Rob Gardiner, with substantial AI assistance, is credited for the structural
11-block exclusion, its reusable rank-equality and actual-support interfaces,
and the formalisation and unified account. The known 12-block construction
and Schönheim's lifting theorem retain their historical attribution. The five
higher-strength lower bounds are standard consequences of the one seed.

An independent AI review examined the paper argument before formalisation;
this is distinct from human peer review. The Lean contracts and their audit
scope are described in [Appendix A](proof.md#appendix-a-lean-correspondence),
with reproduction instructions in
[Appendix B](proof.md#appendix-b-reuse-boundaries-and-verification).
Neither formal verification nor a gap in an inspected table establishes
historical priority.

## Historical attaining construction

**Daniel M. Gordon / La Jolla Covering Repository**, CC BY 4.0. The historical
(18,10,3) construction has 12 distinct 10-sets. Its source credit is
“JCD article”, with timestamp **1996-11-14 17:08:00**. That article has not
been independently identified here; the timestamp is construction metadata,
not an established discovery or first-publication date.

The complete blocks appear in [Proposition 9](proof.md#8-historical-attainment)
and in the included
[Lean witness](../../lean/CoveringDesigns/C18_10_3/Witness.lean).
The ordered one-based block bytes have SHA-256
`173e0a39baa3814f25da9156a861600b0a791ff4437708d55049c85698b3d28a`.
Lean checks distinctness, block sizes, every triple and arbitrary-label
transport. A historical source assertion is not a theorem premise.

The public archive is [Daniel Gordon's La Jolla Coverings Repository](https://github.com/dmgordo/LJCR),
also archived as [version 1.2, 24 April 2026](https://doi.org/10.5281/zenodo.19735294).
These identify the historical collection; the displayed block list is sufficient
to reproduce this account's construction checks without downloading that collection.

<a id="schonheim-lifting"></a>
## Schönheim lifting

**J. Schönheim**, *On coverings*, Pacific Journal of Mathematics **14**
(1964), 1405–1411, [DOI](https://doi.org/10.2140/pjm.1964.14.1405).
Theorem I, formula (6), and its incidence proof are on printed p.1407
([original scan, PDF page 4](https://msp.org/pjm/1964/14-4/pjm-v14-n4-p29-p.pdf#page=4)).
That page was inspected visually in the dated assessment. The same point-link
count lifts any universally proved residual lower bound.

**Daniel M. Gordon, Greg Kuperberg and Oren Patashnik**, *New constructions
for covering designs*, Journal of Combinatorial Designs **3** (1995),
269–284, [DOI](https://doi.org/10.1002/jcd.3180030404),
[Theorem 1](https://arxiv.org/html/math/9502238#S1), states the recurrence
using the actual residual covering number. The [proof, §9](proof.md#9-schönheim-lifting-and-the-five-consequences)
gives the full argument and all intermediate ceilings. The existing lifting
interfaces are reused unchanged; no new foundational lifting theorem is claimed.

## Dated earlier comparison

The 20 October assessment located the following earlier lower bounds and
matching table entries. The links identify the ordinary covering parameters
using the site's convention $M=T$.

| Parameter | Earlier lower located | Proved here |
|---|---:|---:|
| [C(18,10,3)](https://www.coveringrepository.com/systems.aspx?v=18&k=10&t=3&m=3) | 11 | 12, exact |
| [C(19,11,4)](https://www.coveringrepository.com/systems.aspx?v=19&k=11&t=4&m=4) | 19 | 21 |
| [C(20,12,5)](https://www.coveringrepository.com/systems.aspx?v=20&k=12&t=5&m=5) | 32 | 35 |
| [C(21,13,6)](https://www.coveringrepository.com/systems.aspx?v=21&k=13&t=6&m=6) | 52 | 57 |
| [C(22,14,7)](https://www.coveringrepository.com/systems.aspx?v=22&k=14&t=7&m=7) | 82 | 90 |
| [C(23,15,8)](https://www.coveringrepository.com/systems.aspx?v=23&k=15&t=8&m=8) | 126 | 138 |

The earlier chain has a complete deduction independent of those table entries.
**Daniel Horsley**, *Generalising Fisher's inequality to coverings and packings*,
[arXiv:1409.0485v3, 15 August 2016](https://arxiv.org/html/1409.0485v3),
Theorem 1; Combinatorica **37** (2017), 673–696,
[DOI](https://doi.org/10.1007/s00493-016-3326-9), gives $C(17,9,2)\ge6$.
Indeed $(v,k,\lambda,r,d)=(17,9,1,2,0)$ satisfies its hypotheses, and
$\lceil17\cdot3/10\rceil=6$. Schönheim lifting then gives

$$
\begin{aligned}
\lceil18\cdot6/10\rceil&=11,&
\lceil19\cdot11/11\rceil&=19,&
\lceil20\cdot19/12\rceil&=32,\\
\lceil21\cdot32/13\rceil&=52,&
\lceil22\cdot52/14\rceil&=82,&
\lceil23\cdot82/15\rceil&=126.
\end{aligned}
$$

First-publication dates of these individual numerical consequences were not
established. The assessment also inspected the following related sources:

- **Daniel Horsley and Rakhi Singh**, *New lower bounds for t-coverings*,
  [arXiv:1706.06825v2, 4 October 2017](https://arxiv.org/html/1706.06825v2),
  Journal of Combinatorial Designs **26** (2018), 369–386,
  [DOI](https://doi.org/10.1002/jcd.21591): Lemma 3, Theorems 6, 15 and 18,
  and the comparison tables. Substitutions using the preceding justified
  residual floors did not reach the new bounds; this does not exclude other
  seed choices.
- **D. T. Todorov**, *On some covering designs*, Journal of Combinatorial
  Theory, Series A **39** (1985), 83–101,
  [DOI](https://doi.org/10.1016/0097-3165(85)90084-6): Theorems 1–2 on p.84
  and Theorem 4 on p.87. **Daniel M. Gordon and Douglas R. Stinson**,
  *Coverings*, [handbook manuscript](https://dmgordon.org/papers/hcd.pdf):
  Theorem 1.19 and Tables 1.33, 1.35–1.36. These supply earlier statements
  and tables, not an independently established lower bound of 12 for the seed.
- **Alfonso Gippini Requeijo**, *Sixteen exact covering numbers C(v,k,t)
  from a SAT-certified link decomposition*,
  [version 1.1, 19 October 2026](https://zenodo.org/records/23465708):
  Theorem 1 and Appendix A, Table 5. Its stated results include neither
  this seed nor the five lifting bounds. The paper and reported certification
  were inspected; the computational certificates were not independently replayed.
- **James Chang**, *A structural lower bound for C(24,14,4)*,
  [paper and Lean repository](https://github.com/jamesyc/covering),
  [palomar-v2 release](https://github.com/jamesyc/covering/releases/tag/palomar-v2):
  Theorem 1.1 and Corollary 5.2 give bounds at (24,14,4) and (25,15,5).
  The displayed formal statements were inspected without rebuilding them.
  Their point–block-size difference is 10, whereas this account's chain has
  difference 8; ordinary point-link lifting preserves that difference.

No matching earlier claim or complete deduction was located in that bounded
assessment. This is a limit of the search, not proof of first discovery or
an exhaustive survey of the literature.

<a id="historical-priority-limitation"></a>
## Historical priority limitation

One unresolved comparison concerns the Mills–Mullin result quoted in
Horsley–Singh v2, printed p.2, equation (3). Its literal formula, with $r$
inside the $v/k$ factor under the ceiling, cannot be used as printed.
At $(v,k,t)=(7,4,2)$ and $r=2$, the stated residual equalities use
$C(6,3,1)=2$ and $C(5,2,0)=1$, and $7\cdot2$ is nonzero modulo 4.
The literal conclusion would require at least 7 blocks, but the following
5 distinct 4-sets cover all pairs on seven points:

$$
\{1,2,3,4\},\quad\{1,2,5,6\},\quad\{3,4,5,6\},\quad
\{1,3,5,7\},\quad\{2,4,6,7\}.
$$

The first three cover all pairs on $\{1,\ldots,6\}$, and the last two
cover every pair through 7. This finite diagnostic concerns the printed
quotation; it does **not** refute the unread original theorem. No corrected
formula is guessed or used in the proof.

Independently, the quotation's equality premise concerns actual covering
minima. A lower bound such as $C(19,11,4)\ge19$ does not establish equality,
so treating it as an exact residual value would be unjustified.
The following originals remained unavailable to the assessment:

- **W. H. Mills and R. C. Mullin**, *Coverings and packings*, in
  *Contemporary Design Theory* (1992), pp.371–399.
- **W. H. Mills**, *Covering designs I: Coverings by a small number of subsets*,
  Ars Combinatoria **8** (1979), 199–315.
- **Todorov and Tonchev**, *On some coverings of triples*,
  C. R. Acad. Bulgare Sci. **35** (1982), 1209–1211.

These access gaps qualify historical priority. None is a mathematical or
formal prerequisite for the self-contained proof of the seed or its five
corollaries.
