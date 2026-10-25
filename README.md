# Covering designs

[![Lean verification](https://github.com/renidrag/covering/actions/workflows/lean-verification.yml/badge.svg)](https://github.com/renidrag/covering/actions/workflows/lean-verification.yml)

**Rob Gardiner**

This project publishes new covering-number results that I have found,
together with reconstructed proofs and explicit constructions of established
results.

A $(v,k,t)$ covering is a family of distinct $k$-element blocks on $v$ points
that covers every $t$-element subset. The smallest possible number of blocks
is $C(v,k,t)$.

## $C(19,9,3)=17$

Proof of **$C(19,9,3)=17$** by showing that 16 blocks
cannot cover all triples. Rade Belic's known construction uses 17 blocks.
Lean verifies both parts of the proof.

The links at minimum-degree points must agree on their shared blocks.
This forces 8 points with the plane structure of AG(3,2). Counting the
supports of the other 11 points then forces an uncovered triple. The
supporting classification of (18,8,2) coverings with 7 blocks is included,
with credit to the earlier results.

The lower bound also holds when block occurrences repeat. Belic's 17
distinct blocks cover all **969 triples**, and the result holds on any
set of 19 points.

- [Read the result and proof outline](coverings/19-9-3/README.md).
- [Read the mathematical proof and Lean correspondence](coverings/19-9-3/proof.md).
- [Read the sources and construction attribution](coverings/19-9-3/sources.md).
- [View Belic's 17-block construction](data/c1993-belic-17.blocks.txt).

## $C(34,18,3)=13$ and 10 improved lower bounds

I proved **$C(34,18,3)=13$** by combining my lower bound for
$C(2k-2,k,3)$ with a known 13-block construction. LJCR recorded the
construction in 2009 as a multiple of a (17,9,3) covering. With AI
assistance, I verified both the proof and construction in Lean for any
set of 34 points.

Applying Schönheim's bound repeatedly to two previously proved lower
bounds gives 10 further results:

| From $C(14,5,3)\ge41$ | From $C(34,18,3)\ge13$ |
|---|---|
| $C(15,6,4)\ge103$ | $C(35,19,4)\ge24$ |
| $C(16,7,5)\ge236$ | $C(36,20,5)\ge44$ |
| $C(17,8,6)\ge502$ | $C(37,21,6)\ge78$ |
| $C(18,9,7)\ge1004$ | $C(38,22,7)\ge135$ |
| $C(19,10,8)\ge1908$ | $C(39,23,8)\ge229$ |

Each step uses the previous bound and rounds up to an integer. The accounts
include the proofs, credit Schönheim's method and compare the results with
the repository entries checked on 23 October 2026.

- [Read the proof of C(34,18,3)=13](coverings/34-18-3/proof.md) and
  [construction sources](coverings/34-18-3/sources.md).
- [Read the 5 bounds from C(14,5,3)≥41](coverings/19-10-8/README.md).
- [Read the 5 bounds from C(34,18,3)≥13](coverings/39-23-8/README.md).

## Lower bound: $C(14,5,3)\ge41$

I proved **$C(14,5,3)\ge41$**. A known 43-block construction gives
$41\le C(14,5,3)\le43$, improving the 37–43 interval in the repository
entry checked on 21 October 2026. The exact value is not yet known.

My contribution, developed with AI assistance, is the structural lower-bound
argument and Lean formalisation. The proof combines exact point links,
completion counts, a removable-block lemma and compatibility between links.
The historical upper construction is credited to Nurmela and Östergård and
is independently checked in Lean.

- [Read the result and proof outline](coverings/14-5-3/README.md).
- [Read the structural proof and Lean correspondence](coverings/14-5-3/proof.md).
- [Read the sources and attribution](coverings/14-5-3/sources.md).

## Exact values for $C(12u+1,4,3)$, $1\le u\le8$

For $n=12u+1$ with $1\le u\le8$, the library proves
$C(n,4,3)=n(n-1)^2/24$. This covers every $n\equiv1\pmod{12}$ with
$4\le n<100$. For each value, Lean verifies the lower bound and a
construction with that many blocks. The checked block list is available
to download.

| Covering | Exact value |
|---|---:|
| $C(13,4,3)$ | 78 |
| $C(25,4,3)$ | 600 |
| $C(37,4,3)$ | 1,998 |
| $C(49,4,3)$ | 4,704 |
| $C(61,4,3)$ | 9,150 |
| $C(73,4,3)$ | 15,768 |
| $C(85,4,3)$ | 24,990 |
| $C(97,4,3)$ | 37,248 |

These exact values were proved in earlier work. Mills's 1974 construction
result, reported by Hartman–Mills–Mullin, covers this entire congruence
class; Schönheim's bound shows that the constructions are optimal. With
AI assistance, I reconstructed the method, generated 6 optimal block lists
and verified all 8 values in Lean, using recovered lists for the other 2.
Each distributed list is checked against the corresponding Lean construction.

The preserved La Jolla Covering Repository (LJCR) snapshot listed larger
constructions for $n=37,49,61,73,85,97$, although the exact values were already
known. In the sources inspected, I found construction recipes but did not
locate complete optimal block lists for those 6 values of n. The reconstructed
lists use 3, 4, 5, 6, 7 and 8 fewer blocks respectively. The linked
sources give the comparison and describe where I searched.

- [Read the 8 cases and download the block lists](coverings/12u-plus-1-4-3/README.md).
- [Read the mathematical proof and Lean correspondence](coverings/12u-plus-1-4-3/proof.md).
- [Read the sources, attribution and dated comparison](coverings/12u-plus-1-4-3/sources.md).

## $C(18,10,3)=12$ and 5 further lower bounds

**21 October 2026.** I proved **$C(18,10,3)=12$** by ruling out 11
blocks. A known construction uses 12 blocks. Repeatedly applying
Schönheim's bound gives 5 further lower bounds. All 6 results are
formalised in Lean 4.

| Covering | Proved conclusion |
|---|---|
| $C(18,10,3)$ | $12$ (exact) |
| $C(19,11,4)$ | $\ge21$ |
| $C(20,12,5)$ | $\ge35$ |
| $C(21,13,6)$ | $\ge57$ |
| $C(22,14,7)$ | $\ge90$ |
| $C(23,15,8)$ | $\ge138$ |

My contribution is the structural lower-bound proof and its Lean
formalisation, developed with AI assistance. The proof combines incidence
counting, equality in a matrix-rank bound and constraints on shared block
supports to force an uncovered triple. The higher-strength bounds follow
from Schönheim's argument, with rounding at each step.

- [Read the mathematical proof and Lean correspondence](coverings/18-10-3/proof.md).
- [Read the proof outline and formal statements](coverings/18-10-3/README.md).
- [Read the sources and construction attribution](coverings/18-10-3/sources.md).

## Lower bounds and exact values for $C(2k-c,k,3)$

**19 October 2026.** Structural lower bounds, formalised in Lean 4, give the
following results. For each exact value, a construction with that many
distinct blocks is included.

| Covering | Parameter range | Proved conclusion |
|---|---|---|
| $C(20,11,3)$ | — | $12$ |
| $C(2k-2,k,3)$ | $17\le k\le30$ | $13\le C\le14$ |
| $C(2k-2,k,3)$ | $k\ge31$ | $14$ |
| $C(2k-3,k,3)$ | $k\ge59$ | $14$ |
| $C(2k-c,k,3)$ | $c\ge2,\ k\ge25c$ | $14$ |

My contribution is the structural lower-bound arguments and their Lean
formalisation, developed with AI assistance. The proofs combine incidence
counting, constraints on shared blocks, and matrix rank. Known constructions
give the upper bounds. The account includes its mathematical prerequisites
and all supporting Lean modules.

- [Read the mathematical proof](coverings/2k-minus-c-k-3/proof.md).
- [Read the parameter ranges and proof outline](coverings/2k-minus-c-k-3/README.md).
- [Read the sources and attribution](coverings/2k-minus-c-k-3/sources.md).

## $C(13,7,4)=30$

**13 October 2026.** I proved **$C(13,7,4)=30$** by showing that fewer
than 30 blocks cannot cover all 4-element subsets. The known 30-block
construction is credited to Nurmela and Östergård (1993). My contribution
is the structural lower-bound proof and its Lean 4 formalisation.

The public sources checked for this work reported
$28 \le C(13,7,4) \le 30$. The [source history below](#prior-results-and-sources)
describes those records and the limits of the search.

- [Read the mathematical proof](coverings/13-7-4/proof.md).
- [Read the proof outline and formal statement](coverings/13-7-4/README.md).
- [View the 30-block construction](data/ljcr-30-one-based.txt).

## Supporting proofs of established results

These accounts reconstruct known results and formalise them in Lean.
They contain the supporting proofs needed for $C(13,7,4)=30$; each explains
which parts follow the original papers and which arguments were changed.

| Result | Supporting proof |
|---|---|
| [$C(11,5,2)=7$](coverings/11-5-2/README.md) | Stanton's classification into exactly two minimum isomorphism types |
| [$C(12,6,3)=15$](coverings/12-6-3/README.md) | The minimum and structural classification of Gordon, Patashnik, Petro and Taylor (GPPT) |

- **Stanton:** the proof develops my structural reconstruction, with
  shortenings made during formalisation. Stanton's original chapter has not
  been obtained, so I do not claim to reproduce his argument.
- **GPPT:** minimum-pair compatibility and the repeated-triple branch follow
  GPPT, with revised counting. The numerical lower bound is derived from
  compatibility. The branch with no repeated triple of minimum points replaces
  GPPT's argument with projection, Fano-plane geometry and a seven-point cap
  lemma.

These choices make the prerequisites self-contained and reusable in Lean.
The [Stanton](coverings/11-5-2/proof.md#sources-and-contribution) and
[GPPT](coverings/12-6-3/proof.md#sources-and-contribution) source comparisons
identify the established results and the arguments followed or replaced;
no historical novelty is claimed for these supporting arguments.

The proof of $C(13,7,4)=30$ uses the structural results of these two proofs.
It is independent of the separate catalogue calculation described on the
$C(12,6,3)$ page.

## Verification

[GitHub Actions](.github/workflows/lean-verification.yml) rebuilds and verifies
all included Lean proofs, including their theorem, axiom and dependency audits.
Branch pushes changing only citation metadata or the documentation listed in
the [verification guide](technical-details.md#github-actions) skip the workflow,
including DOI and release-history updates.
Changes to proofs, construction data, manifests, tools or workflow configuration
still run verification. Pull requests, tag pushes and manual runs also verify.
The badge above reports the workflow's live status; a passing run confirms
successful verification of that run's revision. Click it to inspect the run
and download its verification records and logs.

The [verification guide](technical-details.md) explains how to build and
check the published Lean proofs, including their axiom and dependency audits.
The [formal sources](lean/CoveringDesigns/) and explicit constructions are
included in this repository.

## Prior results and sources

<details>
<summary>Historical constructions, search attempts and recorded bounds</summary>

- **30-block construction.** The documented credit is to Kari J. Nurmela
  and Patric R. J. Östergård, *Upper bounds for covering designs by simulated
  annealing*, *Congressus Numerantium* 96 (1993), 93–111.
  Daniel M. Gordon, Greg Kuperberg and Oren Patashnik,
  [*New constructions for covering designs*](https://doi.org/10.1002/jcd.3180030404),
  *Journal of Combinatorial Designs* 3(4) (1995), 269–284, records the bound.
  In its [preprint](https://arxiv.org/pdf/math/9502238#page=7), Table 4 lists
  30 for $C(13,7,4)$ with method code *n*. The key credits that code to
  Nurmela–Östergård simulated annealing, and reference 23 cites their 1993 paper.

  The exact first publication date has not been established. The original
  1993 article and their January 1993 Technical Report B10 have not been
  inspected, so the bound's appearance in that earlier report is unconfirmed.

- **La Jolla Covering Repository (LJCR).** Historical snapshots are available
  from [2024](https://zenodo.org/records/10779737) and
  [2026](https://zenodo.org/records/19735294). The 2026 archive's
  $C(13,7,4)$ record gives bounds 28–30 and contains a 30-block entry
  dated **14 November 1996**, labelled “JCD article”. This is a repository
  record date, not the construction's publication date.

- **Earlier heuristic search.** Chaoying Dai, (Ben) Pak Ching Li and
  Michel Toulouse,
  [*A Multilevel Cooperative Tabu Search Algorithm for the Covering Design Problem*](https://w1.cirrelt.ca/~toulouse/CD-BL-MT.pdf#page=30).
  Table 3, printed page 28 / PDF page 30, reports bounds 28–30. Its
  29-block candidate has cost 3 and is an incomplete covering.

- **Other status listings.** The
  [Covering Repository](https://www.coveringrepository.com/) describes its
  import of historical LJCR data through March 2026. The
  [HorizonMath baseline](https://github.com/EnvCommons/HorizonMath/blob/main/baselines.json)
  also lists bounds 28–30 and references LJCR.

The source search does not exclude unpublished or unlocated prior work,
and does not by itself establish publication priority.

</details>
