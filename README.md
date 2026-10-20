# Covering designs

[![Lean verification](https://github.com/renidrag/covering/actions/workflows/lean-verification.yml/badge.svg)](https://github.com/renidrag/covering/actions/workflows/lean-verification.yml)

**Rob Gardiner**

This project publishes new covering-number results that I have found,
together with supporting proofs of established results.

A $(v,k,t)$ covering is a family of distinct $k$-element blocks on $v$ points
that covers every $t$-element subset. The smallest possible number of blocks
is $C(v,k,t)$.

## Lower bounds and exact values for $C(2k-c,k,3)$

**19 October 2026.** Structural lower bounds, formalised in Lean 4, give the
following results. Every equality includes an attaining ordinary covering.

| Covering | Parameter range | Proved conclusion |
|---|---|---|
| $C(20,11,3)$ | — | $12$ |
| $C(2k-2,k,3)$ | $17\le k\le34$ | $13\le C\le14$ |
| $C(2k-2,k,3)$ | $k\ge35$ | $14$ |
| $C(2k-3,k,3)$ | $k\ge59$ | $14$ |
| $C(2k-c,k,3)$ | $c\ge2,\ k\ge25c$ | $14$ |

My contribution is the structural lower-bound arguments and their Lean
formalisation, developed with AI assistance. The proofs combine incidence
counting, constraints on shared blocks, and matrix rank. Known constructions
supply the upper bounds. The account includes its mathematical prerequisites
and all supporting Lean modules.

- [Read the mathematical proof](coverings/2k-minus-c-k-3/proof.md).
- [Read the parameter ranges and proof outline](coverings/2k-minus-c-k-3/README.md).
- [Read the sources and attribution](coverings/2k-minus-c-k-3/sources.md).

## New result: $C(13,7,4)=30$

**13 October 2026.** Covering every four-element subset of thirteen points
with seven-element blocks requires at least thirty blocks.

My contribution is a structural proof of this lower bound, formalised in
Lean 4. The thirty-block construction credited to Nurmela and Östergård
(1993) supplies the upper bound, giving the exact value thirty.

The public sources checked for this work reported
$28 \le C(13,7,4) \le 30$. The [source history below](#prior-results-and-sources)
describes those records and the limits of the search.

- [Read the mathematical proof](coverings/13-7-4/proof.md).
- [Read the proof outline and formal statement](coverings/13-7-4/README.md).
- [View the thirty-block construction](data/ljcr-30-one-based.txt).

## Supporting proofs of established results

**These are self-contained proofs of known results, reconstructed and
formalised in Lean. They are not literal translations of the original
papers.** They provide the proved prerequisites for $C(13,7,4)=30$.

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

The thirteen-point argument uses the structural results of these two proofs.
It is independent of the separate catalogue calculation described on the
twelve-point page.

## Verification

[GitHub Actions](.github/workflows/lean-verification.yml) rebuilds and verifies
all included Lean proofs on every push and pull request, including their
theorem, axiom and dependency audits. The badge above reports the workflow's live
status; a passing run confirms successful verification of that run's revision.
Click it to inspect the run and download its verification records and logs.

The [verification guide](technical-details.md) explains how to build and
check the published Lean proofs, including their axiom and dependency audits.
The [formal sources](lean/CoveringDesigns/) and explicit constructions are
included in this repository.

## Prior results and sources

<details>
<summary>Historical constructions, search attempts and recorded bounds</summary>

- **Thirty-block construction.** The documented credit is to Kari J. Nurmela
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
  $C(13,7,4)$ record gives bounds 28–30 and contains a thirty-block entry
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
