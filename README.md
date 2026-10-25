# Covering designs

[![Lean verification](https://github.com/renidrag/covering/actions/workflows/lean-verification.yml/badge.svg)](https://github.com/renidrag/covering/actions/workflows/lean-verification.yml)

**Rob Gardiner**

This project publishes new covering-number results that I have found,
together with reconstructed proofs and explicit constructions of established
results.

A $(v,k,t)$ covering is a family of distinct $k$-element blocks on $v$ points
that covers every $t$-element subset. The smallest possible number of blocks
is $C(v,k,t)$.

The results below are proved in Lean. Each account gives the mathematical
argument, construction provenance and attribution. OpenAI language models
assisted the development, formalisation, checking and writing.

“Published here” records the first public appearance of the stated result
in this repository. For a strengthened range, it dates that range.
The [release history](RELEASE_HISTORY.md) links earlier statements, exact
snapshots and archived versions. “Next release” marks additions prepared
for publication.

## Exact values

Each equality includes a checked construction with the stated number of blocks.

| Result | Published here | Release | Proof |
|---|---|---|---|
| [$C(13,7,4)=30$](coverings/13-7-4/README.md) | 15 Oct 2026 | [v1.0.0] | [Proof](coverings/13-7-4/proof.md) |
| [$C(18,10,3)=12$](coverings/18-10-3/README.md) | 21 Oct 2026 | [v1.3.0] | [Proof](coverings/18-10-3/proof.md) |
| [$C(19,9,3)=17$](coverings/19-9-3/README.md) | 25 Oct 2026 | [v1.6.0] | [Proof](coverings/19-9-3/proof.md) |
| [$C(20,11,3)=12$](coverings/2k-minus-c-k-3/README.md) | 19 Oct 2026 | [v1.1.0] | [Proof](coverings/2k-minus-c-k-3/proof.md) |
| [$C(34,18,3)=13$](coverings/34-18-3/README.md) | 24 Oct 2026 | [v1.5.0] | [Proof](coverings/34-18-3/proof.md) |
| [$C(2k-2,k,3)=14,\quad k\ge31$](coverings/2k-minus-c-k-3/README.md) | 20 Oct 2026 | [v1.2.0] | [Proof](coverings/2k-minus-c-k-3/proof.md) |
| [$C(2k-3,k,3)=14,\quad k\ge59$](coverings/2k-minus-c-k-3/README.md) | 19 Oct 2026 | [v1.1.0] | [Proof](coverings/2k-minus-c-k-3/proof.md) |
| [$C(2k-c,k,3)=14,\quad c\ge2,\ k\ge25c$](coverings/2k-minus-c-k-3/README.md) | 19 Oct 2026 | [v1.1.0] | [Proof](coverings/2k-minus-c-k-3/proof.md) |

## Lower bounds

| Result | Published here | Release | Proof |
|---|---|---|---|
| [$C(14,5,3)\ge41$](coverings/14-5-3/README.md) | 22 Oct 2026 | [v1.4.0] | [Proof](coverings/14-5-3/proof.md) |
| [$C(15,6,4)\ge103$](coverings/15-6-4/README.md) | 24 Oct 2026 | [v1.5.0] | [Proof](coverings/15-6-4/proof.md) |
| [$C(16,7,5)\ge236$](coverings/16-7-5/README.md) | 24 Oct 2026 | [v1.5.0] | [Proof](coverings/16-7-5/proof.md) |
| [$C(17,8,6)\ge502$](coverings/17-8-6/README.md) | 24 Oct 2026 | [v1.5.0] | [Proof](coverings/17-8-6/proof.md) |
| [$C(18,9,7)\ge1004$](coverings/18-9-7/README.md) | 24 Oct 2026 | [v1.5.0] | [Proof](coverings/18-9-7/proof.md) |
| [$C(19,10,8)\ge1908$](coverings/19-10-8/README.md) | 24 Oct 2026 | [v1.5.0] | [Proof](coverings/19-10-8/proof.md) |
| [$C(19,11,4)\ge21$](coverings/18-10-3/README.md) | 21 Oct 2026 | [v1.3.0] | [Proof](coverings/18-10-3/proof.md#9-schönheim-lifting-and-the-five-consequences) |
| [$C(20,12,5)\ge35$](coverings/18-10-3/README.md) | 21 Oct 2026 | [v1.3.0] | [Proof](coverings/18-10-3/proof.md#9-schönheim-lifting-and-the-five-consequences) |
| [$C(21,13,6)\ge57$](coverings/18-10-3/README.md) | 21 Oct 2026 | [v1.3.0] | [Proof](coverings/18-10-3/proof.md#9-schönheim-lifting-and-the-five-consequences) |
| [$C(22,14,7)\ge90$](coverings/18-10-3/README.md) | 21 Oct 2026 | [v1.3.0] | [Proof](coverings/18-10-3/proof.md#9-schönheim-lifting-and-the-five-consequences) |
| [$C(23,15,8)\ge138$](coverings/18-10-3/README.md) | 21 Oct 2026 | [v1.3.0] | [Proof](coverings/18-10-3/proof.md#9-schönheim-lifting-and-the-five-consequences) |
| [$C(32,7,3)\ge149$](coverings/q2-plus-q-plus-2-q-plus-2-3/README.md) | — | Next release | [Proof](coverings/q2-plus-q-plus-2-q-plus-2-3/proof.md) |
| [$C(35,19,4)\ge24$](coverings/35-19-4/README.md) | 24 Oct 2026 | [v1.5.0] | [Proof](coverings/35-19-4/proof.md) |
| [$C(36,20,5)\ge44$](coverings/36-20-5/README.md) | 24 Oct 2026 | [v1.5.0] | [Proof](coverings/36-20-5/proof.md) |
| [$C(37,21,6)\ge78$](coverings/37-21-6/README.md) | 24 Oct 2026 | [v1.5.0] | [Proof](coverings/37-21-6/proof.md) |
| [$C(38,22,7)\ge135$](coverings/38-22-7/README.md) | 24 Oct 2026 | [v1.5.0] | [Proof](coverings/38-22-7/proof.md) |
| [$C(39,23,8)\ge229$](coverings/39-23-8/README.md) | 24 Oct 2026 | [v1.5.0] | [Proof](coverings/39-23-8/proof.md) |
| [$C(58,9,3)\ge375$](coverings/q2-plus-q-plus-2-q-plus-2-3/README.md) | — | Next release | [Proof](coverings/q2-plus-q-plus-2-q-plus-2-3/proof.md) |
| [$C(92,11,3)\ge774$](coverings/q2-plus-q-plus-2-q-plus-2-3/README.md) | — | Next release | [Proof](coverings/q2-plus-q-plus-2-q-plus-2-3/proof.md) |
| [$13\le C(2k-2,k,3)\le14,\quad k\ge17$](coverings/2k-minus-c-k-3/README.md) | 20 Oct 2026 | [v1.2.0] | [Proof](coverings/2k-minus-c-k-3/proof.md) |
| [$C(n+1,q+2,3)\ge n+\lceil N/M\rceil,\quad q\ge3\text{ odd}$](coverings/q2-plus-q-plus-2-q-plus-2-3/README.md) | — | Next release | [Proof](coverings/q2-plus-q-plus-2-q-plus-2-3/proof.md) |

In the final row, $n=q^2+q+1$, $N=nq^3(q+1)/6$ and
$M=\binom{q+2}{3}-\lceil q/4\rceil$. The
[account](coverings/q2-plus-q-plus-2-q-plus-2-3/README.md) gives the general
proof and the three numerical applications. Published geometric arguments
already imply 149 and 375; the parity estimate strengthens the corresponding
deduction for $C(92,11,3)$ from 770 to 774.

## Reconstructed results and supporting proofs

These results were established in earlier work. The accounts give reconstructed
proofs, Lean verification and attribution.

For $n=12u+1$ with $1\le u\le8$, the exact value is $n(n-1)^2/24$.
The [8 block lists](coverings/12u-plus-1-4-3/README.md) are included: 6
were reconstructed from published methods and 2 recovered from historical
sources. Each list is checked against its Lean construction.

| Result | Published here | Release | Proof |
|---|---|---|---|
| [$C(13,4,3)=78$](coverings/12u-plus-1-4-3/README.md) | 22 Oct 2026 | [v1.4.0] | [Proof](coverings/12u-plus-1-4-3/proof.md) |
| [$C(25,4,3)=600$](coverings/12u-plus-1-4-3/README.md) | 22 Oct 2026 | [v1.4.0] | [Proof](coverings/12u-plus-1-4-3/proof.md) |
| [$C(37,4,3)=1{,}998$](coverings/12u-plus-1-4-3/README.md) | 22 Oct 2026 | [v1.4.0] | [Proof](coverings/12u-plus-1-4-3/proof.md) |
| [$C(49,4,3)=4{,}704$](coverings/12u-plus-1-4-3/README.md) | 22 Oct 2026 | [v1.4.0] | [Proof](coverings/12u-plus-1-4-3/proof.md) |
| [$C(61,4,3)=9{,}150$](coverings/12u-plus-1-4-3/README.md) | 22 Oct 2026 | [v1.4.0] | [Proof](coverings/12u-plus-1-4-3/proof.md) |
| [$C(73,4,3)=15{,}768$](coverings/12u-plus-1-4-3/README.md) | 22 Oct 2026 | [v1.4.0] | [Proof](coverings/12u-plus-1-4-3/proof.md) |
| [$C(85,4,3)=24{,}990$](coverings/12u-plus-1-4-3/README.md) | 22 Oct 2026 | [v1.4.0] | [Proof](coverings/12u-plus-1-4-3/proof.md) |
| [$C(97,4,3)=37{,}248$](coverings/12u-plus-1-4-3/README.md) | 22 Oct 2026 | [v1.4.0] | [Proof](coverings/12u-plus-1-4-3/proof.md) |
| [$C(11,5,2)=7\text{; 2 minimum forms}$](coverings/11-5-2/README.md) | 15 Oct 2026 | [v1.0.0] | [Proof](coverings/11-5-2/proof.md) |
| [$C(12,6,3)=15\text{; minimum coverings classified}$](coverings/12-6-3/README.md) | 15 Oct 2026 | [v1.0.0] | [Proof](coverings/12-6-3/proof.md) |
| [$C(7a+4,3a+2,2)=7,\ a\ge1\text{; 2 minimum forms}$](coverings/seven-block/README.md) | 25 Oct 2026 | [v1.6.0] | [Proof](coverings/seven-block/proof.md) |

## Verification

[GitHub Actions](.github/workflows/lean-verification.yml) rebuilds the included
Lean proofs and checks their theorem contracts, axioms and dependencies.
Branch pushes changing only citation metadata or the documentation listed in
the [verification guide](technical-details.md#github-actions) skip the workflow.
Proof, data, manifest, tool and workflow changes still run verification;
pull requests, tag pushes and manual runs also verify. A passing run applies
to that run's revision. The badge links to the runs, records and logs.

The [verification guide](technical-details.md) explains how to reproduce the
checks. The [Lean sources](lean/CoveringDesigns/) and construction data are
included in this repository.

## Citation and release history

Use the [citation metadata](CITATION.cff) to cite the package. The
[collection DOI](https://doi.org/10.5281/zenodo.23511135) covers all versions;
the [release history](RELEASE_HISTORY.md) gives the dates, exact snapshots and
version DOIs for individual results.

[v1.0.0]: https://github.com/renidrag/covering/releases/tag/v1.0.0
[v1.1.0]: https://github.com/renidrag/covering/releases/tag/v1.1.0
[v1.2.0]: https://github.com/renidrag/covering/releases/tag/v1.2.0
[v1.3.0]: https://github.com/renidrag/covering/releases/tag/v1.3.0
[v1.4.0]: https://github.com/renidrag/covering/releases/tag/v1.4.0
[v1.5.0]: https://github.com/renidrag/covering/releases/tag/v1.5.0
[v1.6.0]: https://github.com/renidrag/covering/releases/tag/v1.6.0
