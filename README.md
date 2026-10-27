# Covering designs

[![Lean verification](https://github.com/renidrag/covering/actions/workflows/lean-verification.yml/badge.svg)](https://github.com/renidrag/covering/actions/workflows/lean-verification.yml)

**Rob Gardiner**

This project publishes new covering-number results that I have proved,
together with reconstructed proofs and explicit constructions of established
results.

A $(v,k,t)$ covering is a family of distinct $k$-element blocks on $v$ points
that covers every $t$-element subset. The smallest possible number of blocks
is $C(v,k,t)$.

The results below are proved in Lean. Each account gives the mathematical
proof, construction provenance and attribution. OpenAI language models
assisted the development, formalisation, checking and writing.

The catalogue contains **205 Lean-verified numerical results for \(v<100\), \(k<25\) and \(t<9\), including 34 exact values**. It brings together improved bounds and exactness proofs, alongside reconstructed proofs and explicit constructions of established results.

The [numerical index](RESULTS.md) lists all results ordered by strength and parameters. Its [JSON inventory](RESULTS.json)
provides proof references, methods, seeds, ceiling chains and dated comparisons
for research and ablation studies. The principal results and families are below.

“Published here” dates the first appearance of the precise statement in this
repository. The v2.0.0 entries are prepared for publication; their public dates
will be recorded after release. The [release history](RELEASE_HISTORY.md)
retains earlier statements, exact snapshots and archived versions.

## Exact values and families

Each equality includes an attaining construction.

| Result | Published here | Release | Account and proof |
|---|---|---|---|
| $C(13,7,4)=30$ | 15 Oct 2026 | [v1.0.0] | [Account](coverings/13-7-4/README.md) · [Proof](coverings/13-7-4/proof.md) |
| $C(18,10,3)=12$ | 21 Oct 2026 | [v1.3.0] | [Account](coverings/18-10-3/README.md) · [Proof](coverings/18-10-3/proof.md) |
| $C(19,9,3)=17$ | 25 Oct 2026 | [v1.6.0] | [Account](coverings/19-9-3/README.md) · [Proof](coverings/19-9-3/proof.md) |
| $C(20,11,3)=12$ | 19 Oct 2026 | [v1.1.0] | [Account](coverings/2k-minus-c-k-3/README.md) · [Proof](coverings/2k-minus-c-k-3/proof.md) |
| $C(34,18,3)=13$ | 24 Oct 2026 | [v1.5.0] | [Account](coverings/34-18-3/README.md) · [Proof](coverings/34-18-3/proof.md) |
| $C(2k-2,k,3)=14,\quad k\ge31$ | 20 Oct 2026 | [v1.2.0] | [Account](coverings/2k-minus-c-k-3/README.md) · [Proof](coverings/2k-minus-c-k-3/proof.md) |
| $C(2k-3,k,3)=14,\quad k\ge59$ | 19 Oct 2026 | [v1.1.0] | [Account](coverings/2k-minus-c-k-3/README.md) · [Proof](coverings/2k-minus-c-k-3/proof.md) |
| $C(2k-c,k,3)=14,\quad c\ge2,\ k\ge25c$ | 19 Oct 2026 | [v1.1.0] | [Account](coverings/2k-minus-c-k-3/README.md) · [Proof](coverings/2k-minus-c-k-3/proof.md) |
| $C(4k,k,2)=20$ if $4\mid k$, otherwise $21$, for $k\ge8$ | — | v2.0.0 (prepared) | [Account](coverings/4k-k-2/README.md) · [Proof](coverings/4k-k-2/proof.md) |
| $C(55,11,2)=31$ | — | v2.0.0 (prepared) | [Account](coverings/qk-k-2/README.md) · [Proof](coverings/qk-k-2/proof.md#4-seven-exact-values-and-the-separate-bound) |
| $C(56,8,2)=57$ | — | v2.0.0 (prepared) | [Account](coverings/qk-k-2/README.md) · [Proof](coverings/qk-k-2/proof.md#4-seven-exact-values-and-the-separate-bound) |
| $C(65,13,2)=31$ | — | v2.0.0 (prepared) | [Account](coverings/qk-k-2/README.md) · [Proof](coverings/qk-k-2/proof.md#4-seven-exact-values-and-the-separate-bound) |
| $C(80,16,2)=31$ | — | v2.0.0 (prepared) | [Account](coverings/qk-k-2/README.md) · [Proof](coverings/qk-k-2/proof.md#4-seven-exact-values-and-the-separate-bound) |
| $C(85,17,2)=31$ | — | v2.0.0 (prepared) | [Account](coverings/qk-k-2/README.md) · [Proof](coverings/qk-k-2/proof.md#4-seven-exact-values-and-the-separate-bound) |
| $C(90,10,2)=91$ | — | v2.0.0 (prepared) | [Account](coverings/qk-k-2/README.md) · [Proof](coverings/qk-k-2/proof.md#4-seven-exact-values-and-the-separate-bound) |
| $C(95,19,2)=31$ | — | v2.0.0 (prepared) | [Account](coverings/qk-k-2/README.md) · [Proof](coverings/qk-k-2/proof.md#4-seven-exact-values-and-the-separate-bound) |
| $C(v,k,2)=q^2+q+1,\quad qk<v\le qk+r$ | — | v2.0.0 (prepared) | [Account](coverings/qk-k-2/README.md) · [Proof](coverings/qk-k-2/proof.md#3-actual-constructions-and-exact-intervals) |

For the weighted interval, q is a prime power with q≥2, k=qu+r and 1≤r≤u.
The endpoint v=qk has separate hypotheses in the linked proof.
The [pair-results index](RESULTS.md#strength-2) also lists the twelve numerical
applications of the C(4k,k,2) family in the current batch.

## Lower bounds

| Result | Published here | Release | Account and proof |
|---|---|---|---|
| $C(14,5,3)\ge41$ | 22 Oct 2026 | [v1.4.0] | [Account](coverings/14-5-3/README.md) · [Proof](coverings/14-5-3/proof.md) |
| $13\le C(2k-2,k,3)\le14,\quad k\ge17$ | 20 Oct 2026 | [v1.2.0] | [Account](coverings/2k-minus-c-k-3/README.md) · [Proof](coverings/2k-minus-c-k-3/proof.md) |
| $C(32,7,3)\ge149$ | 25 Oct 2026 | [v1.7.0] | [Account](coverings/q2-plus-q-plus-2-q-plus-2-3/README.md) · [Proof](coverings/q2-plus-q-plus-2-q-plus-2-3/proof.md) |
| $C(58,9,3)\ge375$ | 25 Oct 2026 | [v1.7.0] | [Account](coverings/q2-plus-q-plus-2-q-plus-2-3/README.md) · [Proof](coverings/q2-plus-q-plus-2-q-plus-2-3/proof.md) |
| $C(92,11,3)\ge774$ | 25 Oct 2026 | [v1.7.0] | [Account](coverings/q2-plus-q-plus-2-q-plus-2-3/README.md) · [Proof](coverings/q2-plus-q-plus-2-q-plus-2-3/proof.md) |
| $C(70,14,2)\ge31$ | — | v2.0.0 (prepared) | [Account](coverings/qk-k-2/README.md) · [Proof](coverings/qk-k-2/proof.md) |
| $C(6k,k,2)\ge43,\quad k\ge6$ | — | v2.0.0 (prepared) | [Account](coverings/6k-k-2/README.md) · [Proof](coverings/6k-k-2/proof.md) |

The [projective-link account](coverings/q2-plus-q-plus-2-q-plus-2-3/README.md)
proves the odd-q family underlying 149, 375 and 774. The
[C(2k−c,k,3) account](coverings/2k-minus-c-k-3/README.md) includes
the general inequalities behind its numerical thresholds.

The [full index](RESULTS.md) includes the five lifts from each of
C(18,10,3)≥12, C(14,5,3)≥41 and C(34,18,3)≥13, and the
[151 pair-derived bounds](coverings/qk-k-2/bounds.md).

## Reconstructed results and supporting proofs

These accounts reconstruct established results and record their attribution.

| Result | Published here | Release | Account and proof |
|---|---|---|---|
| $C(11,5,2)=7\text{; 2 minimum forms}$ | 15 Oct 2026 | [v1.0.0] | [Account](coverings/11-5-2/README.md) · [Proof](coverings/11-5-2/proof.md) |
| $C(12,6,3)=15\text{; minimum coverings classified}$ | 15 Oct 2026 | [v1.0.0] | [Account](coverings/12-6-3/README.md) · [Proof](coverings/12-6-3/proof.md) |
| $C(n,4,3)=n(n-1)^2/24$, for $n=12u+1$, $1\le u\le8$ | 22 Oct 2026 | [v1.4.0] | [Account and block lists](coverings/12u-plus-1-4-3/README.md) · [Proof](coverings/12u-plus-1-4-3/proof.md) |
| $C(7a+4,3a+2,2)=7,\ a\ge1\text{; 2 minimum forms}$ | 25 Oct 2026 | [v1.6.0] | [Account](coverings/seven-block/README.md) · [Proof](coverings/seven-block/proof.md) |
| $C(qk,k,2)=q(q+1),\quad k\ge q,\ q\mid k$ | — | v2.0.0 (prepared) | [Account](coverings/qk-k-2/README.md) · [Proof](coverings/qk-k-2/proof.md#3-actual-constructions-and-exact-intervals) |

The eight included block lists correspond to n=13,25,37,49,61,73,85,97.
Six were reconstructed from published methods and two recovered from historical
sources; each list is checked against its Lean construction.
In the final family, q is a prime power with q≥2.

## Equality and structural results

| Result | Published here | Release | Account and proof |
|---|---|---|---|
| $C(qk,k,2)=q(q+1)\Longrightarrow q\mid k\text{ or }(q+1)\mid k,\quad q\ge4,\ k\ge q$ | — | v2.0.0 (prepared) | [Account](coverings/4k-k-2/README.md) · [Proof](coverings/4k-k-2/proof.md) |
| $20\text{-block }(16t,4t,2)\text{ coverings: complete description and converse},\quad t\ge1$ | — | v2.0.0 (prepared) | [Account](coverings/qk-k-2/README.md) · [Proof](coverings/qk-k-2/proof.md#5-all-20-block-16t4t2-coverings) |

The [general account](coverings/qk-k-2/proof.md) also includes the determinant
criterion, positive-load classification and the primitive quotient with its
replication converse. Their precise hypotheses and original sources are included.

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

Use the [citation metadata](CITATION.cff) to cite this package. The
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

[v1.7.0]: https://github.com/renidrag/covering/releases/tag/v1.7.0

