# Mathematical release history

**Rob Gardiner**

This records the project's main mathematical additions. Dates use
Europe/London time. Historical links identify each public snapshot's
mathematical account and successful Lean verification run.
Each exact value includes a construction with that number of distinct blocks.

Releases are cumulative. The [collection DOI](https://doi.org/10.5281/zenodo.23511135)
represents all versions; use a version DOI below to cite a particular archive.

| Release | First public date | Archived snapshot | Version DOI |
|---|---|---|---|
| [v1.6.0](https://github.com/renidrag/covering/releases/tag/v1.6.0) | 25 October 2026 | [6b31c1407457](https://github.com/renidrag/covering/tree/6b31c1407457709b335baf346a29962701d8b6e6) | [10.5281/zenodo.23638382](https://doi.org/10.5281/zenodo.23638382) |
| [v1.5.0](https://github.com/renidrag/covering/releases/tag/v1.5.0) | 24 October 2026 | [d8e27cb77c77](https://github.com/renidrag/covering/tree/d8e27cb77c77e91b7657fdc9d7ca14552e1ee2c1) | [10.5281/zenodo.23616283](https://doi.org/10.5281/zenodo.23616283) |
| [v1.4.0](https://github.com/renidrag/covering/releases/tag/v1.4.0) | 22 October 2026 | [a2a726abb7ae](https://github.com/renidrag/covering/tree/a2a726abb7ae1e26a37841f730abb90a34469c11) | [10.5281/zenodo.23576357](https://doi.org/10.5281/zenodo.23576357) |
| [v1.3.0](https://github.com/renidrag/covering/releases/tag/v1.3.0) | 21 October 2026 | [78e2076b0cb0](https://github.com/renidrag/covering/tree/78e2076b0cb05b99aa83fc952832c6591ac47f80) | [10.5281/zenodo.23546184](https://doi.org/10.5281/zenodo.23546184) |
| [v1.2.0](https://github.com/renidrag/covering/releases/tag/v1.2.0) | 20 October 2026 | [d9886e4709b3](https://github.com/renidrag/covering/tree/d9886e4709b3987974e6920d98cb4df5345ef922) | [10.5281/zenodo.23512290](https://doi.org/10.5281/zenodo.23512290) |
| [v1.1.0](https://github.com/renidrag/covering/releases/tag/v1.1.0) | 19 October 2026 | [9bc5a0f8d7e2](https://github.com/renidrag/covering/tree/9bc5a0f8d7e2d2b104bbed38eccad35b778fe46d) | [10.5281/zenodo.23511297](https://doi.org/10.5281/zenodo.23511297) |
| [v1.0.0](https://github.com/renidrag/covering/releases/tag/v1.0.0) | 15 October 2026 | [aee92cd704b6](https://github.com/renidrag/covering/tree/aee92cd704b6ac7dd2143459659c9e101d61d859) | [10.5281/zenodo.23511136](https://doi.org/10.5281/zenodo.23511136) |

Versions v1.0.0–v1.2.0 were archived on Zenodo on 20 October 2026; v1.3.0
was archived on 21 October 2026, v1.4.0 on 22 October 2026 and v1.5.0
on 24 October 2026. v1.6.0 was published and archived on 25 October 2026.
The v1.1.0 archive uses a same-day packaging
cleanup with unchanged mathematics; the 19 October account below retains
the first public snapshot.

## 25 October 2026 — $C(19,9,3)=17$

**v1.6.0**

[Snapshot 6b31c1407457](https://github.com/renidrag/covering/tree/6b31c1407457709b335baf346a29962701d8b6e6) ·
[Lean verification passed](https://github.com/renidrag/covering/actions/runs/40177073143) ·
[Zenodo archive — DOI 10.5281/zenodo.23638382](https://doi.org/10.5281/zenodo.23638382).

This release proves C(19,9,3)=17. The new argument rules out 16 blocks;
Rade Belic's known construction uses 17. Both are verified in Lean.

The proof shows that the links of minimum-degree points must fit together
in a particular way: 8 points have the plane structure of AG(3,2).
Counting the supports of the other 11 points then forces an uncovered
triple. The argument allows repeated block occurrences and works on any
set of 19 points.

The package includes a proof of the supporting pair-covering classification
and credits its earlier sources. LJCR recorded Belic's construction on
11 June 1997. Its 17 distinct blocks cover all 969 triples; the distributed
block list is checked against the Lean construction.

[Result and proof outline](https://github.com/renidrag/covering/blob/6b31c1407457709b335baf346a29962701d8b6e6/coverings/19-9-3/README.md) ·
[Mathematical proof and Lean correspondence](https://github.com/renidrag/covering/blob/6b31c1407457709b335baf346a29962701d8b6e6/coverings/19-9-3/proof.md) ·
[Sources and construction attribution](https://github.com/renidrag/covering/blob/6b31c1407457709b335baf346a29962701d8b6e6/coverings/19-9-3/sources.md) ·
[Supporting classification](https://github.com/renidrag/covering/blob/6b31c1407457709b335baf346a29962701d8b6e6/coverings/seven-block/proof.md) ·
[Belic's block list](https://github.com/renidrag/covering/blob/6b31c1407457709b335baf346a29962701d8b6e6/data/c1993-belic-17.blocks.txt).

All earlier mathematical results and constructions are retained.

## 24 October 2026 — $C(34,18,3)=13$ and 10 improved lower bounds

**v1.5.0**

[Snapshot d8e27cb77c77](https://github.com/renidrag/covering/tree/d8e27cb77c77e91b7657fdc9d7ca14552e1ee2c1) ·
[Lean verification passed](https://github.com/renidrag/covering/actions/runs/40086303290) ·
[Zenodo archive — DOI 10.5281/zenodo.23616283](https://doi.org/10.5281/zenodo.23616283).

This release proves $C(34,18,3)=13$ in Lean, including the known 13-block
construction. It also proves 10 lower bounds by applying Schönheim's bound
repeatedly.

| Result | Mathematical account |
|---|---|
| C(34,18,3)=13 | [Proof and 13-block construction](https://github.com/renidrag/covering/blob/d8e27cb77c77e91b7657fdc9d7ca14552e1ee2c1/coverings/34-18-3/proof.md) |
| C(15,6,4)≥103 | [Proof](https://github.com/renidrag/covering/blob/d8e27cb77c77e91b7657fdc9d7ca14552e1ee2c1/coverings/15-6-4/proof.md) |
| C(16,7,5)≥236 | [Proof](https://github.com/renidrag/covering/blob/d8e27cb77c77e91b7657fdc9d7ca14552e1ee2c1/coverings/16-7-5/proof.md) |
| C(17,8,6)≥502 | [Proof](https://github.com/renidrag/covering/blob/d8e27cb77c77e91b7657fdc9d7ca14552e1ee2c1/coverings/17-8-6/proof.md) |
| C(18,9,7)≥1004 | [Proof](https://github.com/renidrag/covering/blob/d8e27cb77c77e91b7657fdc9d7ca14552e1ee2c1/coverings/18-9-7/proof.md) |
| C(19,10,8)≥1908 | [Proofs of the first 5 bounds](https://github.com/renidrag/covering/blob/d8e27cb77c77e91b7657fdc9d7ca14552e1ee2c1/coverings/19-10-8/proof.md) |
| C(35,19,4)≥24 | [Proof](https://github.com/renidrag/covering/blob/d8e27cb77c77e91b7657fdc9d7ca14552e1ee2c1/coverings/35-19-4/proof.md) |
| C(36,20,5)≥44 | [Proof](https://github.com/renidrag/covering/blob/d8e27cb77c77e91b7657fdc9d7ca14552e1ee2c1/coverings/36-20-5/proof.md) |
| C(37,21,6)≥78 | [Proof](https://github.com/renidrag/covering/blob/d8e27cb77c77e91b7657fdc9d7ca14552e1ee2c1/coverings/37-21-6/proof.md) |
| C(38,22,7)≥135 | [Proof](https://github.com/renidrag/covering/blob/d8e27cb77c77e91b7657fdc9d7ca14552e1ee2c1/coverings/38-22-7/proof.md) |
| C(39,23,8)≥229 | [Proofs of the other 5 bounds](https://github.com/renidrag/covering/blob/d8e27cb77c77e91b7657fdc9d7ca14552e1ee2c1/coverings/39-23-8/proof.md) |

The proof of $C(34,18,3)=13$ combines the project's lower bound with a
known 13-block construction. LJCR recorded it on 20 January 2009 as a
multiple of a (17,9,3) covering. Lean verifies the construction on any set
of 34 points. Its LJCR credit is preserved.

The first 5 inequalities follow from C(14,5,3)≥41, first published here on
22 October 2026. The other 5 follow from C(34,18,3)≥13, already covered
by the C(2k−2,k,3) theorem first published on 19 October. Each step applies
Schönheim's point-link argument and rounds up to an integer. These are
lower bounds; the linked accounts give the proofs, credits and dated
comparisons.

All previously published result-specific proofs and accounts are retained.

## 22 October 2026 — $41\le C(14,5,3)\le43$ and exact values for $C(12u+1,4,3)$, $1\le u\le8$

**v1.4.0**

[Snapshot a2a726abb7ae](https://github.com/renidrag/covering/tree/a2a726abb7ae1e26a37841f730abb90a34469c11) ·
[Lean verification passed](https://github.com/renidrag/covering/actions/runs/39836729509) ·
[Zenodo archive — DOI 10.5281/zenodo.23576357](https://doi.org/10.5281/zenodo.23576357).

The two contributions have separate mathematical accounts.

**Stronger lower bound:** $41\le C(14,5,3)\le43$, improving the 37–43
interval displayed in the repository entry inspected on 21 October 2026.
The lower-bound proof combines exact point links, completion counts,
a removable-block lemma and compatibility between links. The historical
43-block construction is credited to Nurmela and Östergård and checked in
Lean. The exact value is not yet known.

[Result and proof outline](https://github.com/renidrag/covering/blob/a2a726abb7ae1e26a37841f730abb90a34469c11/coverings/14-5-3/README.md) ·
[Proof and Lean correspondence](https://github.com/renidrag/covering/blob/a2a726abb7ae1e26a37841f730abb90a34469c11/coverings/14-5-3/proof.md) ·
[Sources](https://github.com/renidrag/covering/blob/a2a726abb7ae1e26a37841f730abb90a34469c11/coverings/14-5-3/sources.md).

**Known exact values, reconstructed lists and Lean verification:**
$C(12u+1,4,3)=(12u+1)(12u)^2/24$ for $1\le u\le8$.

| $v$ | $C(v,4,3)$ |
|---:|---:|
| 13 | 78 |
| 25 | 600 |
| 37 | 1,998 |
| 49 | 4,704 |
| 61 | 9,150 |
| 73 | 15,768 |
| 85 | 24,990 |
| 97 | 37,248 |

These exact values were proved in earlier work. This project reconstructs
the 6 larger optimal block lists and uses known lists for 13 and 25 points.
Lean verifies all 8 values and checks that the constructions match the
included lists. The 6 reconstructed lists use fewer blocks than those in
the inspected La Jolla snapshot; the exact values were already known.

[Result and block lists](https://github.com/renidrag/covering/blob/a2a726abb7ae1e26a37841f730abb90a34469c11/coverings/12u-plus-1-4-3/README.md) ·
[Proof and Lean correspondence](https://github.com/renidrag/covering/blob/a2a726abb7ae1e26a37841f730abb90a34469c11/coverings/12u-plus-1-4-3/proof.md) ·
[Sources and attribution](https://github.com/renidrag/covering/blob/a2a726abb7ae1e26a37841f730abb90a34469c11/coverings/12u-plus-1-4-3/sources.md).

All earlier mathematical results are retained unchanged.

## 21 October 2026 — $C(18,10,3)=12$ and 5 further lower bounds

**v1.3.0**

| Result |
|---|
| $C(18,10,3)=12$ |
| $C(19,11,4)\ge21$ |
| $C(20,12,5)\ge35$ |
| $C(21,13,6)\ge57$ |
| $C(22,14,7)\ge90$ |
| $C(23,15,8)\ge138$ |

The proof rules out 11 blocks for C(18,10,3). A known construction uses
12, proving C(18,10,3)=12. The 5 further lower bounds follow by applying
Schönheim's bound repeatedly, with rounding at each step. All 6 results
are proved in Lean for any point sets of the stated sizes.

[Snapshot 78e2076b0cb0](https://github.com/renidrag/covering/tree/78e2076b0cb05b99aa83fc952832c6591ac47f80) ·
[Mathematical account](https://github.com/renidrag/covering/blob/78e2076b0cb05b99aa83fc952832c6591ac47f80/coverings/18-10-3/README.md) ·
[Proof and Lean correspondence](https://github.com/renidrag/covering/blob/78e2076b0cb05b99aa83fc952832c6591ac47f80/coverings/18-10-3/proof.md) ·
[Sources and attribution](https://github.com/renidrag/covering/blob/78e2076b0cb05b99aa83fc952832c6591ac47f80/coverings/18-10-3/sources.md) ·
[Lean verification passed](https://github.com/renidrag/covering/actions/runs/39670689136).

These additions are not included in the v1.0.0–v1.2.0 archives.

## 20 October 2026 — improved thresholds for $C(2k-2,k,3)$

**v1.2.0**

| Result | Previous range | Improved range |
|---|---|---|
| $C(2k-2,k,3)\ge13$ | $k\ge18$ | $k\ge17$ |
| $C(2k-2,k,3)=14$ | $k\ge36$ | $k\ge31$ |

In particular, $C(60,31,3)=C(62,32,3)=14$. The strengthened proof uses
rank slack, affine support capacity, boundary rigidity and saturated-matching
compatibility. The other conclusions from 19 October remain unchanged.
The separate indexed threefold pair-covering theorem has threshold $k\ge33$.

[Snapshot d9886e4709b3](https://github.com/renidrag/covering/tree/d9886e4709b3987974e6920d98cb4df5345ef922) ·
[Mathematical account](https://github.com/renidrag/covering/blob/d9886e4709b3987974e6920d98cb4df5345ef922/coverings/2k-minus-c-k-3/README.md) ·
[Lean verification passed](https://github.com/renidrag/covering/actions/runs/39462685475).

## 19 October 2026 — $C(20,11,3)=12$ and family bounds $13$ and $14$

**v1.1.0**

| Result | Parameter range |
|---|---|
| $C(20,11,3)=12$ | $(v,k,t)=(20,11,3)$ |
| $13\le C(2k-2,k,3)\le14$ | $k\ge18$ |
| $C(2k-2,k,3)=14$ | $k\ge36$ |
| $C(2k-3,k,3)=14$ | $k\ge59$ |
| $C(2k-c,k,3)=14$ | $c\ge2$ and $k\ge25c$ |

[Snapshot c99e30c5421c](https://github.com/renidrag/covering/tree/c99e30c5421c90de960df79e98050fa517ea492a) ·
[Mathematical account](https://github.com/renidrag/covering/blob/c99e30c5421c90de960df79e98050fa517ea492a/coverings/2k-minus-c-k-3/README.md) ·
[Lean verification passed](https://github.com/renidrag/covering/actions/runs/39330451817).

## 15 October 2026 — $C(13,7,4)=30$

**v1.0.0**

This release proves $C(13,7,4)=30$, using reconstructed proofs and
Lean formalisations of Stanton's $C(11,5,2)=7$ classification and GPPT's
$C(12,6,3)=15$ result and structural classification.

[Snapshot aee92cd704b6](https://github.com/renidrag/covering/tree/aee92cd704b6ac7dd2143459659c9e101d61d859) ·
[Mathematical account](https://github.com/renidrag/covering/blob/aee92cd704b6ac7dd2143459659c9e101d61d859/coverings/13-7-4/README.md) ·
[Lean verification passed](https://github.com/renidrag/covering/actions/runs/38687834009).

The original repository README dates the result to 13 October; its first
public GitHub snapshot is dated 15 October.

The mathematical accounts credit the established constructions and supporting
theorems. Rob Gardiner's reconstructed proofs, structural arguments and Lean
formalisations were developed with AI assistance.
