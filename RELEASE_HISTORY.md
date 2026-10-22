# Mathematical release history

**Rob Gardiner**

This records the project's main mathematical additions. Dates use
Europe/London time. Historical links identify each public snapshot's
mathematical account and successful Lean verification run.
Every stated exact value includes an attaining ordinary covering.

Releases are cumulative. The [collection DOI](https://doi.org/10.5281/zenodo.23511135)
represents all versions; use a version DOI below to cite a particular archive.

| Release | First public date | Archived snapshot | Version DOI |
|---|---|---|---|
| [v1.3.0](https://github.com/renidrag/covering/releases/tag/v1.3.0) | 21 October 2026 | [78e2076b0cb0](https://github.com/renidrag/covering/tree/78e2076b0cb05b99aa83fc952832c6591ac47f80) | [10.5281/zenodo.23546184](https://doi.org/10.5281/zenodo.23546184) |
| [v1.2.0](https://github.com/renidrag/covering/releases/tag/v1.2.0) | 20 October 2026 | [d9886e4709b3](https://github.com/renidrag/covering/tree/d9886e4709b3987974e6920d98cb4df5345ef922) | [10.5281/zenodo.23512290](https://doi.org/10.5281/zenodo.23512290) |
| [v1.1.0](https://github.com/renidrag/covering/releases/tag/v1.1.0) | 19 October 2026 | [9bc5a0f8d7e2](https://github.com/renidrag/covering/tree/9bc5a0f8d7e2d2b104bbed38eccad35b778fe46d) | [10.5281/zenodo.23511297](https://doi.org/10.5281/zenodo.23511297) |
| [v1.0.0](https://github.com/renidrag/covering/releases/tag/v1.0.0) | 15 October 2026 | [aee92cd704b6](https://github.com/renidrag/covering/tree/aee92cd704b6ac7dd2143459659c9e101d61d859) | [10.5281/zenodo.23511136](https://doi.org/10.5281/zenodo.23511136) |

Versions v1.0.0–v1.2.0 were archived on Zenodo on 20 October 2026; v1.3.0
was archived on 21 October 2026. The v1.1.0 archive uses a same-day packaging
cleanup with unchanged mathematics; the 19 October account below retains
the first public snapshot.

## 22 October 2026 — $41\le C(14,5,3)\le43$ and exact values for $C(12u+1,4,3)$, $1\le u\le8$

**v1.4.0**

The two contributions have separate mathematical accounts.

**Stronger lower bound:** $41\le C(14,5,3)\le43$, improving the 37–43
interval displayed in the repository entry inspected on 21 October 2026.
The structural lower proof combines exact point links, completion counts,
a removable-block lemma and compatibility between links. The historical
43-block construction is credited to Nurmela and Östergård and checked in
Lean. The exact value remains undetermined.

[Result and proof outline](coverings/14-5-3/README.md) ·
[Proof and Lean correspondence](coverings/14-5-3/proof.md) ·
[Sources](coverings/14-5-3/sources.md).

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
the six larger optimal block lists, retains historical witnesses for 13 and
25, and proves all eight exact values and their correspondence to the
included lists in Lean. The six larger lists are smaller than those in the
inspected La Jolla snapshot; the mathematical exactness predates this package.

[Result and block lists](coverings/12u-plus-1-4-3/README.md) ·
[Proof and Lean correspondence](coverings/12u-plus-1-4-3/proof.md) ·
[Sources and attribution](coverings/12u-plus-1-4-3/sources.md).

All earlier mathematical results are retained unchanged.

## 21 October 2026 — $C(18,10,3)=12$ and five lifted lower bounds

**v1.3.0**

| Result |
|---|
| $C(18,10,3)=12$ |
| $C(19,11,4)\ge21$ |
| $C(20,12,5)\ge35$ |
| $C(21,13,6)\ge57$ |
| $C(22,14,7)\ge90$ |
| $C(23,15,8)\ge138$ |

The structural proof excludes an 11-block covering of the triples of 18
points by 10-element blocks. A historical 12-block construction gives
attainment. The five further lower bounds follow by Schönheim lifting,
retaining every intermediate ceiling. All six conclusions are proved in
Lean for arbitrary finite point types.

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

The proof establishes $C(13,7,4)=30$, supported by reconstructed proofs and
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
