# Mathematical release history

**Rob Gardiner**

This records the first public GitHub snapshots of the project's main
mathematical results. Dates use Europe/London time. The links identify each
snapshot's mathematical account and successful Lean verification run.
Every stated exact value includes an attaining ordinary covering.

## 15 October 2026 — $C(13,7,4)=30$

The proof establishes $C(13,7,4)=30$, supported by reconstructed proofs and
Lean formalisations of Stanton's $C(11,5,2)=7$ classification and GPPT's
$C(12,6,3)=15$ result and structural classification.

[Snapshot aee92cd704b6](https://github.com/renidrag/covering/tree/aee92cd704b6ac7dd2143459659c9e101d61d859) ·
[Mathematical account](https://github.com/renidrag/covering/blob/aee92cd704b6ac7dd2143459659c9e101d61d859/coverings/13-7-4/README.md) ·
[Lean verification passed](https://github.com/renidrag/covering/actions/runs/38687834009).

The original repository README dates the result to 13 October; its first
public GitHub snapshot is dated 15 October.

## 19 October 2026 — $C(20,11,3)=12$ and family bounds $13$ and $14$

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

## 20 October 2026 — improved thresholds for $C(2k-2,k,3)$

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

The mathematical accounts credit the established constructions and supporting
theorems. Rob Gardiner's reconstructed proofs, structural arguments and Lean
formalisations were developed with AI assistance.
