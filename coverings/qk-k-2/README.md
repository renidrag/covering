# Exact values and construction intervals for C(qk,k,2)

**Rob Gardiner, with Codex assistance.**

We prove these exact values, including constructions with the stated number of blocks:

| Covering number | Exact value | Construction |
|---|---:|---|
| C(55,11,2) | 31 | Weighted projective plane |
| C(65,13,2) | 31 | Flavio Perona's 2011 construction |
| C(80,16,2) | 31 | Weighted projective plane |
| C(85,17,2) | 31 | Weighted projective plane |
| C(95,19,2) | 31 | Jan de Heer and Steve Muir's 2011 construction |
| C(56,8,2) | 57 | Weighted projective plane |
| C(90,10,2) | 91 | Weighted projective plane |

We also prove **C(70,14,2)≥31**. Its exact value is not established here.
The [combined table](bounds.md) gives **151 lower bounds**, including
C(37,10,3)≥78, C(56,12,3)≥145, C(66,14,3)≥147,
C(59,17,5)≥1007 and C(98,22,5)≥3070. It combines the earlier
order-four lifts, 78 direct additions and 14 order-six consequences,
retaining every intermediate ceiling.

For prime-power q≥2 we prove these general results:

| Hypotheses | Conclusion |
|---|---|
| k≥q and q∣k | C(qk,k,2)=q(q+1) |
| k=qu+r, 1≤r≤u, qk≤v≤qk+r | C(v,k,2)≤q²+q+1 |
| Same weighted parameters, qk<v≤qk+r | C(v,k,2)=q²+q+1 |
| Same weighted parameters, q≥4, v=qk, q∤k, and either (q+1)∤k or no twisted plane of order q | C(qk,k,2)=q²+q+1 |

Here r need not be less than q. The endpoint v=qk has the separate
conditions in the last row.

Each exact value includes a construction with that many distinct blocks
on any point set of the stated size. Read the [proof](proof.md) for the
argument and Lean correspondence. The separate [order-six account](../6k-k-2/README.md)
proves C(6k,k,2)≥43 for every k≥6.

## Proof in outline

For q≥4 and k≥q, a pair covering with q(q+1) blocks on qk points requires
q∣k or (q+1)∣k.
For the listed order-five cases, neither 5 nor 6 divides k, so 30 blocks
are impossible. For the listed order-7 and order-9 cases, the twisted-plane
determinant excludes the remaining equality branch. The constructions give
the matching upper bounds.
For v>qk, elementary incidence counting supplies the lower bound.

We also classify every 20-block (16t,4t,2) covering for t≥1, allowing
repeated block occurrences. It comes from a truncated-plane core with
uniform multiplicities or an extension through one common coordinate.
[Theorem 5](proof.md#5-all-20-block-16t4t2-coverings)
gives the exact weights and converse. At t=1 only the pure core occurs.
The [general description and primitive quotient](proof.md#primitive-quotient-and-replication)
explain both equality branches: excluded twisting leaves the two core-load
forms, while a twisted equality cover is a uniform replication of a smaller
pair covering. The converse requires a supplied primitive construction.

## Supporting results and construction

The proofs use the included geometric classification, positive-load
classification, determinant calculation and finite-plane constructions.
Perona's and de Heer–Muir's block lists are transcribed and verified
separately. Their provenance, licences and the earlier mathematical results
are documented in [sources.md](sources.md).

The seven exact pair values close intervals in the LJCR snapshot of
26 October 2026, and C(70,14,2) improves its listed 30–32 to 31–32.
[Sources](sources.md#comparison-dates-and-the-combined-table) records the dates
and attribution.

## Build and verify

Import `CoveringDesigns.Qk_K_2` for the numerical results and equality
description, and `CoveringDesigns.PairConsequences.Intervals` for the full
parameter ranges in the construction table. The [proof appendix](proof.md#appendix-a-lean-correspondence-and-trust-boundary)
identifies smaller imports for lower bounds, lifting, constructions and
equality. Use `./covering verify qk-k-2` and
`./covering verify pair-consequences` and `./covering verify 6k-k-2`,
followed by the corresponding
`./covering audit` commands to validate their records. The
[shared verification guide](../../technical-details.md) explains setup,
source/data checks and witness correspondence.
