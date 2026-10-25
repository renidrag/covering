# Lower bounds for C(q²+q+2,q+2,3), odd q≥3

**Rob Gardiner**

We prove **C(32,7,3)≥149**, **C(58,9,3)≥375** and
**C(92,11,3)≥774** in Lean. These follow from a general bound for every
odd integer q≥3. Put n=q²+q+1, h=⌈q/4⌉, N=nq³(q+1)/6 and
M=binom(q+2,3)−h. Then

\[
C(n+1,q+2,3)\ge n+\left\lceil\frac NM\right\rceil.
\]

The [proof](proof.md) applies to any finite point set of the stated size
and allows repeated blocks, counted separately. No finite-field or
projective-plane existence assumption is required.

| q | Covering number | Lower bound | Bound without deletion |
|---:|---|---:|---:|
| 3 | C(14,5,3) | 39 | outside the proved range |
| 5 | C(32,7,3) | 149 | 147 |
| 7 | C(58,9,3) | 375 | 374 |
| 9 | C(92,11,3) | 774 | 770 |

The independent bound without deletion is
C(q²+q+2,q+2,3)≥⌈(q²+q+2)²/(q+2)⌉ for odd q≥5.
For q=3, the existing [C(14,5,3)≥41 result](../14-5-3/README.md) is stronger.

## Proof in outline

The link of a point consists of the blocks containing it, with that point
removed. A link with n blocks is a projective plane. With n+1 blocks,
the Füredi–Sane theorem shows that deleting one block leaves a plane.

Parity forces every (q+2)-set in this plane to contain at least ⌈q/4⌉
collinear triples. The n plane blocks leave N noncollinear triples to
cover, while each remaining block covers at most M of them. This gives
the displayed bound. If every point has degree at least n+2, counting
point-block incidences gives a bound at least as strong.

## Supporting results and contribution

Füredi proved the deletion theorem in 1989; Sane gave its elementary
proof in 1991. Geometric results in the 2010 covering-array argument of
Colbourn, Kéri, Rivas Soriano and Schlage-Puchta already imply 149 and 375.
The parity estimate used here strengthens that deduction from 770 to 774
at q=9. This account gives a complete proof and a reusable Lean
formalisation of parity, deletion and completion counting.
The [source account](sources.md) separates the published ingredients,
the supplied arguments and the historical assessment.

## Build and verify

Import `CoveringDesigns.ProjectiveLinkBounds`. The theorems
`indexed_completion_lower_bound` and `completion_lower_bound` assume
only odd q≥3, the point count, uniform block size and triple coverage.
The [proof appendix](proof.md#appendix-lean-correspondence) maps the
mathematical statements to Lean declarations.

Run `./covering verify projective-link-bounds` for fresh compilation and
contract/axiom checks, then `./covering audit projective-link-bounds` to
validate that record. `./covering verify` checks the whole package.
The [shared guide](../../technical-details.md) describes dependency setup
and the distinction between source checks, compilation and record validation.
