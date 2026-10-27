# Exact values of C(4k,k,2)

**Rob Gardiner, with Codex assistance.**

For every integer k≥8,

\[
C(4k,k,2)=
\begin{cases}
20,&4\mid k,\\
21,&4\nmid k.
\end{cases}
\]

Lean proves the lower bounds and constructs a covering with exactly the
stated number of blocks on any set of 4k points. C(v,k,2) is the minimum number of distinct k-subsets
needed to cover every pair of a v-point set.

| Result | Hypotheses | Conclusion |
|---|---|---|
| Exact value | k≥8 | 20 if 4∣k; 21 otherwise |
| Lower bound, allowing repeated blocks | k≥4 | At least 20; at least 21 if 4∤k |
| General equality condition | q≥4, k≥q; q(q+1) k-element blocks covering pairs on qk points | q∣k or (q+1)∣k |

The lower bounds allow repeated block occurrences; the constructions use
distinct blocks.

Read the [proof](proof.md), including the appendix linking the argument to Lean.

## Proof in outline

Suppose q(q+1) k-element blocks cover all pairs on qk points. Incidence
counting forces every point to lie in exactly q+1 blocks. A point's
**support** is the set of block indices containing it. Füredi's
[geometric classification](../pair-equality/README.md) gives a truncated-plane
core or a twisted plane among these supports. The
[load theorem](../truncated-plane-loads/README.md) forces q∣k in the first
case; two mate equations force (q+1)∣k in the second. At q=4 the twisted
case would make a squared integer determinant equal 3¹⁰·5¹¹, impossible
because the exponent of 5 is odd.

## Supporting results and construction

Affine-plane expansion gives 20 blocks when 4∣k. Weighted projective-plane
expansion gives 21 blocks in the other cases except k=11. That case uses
Colin Barker's historical 21-block (44,11,2) construction, verified in Lean.
The [sources](sources.md) give the earlier results, the project's load
argument, and construction credits and licences.

The LJCR snapshot of 26 October 2026 records 20–21 at
k=9,10,11,13,14,15,17,18,19,21,22,23, with v=4k. The theorem settles all
twelve entries at 21. Divisible cases were already recorded as 20.
Further orders, construction intervals and lifted bounds are in
[C(qk,k,2)](../qk-k-2/README.md).

## Build and verify

`CoveringDesigns.C4k_K_2.exactness` gives the theorem on any finite point set
of the required size. Import `CoveringDesigns.C4k_K_2.LowerBound` when only lower
bounds are needed. Use `./covering verify 4k-k-2`, followed by
`./covering audit 4k-k-2` to validate the record. The
[shared verification guide](../../technical-details.md) explains setup,
source/data checks and the distinction between compilation and record validation.
