# Geometric equality for pair coverings

**Rob Gardiner, with Codex assistance.**

In a covering, a point's **support** is the set of block indices containing
it. Its multiplicity counts points with that same support.

Let H be an intersecting family of distinct (q+1)-subsets of a set I,
where |I|=q(q+1) and q≥4. Give its members positive real weights so that
the weights through each coordinate sum to 1. We prove Füredi's dichotomy:

| Branch | Conclusion about H |
|---|---|
| Truncated plane | H contains the q² supports of a truncated plane on I. |
| Twisted plane | H has q(q+1) supports and every coordinate lies in q+1 of them. Each support has one distinct mate meeting it twice; all other distinct intersections have size 1. |

In the twisted case each coordinate also has one distinct mate with which
it occurs in two supports; every other distinct pair occurs once. Both
mate maps are involutions, and no further (q+1)-set can be added while
keeping the family intersecting.

In the core case, the original weights and all extra supports remain.
The core need not be the whole family. Read the [proof](proof.md) for the
precise incidence conditions and Lean correspondence.

## Proof in outline

Choose a subfamily whose incidence vectors are independent and which still
admits positive weights giving load 1 at each coordinate. These auxiliary
weights may differ from the originals. Counting shows that every coordinate
lies in at least q supports.

A coordinate of degree q defines a group of q coordinates. Füredi's
dimension argument forces these groups to partition I and yields the core.
Otherwise every degree is q+1, giving the twisted incidence structure.
A short counting argument shows that this subfamily is already all of H.

## Supporting results and applications

The classification and dimension argument are due to Füredi. The twisted
maximality proof uses Bierbrauer–Marcugini–Pambianco's shorter count; see the
[source section](proof.md#sources-and-proof-provenance).

The [load theorem](../truncated-plane-loads/README.md) describes the weights
and extras allowed in the core branch. Together these results give
[general divisibility and C(4k,k,2) exactness](../4k-k-2/README.md), with
[further consequences](../qk-k-2/README.md) at other orders.

## Build and verify

The main theorem is `CoveringDesigns.PairEquality.geometric_dichotomy`.
Import `CoveringDesigns.PairEquality.Classification` for the geometry;
the [appendix](proof.md#appendix-a-lean-contracts-and-dependencies) gives
the other interfaces. Use `./covering verify pair-equality`, followed by
`./covering audit pair-equality`. See the
[shared verification guide](../../technical-details.md).
