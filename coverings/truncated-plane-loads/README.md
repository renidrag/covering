# Equal-load extensions of truncated projective planes, q≥4

**Rob Gardiner, with Codex assistance.**

We classify intersecting families of (q+1)-subsets containing a truncated
projective plane of order q≥4, when positive weights give the same load K>0
at every coordinate. The **load** is the sum of weights of the subsets
containing that coordinate. No field or prime-power assumption is required.

Write T for the q² core supports, G₀,…,G_q for its groups of q coordinates,
and t=K/q. There are exactly two possible forms:

| Form | Supports and weights |
|---|---|
| Pure core | Exactly T, each with weight t. |
| Common-coordinate extension | Choose c∈G_h and 0<s<t. Add G_i∪{c} for every i≠h, each with weight s. Core supports through c have weight t−s; the others have weight t. |

Both forms satisfy the hypotheses. For positive integer weights, t and s
are integers: **q∣K**, and the extended form requires 1≤s<t. At t=1 only
the pure core is possible. The classification is relative to the supplied
core and does not assert its uniqueness.

Lean proves the classification and converse. Read the [proof](proof.md)
for the incidence definitions and Lean correspondence.

## Proof in outline

Any (q+1)-set meeting every core support is either a core support or a
whole group plus one outside coordinate. If extra supports occur, equal
loads force at least q groups to carry them. Since q≥4, intersection forces
a common coordinate. Counting loads by group, then along each core support,
determines all the weights in the table.

## Supporting results and construction

In a covering, a point's **support** is the set of block indices containing
it. Integer weights count points with the same support. Conversely, replacing
each support by that many distinct points produces a covering with qK points
and q(q+1) distinct blocks of size K. Equal supports do not identify points.
At q=4, t=2, s=1 this gives 20 blocks of size 8 on 32 points.

Füredi's [geometric classification](../pair-equality/README.md) supplies a
core in one branch of the equality problem. The present load theorem then
gives the divisibility used in [C(4k,k,2)](../4k-k-2/README.md) and its
[further consequences](../qk-k-2/README.md).
[Sources](sources.md) gives attribution and historical qualifications.

## Build and verify

The principal interface is `CoveringDesigns.TruncatedPlaneLoads.real_classification_iff`.
The [proof appendix](proof.md#appendix-a-lean-correspondence-and-dependencies)
lists the integer, construction and existing-cover interfaces with their imports.
Use `./covering verify truncated-plane-loads`, followed by
`./covering audit truncated-plane-loads`. See the
[shared verification guide](../../technical-details.md) for setup and checks.
