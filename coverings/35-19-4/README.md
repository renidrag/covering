# A Schönheim corollary: $C(35,19,4)\ge24$

**Deduction and Lean formalisation: Rob Gardiner, with AI assistance.**

Every family of 19-element subsets covering all 4-element subsets of a
35-point set has at least **24 distinct blocks**. This is the
first of five direct corollaries of this project's
[lower theorem $C(34,18,3)\ge13$](../34-18-3/README.md).
The immediate dependency is:

| Result | Proved universal premise |
| --- | --- |
| [$C(35,19,4)\ge24$](proof.md) | [$C(34,18,3)\ge13$](../34-18-3/proof.md) |

The contribution is the explicit deduction and its Lean formalisation,
using Schönheim's classical point-link argument. The [proof](proof.md)
gives the complete short argument. Attainment at 24 is not asserted.

The [five-result overview](../39-23-8/README.md) shows the whole chain.

The Covering Repository query of **23 October 2026** displayed lower bound
**23**; this deduction improves that entry by **1**. The lower bound
$C(34,18,3)\ge13$ follows from the project's general theorem published
on 19 October 2026. The [source account](sources.md) records the dated
comparison, attribution and publication history.

## Proof in outline

Deleting a point from every block through it gives a
$(34,18,3)$ covering. The universal premise forces at least
13 blocks through each point. Counting incidences and rounding up gives

$$
19|\mathcal C|\ge35\cdot13=455,
\qquad |\mathcal C|\ge\left\lceil455/19\right\rceil=24.
$$

## Supporting results and attribution

Schönheim's proof of Theorem I (1964, p. 1407) supplies the lifting step.
This project's [offset-two theorem, Corollary 10](../2k-minus-c-k-3/proof.md#73-the-numerical-conclusions)
gives $C(2k-2,k,3)\ge13$ for $k\ge18$. Setting $k=18$ supplies
the stronger seed $C(34,18,3)\ge13$; every subsequent ceiling is retained.
The historical LJCR family attaining thirteen, recorded in 2009, is separate
from this lower-bound argument; its [provenance](../34-18-3/sources.md) is retained.

## Build and verify

**Lean-verified, 23 October 2026.** Import `CoveringDesigns.C35_19_4` and use
`CoveringDesigns.lower_bound_35_19_4`. The public theorem requires only
the point count and ordinary covering condition on arbitrary finite labels.
The [proof appendix](proof.md#appendix-a-lean-correspondence) gives its
contract and audits.

From the repository root, with the [shared prerequisites](../../technical-details.md):

```sh
./covering verify 35-19-4
./covering audit 35-19-4
```

The first command compiles the component and its prerequisites and runs its
theorem audits; the second validates the recorded verification.
