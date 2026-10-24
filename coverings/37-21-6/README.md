# A Schönheim corollary: $C(37,21,6)\ge78$

**Deduction and Lean formalisation: Rob Gardiner, with AI assistance.**

Every family of 21-element subsets covering all 6-element subsets of a
37-point set has at least **78 distinct blocks**. This is the
third of five direct corollaries of this project's
[lower theorem $C(34,18,3)\ge13$](../34-18-3/README.md).
The immediate dependency is:

| Result | Proved universal premise |
| --- | --- |
| [$C(37,21,6)\ge78$](proof.md) | [$C(36,20,5)\ge44$](../36-20-5/proof.md) |

The contribution is the explicit deduction and its Lean formalisation,
using Schönheim's classical point-link argument. The [proof](proof.md)
gives the complete short argument. Attainment at 78 is not asserted.

The [five-result overview](../39-23-8/README.md) shows the whole chain.

The Covering Repository query of **23 October 2026** displayed lower bound
**74**; this deduction improves that entry by **4**. The lower bound
$C(34,18,3)\ge13$ follows from the project's general theorem published
on 19 October 2026. The [source account](sources.md) records the dated
comparison, attribution and publication history.

## Proof in outline

Deleting a point from every block through it gives a
$(36,20,5)$ covering. The universal premise forces at least
44 blocks through each point. Counting incidences and rounding up gives

$$
21|\mathcal C|\ge37\cdot44=1628,
\qquad |\mathcal C|\ge\left\lceil1628/21\right\rceil=78.
$$

## Supporting results and attribution

Schönheim's proof of Theorem I (1964, p. 1407) supplies the lifting step.
This project's [offset-two theorem, Corollary 10](../2k-minus-c-k-3/proof.md#73-the-numerical-conclusions)
gives $C(2k-2,k,3)\ge13$ for $k\ge18$. Setting $k=18$ supplies
the stronger seed $C(34,18,3)\ge13$; every subsequent ceiling is retained.
The historical LJCR family attaining thirteen, recorded in 2009, is separate
from this lower-bound argument; its [provenance](../34-18-3/sources.md) is retained.

## Build and verify

**Lean-verified, 23 October 2026.** Import `CoveringDesigns.C37_21_6` and use
`CoveringDesigns.lower_bound_37_21_6`. The public theorem requires only
the point count and ordinary covering condition on arbitrary finite labels.
The [proof appendix](proof.md#appendix-a-lean-correspondence) gives its
contract and audits.

From the repository root, with the [shared prerequisites](../../technical-details.md):

```sh
./covering verify 37-21-6
./covering audit 37-21-6
```

The first command compiles the component and its prerequisites and runs its
theorem audits; the second validates the recorded verification.
