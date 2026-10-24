# A Schönheim corollary: $C(39,23,8)\ge229$

**Deduction and Lean formalisation: Rob Gardiner, with AI assistance.**

Every family of 23-element subsets covering all 8-element subsets of a
39-point set has at least **229 distinct blocks**. This is the
fifth of five direct corollaries of this project's
[lower theorem $C(34,18,3)\ge13$](../34-18-3/README.md).
The immediate dependency is:

| Result | Proved universal premise |
| --- | --- |
| [$C(39,23,8)\ge229$](proof.md) | [$C(38,22,7)\ge135$](../38-22-7/proof.md) |

The contribution is the explicit deduction and its Lean formalisation,
using Schönheim's classical point-link argument. The [proof](proof.md)
gives the complete short argument. Attainment at 229 is not asserted.

The full chain is:

| Result and account | Lower bound |
| --- | ---: |
| [C(35,19,4)](../35-19-4/README.md) | 24 |
| [C(36,20,5)](../36-20-5/README.md) | 44 |
| [C(37,21,6)](../37-21-6/README.md) | 78 |
| [C(38,22,7)](../38-22-7/README.md) | 135 |
| [C(39,23,8)](proof.md) | 229 |

Each row supplies the universal premise for the next.

The Covering Repository query of **23 October 2026** displayed lower bound
**218**; this deduction improves that entry by **11**. The lower bound
$C(34,18,3)\ge13$ follows from the project's general theorem published
on 19 October 2026. The [source account](sources.md) records the dated
comparison, attribution and publication history.

## Proof in outline

Deleting a point from every block through it gives a
$(38,22,7)$ covering. The universal premise forces at least
135 blocks through each point. Counting incidences and rounding up gives

$$
23|\mathcal C|\ge39\cdot135=5265,
\qquad |\mathcal C|\ge\left\lceil5265/23\right\rceil=229.
$$

## Supporting results and attribution

Schönheim's proof of Theorem I (1964, p. 1407) supplies the lifting step.
This project's [offset-two theorem, Corollary 10](../2k-minus-c-k-3/proof.md#73-the-numerical-conclusions)
gives $C(2k-2,k,3)\ge13$ for $k\ge18$. Setting $k=18$ supplies
the stronger seed $C(34,18,3)\ge13$; every subsequent ceiling is retained.
The historical LJCR family attaining thirteen, recorded in 2009, is separate
from this lower-bound argument; its [provenance](../34-18-3/sources.md) is retained.

## Build and verify

**Lean-verified, 23 October 2026.** Import `CoveringDesigns.C39_23_8` and use
`CoveringDesigns.lower_bound_39_23_8`. The public theorem requires only
the point count and ordinary covering condition on arbitrary finite labels.
The [proof appendix](proof.md#appendix-a-lean-correspondence) gives its
contract and audits.

From the repository root, with the [shared prerequisites](../../technical-details.md):

```sh
./covering verify 39-23-8
./covering audit 39-23-8
```

The first command compiles the component and its prerequisites and runs its
theorem audits; the second validates the recorded verification.
