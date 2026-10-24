# A Schönheim corollary: $C(18,9,7)\ge1004$

**Deduction and Lean formalisation: Rob Gardiner, with AI assistance.**

Every family of 9-element subsets covering all 7-element subsets
of an 18-point set has at least **1004 distinct blocks**. This is the
fourth of five direct Schönheim corollaries. Its dependencies are:

| Result | Proved universal premise |
| --- | --- |
| [$C(15,6,4)\ge103$](../15-6-4/README.md) | [$C(14,5,3)\ge41$](../14-5-3/README.md) |
| [$C(16,7,5)\ge236$](../16-7-5/README.md) | [$C(15,6,4)\ge103$](../15-6-4/README.md) |
| [$C(17,8,6)\ge502$](../17-8-6/README.md) | [$C(16,7,5)\ge236$](../16-7-5/README.md) |
| [$C(18,9,7)\ge1004$](proof.md) | [$C(17,8,6)\ge502$](../17-8-6/README.md) |

The contribution here is the explicit deduction and its Lean proof.
The [mathematical account](proof.md) gives the short proof from the
preceding bound. Attainment at 1004 is not asserted.

The Covering Repository query of **23 October 2026** displayed lower bound
**906**; this result improves that entry by **98**.
The starting bound $C(14,5,3)\ge41$ was published by this project on
22 October 2026. The [source account](sources.md) records the dated
comparison, attribution and publication history.

## Proof in outline

Deleting a point from the blocks through it gives a $(17,8,6)$
covering. The proved premise forces at least 502 blocks through every point.
Counting incidences and rounding up gives
$$
9|\mathcal C|\ge18\cdot502=9036,
\qquad
|\mathcal C|\ge\left\lceil9036/9\right\rceil=1004.
$$

## Supporting results and attribution

Schönheim supplies the point-link argument. This project's
[structural proof of $C(14,5,3)\ge41$](../14-5-3/README.md) supplies the
stronger seed; each later step uses the preceding proved universal bound.
The [five-result overview](../19-10-8/README.md) displays the full chain.

## Build and verify

Lean-verified on **23 October 2026**. Import `CoveringDesigns.C18_9_7`
and use `CoveringDesigns.lower_bound_18_9_7`.
The only mathematical hypotheses are the point count and ordinary coverage.
The [proof appendix](proof.md#appendix-a-lean-correspondence) gives the
full contract, dependencies and audit correspondence.

From the repository root, with the [shared prerequisites](../../technical-details.md):

```sh
./covering verify 18-9-7
./covering audit 18-9-7
```

The first command compiles the component and its prerequisites and runs the
theorem audits. The second validates the resulting verification record.
