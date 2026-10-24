# A Schönheim corollary: $C(16,7,5)\ge236$

**Deduction and Lean formalisation: Rob Gardiner, with AI assistance.**

Every family of 7-element subsets covering all 5-element subsets
of a 16-point set has at least **236 distinct blocks**. This is the
second of five direct Schönheim corollaries. Its dependencies are:

| Result | Proved universal premise |
| --- | --- |
| [$C(15,6,4)\ge103$](../15-6-4/README.md) | [$C(14,5,3)\ge41$](../14-5-3/README.md) |
| [$C(16,7,5)\ge236$](proof.md) | [$C(15,6,4)\ge103$](../15-6-4/README.md) |

The contribution here is the explicit deduction and its Lean proof.
The [mathematical account](proof.md) gives the short proof from the
preceding bound. Attainment at 236 is not asserted.

The Covering Repository query of **23 October 2026** displayed lower bound
**213**; this result improves that entry by **23**.
The starting bound $C(14,5,3)\ge41$ was published by this project on
22 October 2026. The [source account](sources.md) records the dated
comparison, attribution and publication history.

## Proof in outline

Deleting a point from the blocks through it gives a $(15,6,4)$
covering. The proved premise forces at least 103 blocks through every point.
Counting incidences and rounding up gives
$$
7|\mathcal C|\ge16\cdot103=1648,
\qquad
|\mathcal C|\ge\left\lceil1648/7\right\rceil=236.
$$

## Supporting results and attribution

Schönheim supplies the point-link argument. This project's
[structural proof of $C(14,5,3)\ge41$](../14-5-3/README.md) supplies the
stronger seed; each later step uses the preceding proved universal bound.
The [five-result overview](../19-10-8/README.md) displays the full chain.

## Build and verify

Lean-verified on **23 October 2026**. Import `CoveringDesigns.C16_7_5`
and use `CoveringDesigns.lower_bound_16_7_5`.
The only mathematical hypotheses are the point count and ordinary coverage.
The [proof appendix](proof.md#appendix-a-lean-correspondence) gives the
full contract, dependencies and audit correspondence.

From the repository root, with the [shared prerequisites](../../technical-details.md):

```sh
./covering verify 16-7-5
./covering audit 16-7-5
```

The first command compiles the component and its prerequisites and runs the
theorem audits. The second validates the resulting verification record.
