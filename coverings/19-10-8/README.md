# A Schönheim corollary: $C(19,10,8)\ge1908$

**Deduction and Lean formalisation: Rob Gardiner, with AI assistance.**

Every family of 10-element subsets covering all 8-element subsets
of a 19-point set has at least **1908 distinct blocks**. This is the
fifth of five lower bounds obtained from this project's
[structural proof of $C(14,5,3)\ge41$](../14-5-3/README.md)
by successive applications of Schönheim's classical lifting theorem:

| Parameters and proof account | Proved lower bound |
| --- | ---: |
| [$(15,6,4)$](../15-6-4/README.md) | $C(15,6,4)\ge103$ |
| [$(16,7,5)$](../16-7-5/README.md) | $C(16,7,5)\ge236$ |
| [$(17,8,6)$](../17-8-6/README.md) | $C(17,8,6)\ge502$ |
| [$(18,9,7)$](../18-9-7/README.md) | $C(18,9,7)\ge1004$ |
| [$(19,10,8)$](proof.md) | $C(19,10,8)\ge1908$ |

Each row supplies the universal lower bound needed for the next row.
These are five corollaries of the same structural seed.

The contribution here is the explicit deduction and its Lean proof.
The [mathematical account](proof.md) gives the statement, complete lifting
argument and every ceiling from the 41 seed. Attainment at 1908 is not asserted.

The Covering Repository query of **23 October 2026** displayed lower bound
**1722**; this result improves that entry by **186**.
The starting bound $C(14,5,3)\ge41$ was published by this project on
22 October 2026. The [source account](sources.md) records the dated
comparison, attribution and publication history.

## Proof in outline

Fix a point and delete it from every block containing it. The resulting
family covers all 7-subsets of the remaining 18 points with
9-sets. The [preceding bound](../18-9-7/README.md) forces at
least 1004 blocks through each point.

Counting incidences between points and blocks therefore gives
$10|\mathcal C|\ge19\cdot1004=19076$.
Rounding up yields
$|\mathcal C|\ge\lceil19076/10\rceil=1908$.
The same point-link argument gives each preceding row in the chain.

## Supporting results and attribution

Schönheim supplies the lifting method; this project's 41 theorem supplies
the improved starting value. The five corollaries share that one structural
input. Each step uses the preceding universal lower theorem.

## Build and verify

Lean-verified on **23 October 2026**. Import `CoveringDesigns.C19_10_8`
and use `CoveringDesigns.lower_bound_19_10_8`.
The only mathematical hypotheses are the point count and ordinary coverage.
The [proof appendix](proof.md#appendix-a-lean-correspondence) gives the
full contract, dependencies and audit correspondence.

From the repository root, with the [shared prerequisites](../../technical-details.md):

```sh
./covering verify 19-10-8
./covering audit 19-10-8
```

The first command compiles the component and its prerequisites and runs the
theorem audits. The second validates the resulting verification record.
