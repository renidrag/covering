# The exact covering number $C(34,18,3)=13$

**Exactness deduction and Lean formalisation: Rob Gardiner, with AI assistance.**

Exactly **13 blocks of size 18** are needed to cover all triples of a
34-point set. This account combines the project's lower bound with the
historical LJCR construction and proves both directions in Lean on
arbitrary point labels.

Read the [mathematical proof](proof.md) for the lower-bound substitution,
the explicit family and the final exactness argument.

## Proof in outline

The project's offset-two theorem says that a triple covering on $2k-2$
points by $k$-element blocks needs at least 13 blocks when $k\ge18$.
Putting $k=18$ gives the required lower bound on 34 points.

For the upper bound, take the 13 historical blocks described in the
proof. Each has 18 points, the blocks are distinct, and direct finite
verification shows that they cover all $\binom{34}{3}=5,984$ triples.
The two bounds agree. A bijection transfers the same construction to any
34-point set.

## Supporting results and construction

The lower argument is reused from this project's
[offset-two account](../2k-minus-c-k-3/README.md). That argument combines
Horsley and Singh's bound with the project's saturated-pair exclusion.
The source attributes the attaining family to **LJCR**, describing it as a
**“Multiple of (17,9,3) covering”**, recorded on **20 January 2009**.
The [retained blocks](../../data/c34183-historical-witness.json) preserve
Daniel M. Gordon / La Jolla Covering Repository's CC BY 4.0 credit.

The contribution of this account is the explicit exactness deduction and
the Lean proof connecting that historical family to the lower theorem.
The construction itself is historical. The lower theorem was first public on
19 October 2026 and retained in the 22 October cumulative package.

The Covering Repository query of **23 October 2026** displayed **12–13**.
The matching lower bound and construction establish the exact value **13**.
The [source account](sources.md) records the comparison, construction
provenance and publication history.

## Build and verify

Lean-verified on **23 October 2026**. Import `CoveringDesigns.C34_18_3`
and use `CoveringDesigns.covering_number_34_18_3_on`.
For any finite type with 34 points, it supplies an actual 13-block
cover and proves that every ordinary cover has at least 13 blocks.
The [proof appendix](proof.md#appendix-a-lean-correspondence) gives the
witness accessors, contract correspondence and verification details.

From the repository root, with the [shared prerequisites](../../technical-details.md):

```sh
./covering check
./covering verify 34-18-3
./covering audit 34-18-3
```

These commands check the retained data, compile and audit the Lean component,
and validate its verification record, respectively.
