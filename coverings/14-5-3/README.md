# 41 ≤ C(14,5,3) ≤ 43

**Rob Gardiner — structural argument and Lean formalisation, with AI assistance.**

Every covering of the triples of fourteen points by five-element blocks
needs at least **41 blocks**. A historical construction with **43 blocks**
gives the upper bound. The ordinary-family result holds on every finite
fourteen-point type; a separate lower-bound interface permits repeated
block occurrences. Neither 41 nor 42 is excluded, and no exact value is
asserted.

Read the [self-contained proof](proof.md) for the structural argument,
construction and [Lean correspondence](proof.md#appendix-a-lean-correspondence).
The [source account](sources.md) credits the known deletion antecedent and
construction. The bounded historical assessment did not establish an earlier
complete implication of the lower bound 41; this is not a first-discovery claim.

## Proof in outline

An exact thirteen-point pair design has 234 noncollinear triples. A parity
argument and a linewise divisibility obstruction show that covering these
triples by five-sets needs at least 27 occurrences. Point links then give
C(14,5,3)≥40, so a hypothetical forty-occurrence cover is irredundant.

Fourteen-occurrence pair links have a removable block. Their special parent
blocks have private triples and disjoint excess charges. These exclude the
branch with no degree-13 point and sharply restrict the other branch.
Compatibility of four exact point links forces a point of degree at least
16, contradicting the remaining degree budget. After the lower bound 41 is
proved, adjoining a new point strengthens the universal completion bound
to **28 occurrences**.

## Supporting results and construction

The proof reuses the library's indexed incidence, point/subset links,
exact-design counting and extension identities. It does not use plane
coordinates, a uniqueness classification, rank inequalities, exhaustive
covering classification or an external exclusion certificate.

The removable-block result is a self-contained order-three special case of
**Sharad S. Sane's projective failed-design theorem**. The historical upper
witness is credited to **Nurmela and Östergård's simulated annealing**, with
repository date 1 December 1996. Its [original labelled blocks and provenance](../../data/c1453-historical-witness.json)
are retained from Daniel M. Gordon's La Jolla Coverings Repository,
CC BY 4.0. Lean checks the explicit witness and transports it to arbitrary
fourteen-point labels.

## Recommended interfaces

Import `CoveringDesigns.C14_5_3`. These eight entry points cover the result
and its principal reusable consequences; names have prefix `CoveringDesigns.`.
Their precise hypotheses and helper correspondence are in the
[proof appendix](proof.md#exact-contract-scope-and-representation).

| Purpose | Declaration |
|---|---|
| Ordinary lower bound | `lower_bound_14_5_3` |
| Repeated-occurrence lower bound | `indexed_lower_bound_14_5_3` |
| Arbitrary-label interval | `covering_interval_14_5_3_on` |
| Actual historical upper witness | `upper_bound_14_5_3_on` |
| Exact-link completion ≥28 | `C14_5_3.completion_at_least_28` |
| Deletion from a fourteen-occurrence pair link | `C14_5_3.almost_exact_deletion` |
| At most four minimum points | `C14_5_3.minimum_points_le_four` |
| Four-point compatibility | `C14_5_3.four_minimum_forces_sixteen` |

These are fixed-parameter results on arbitrary finite labels. Construction
accessors, specialisations and finer helpers remain available and audited.

## Build and verify

The public import is `CoveringDesigns.C14_5_3`. The principal declaration is
`CoveringDesigns.covering_interval_14_5_3_on`; its lower-bound premise is only
the ordinary covering condition and point cardinality. It also supplies an
actual ordinary covering of cardinality 43.

Use the [verification guide](../../technical-details.md) for setup, then
`./covering verify 14-5-3` for fresh focused compilation and audits, or
`./covering verify` for the whole library. `./covering audit 14-5-3` validates
existing verification records without recompiling. The
[component audit](../../lean/audits/C14_5_3.lean) checks all public contracts,
expanded covering conditions, boundary examples and transitive axioms.
