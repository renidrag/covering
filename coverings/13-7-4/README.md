# C(13,7,4) = 30

**Rob Gardiner**

**New result.** Every covering of the four-element subsets of thirteen
points by seven-element blocks needs at least thirty blocks. The new
contribution is the structural lower-bound proof; a known thirty-block
construction supplies the upper bound.

Read the [mathematical proof](proof.md) for the full argument and attribution.

## Proof in outline

A hypothetical covering with at most 29 blocks has at least five points
of minimum degree fifteen. Compatibility of their links forces the following
numbers of blocks through subsets of these points:

| Number of points | Blocks containing them |
|---|---:|
| One | 15 |
| Two | 7 |
| Three | 3 |
| Four | 1 |

Inclusion–exclusion on five minimum points then gives at least

$$
5\cdot15-10\cdot7+10\cdot3-5\cdot1=30
$$

blocks, a contradiction. Proving the pair and four-point compatibility
statements is the main work.

## Supporting results and construction

The argument uses the proved [Stanton classification](../11-5-2/README.md)
and [GPPT structural reduction](../12-6-3/README.md). It works with arbitrary
completions of GPPT's forms; the separate 68-entry catalogue calculation
is not a prerequisite.

The thirty-block construction comes from the
[La Jolla Covering Repository](https://ljcr.dmgordon.org/cover/show_cover.php?k=7&t=4&v=13).
The [original blocks](../../data/ljcr-30-one-based.txt) and
[zero-based data](../../data/ljcr-30.json) are retained, and the same
construction is checked in Lean.

## Build and verify

The public import is `CoveringDesigns.C13_7_4`; the theorem is
`CoveringDesigns.covering_number_13_7_4`. It asserts both the existence of a
thirty-block covering and the lower bound for every covering, with no
classification or compatibility assumptions.

The [verification guide](../../technical-details.md) explains dependency
setup and how to reproduce the checks.
[Appendix A of the proof](proof.md#appendix-a-lean-correspondence-and-dependency-checks)
maps the mathematical steps to Lean sources and describes the theorem audit.
[Appendix B](proof.md#appendix-b-verification-and-retained-artifacts)
gives verification commands, construction data and source provenance.
