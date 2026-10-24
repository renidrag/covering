# Sources and standing

**Comparison/access date: 23 October 2026.** These are dated observations;
release preparation has not repeated the literature search or table queries.

## Proved dependencies and attribution

J. Schönheim, *On coverings*, Pacific Journal of Mathematics **14** (1964),
1405–1411, [proof of Theorem I, p. 1407](https://msp.org/pjm/1964/14-4/pjm-v14-n4-p29-p.pdf#page=4),
supplies the point-link incidence step. Formula (6) states the classical
nested bound; the same step propagates the stronger universal seed here.

The seed is this project's [offset-two theorem, Corollary 10](../2k-minus-c-k-3/proof.md#73-the-numerical-conclusions):
C(2k−2,k,3)≥13 for k≥18. At k=18 it gives C(34,18,3)≥13.
Its first public date is **19 October 2026**, as recorded in the
[release history](../../RELEASE_HISTORY.md). The
[22 October cumulative snapshot](https://github.com/renidrag/covering/blob/a2a726abb7ae1e26a37841f730abb90a34469c11/lean/CoveringDesigns/TwoKMinusC/OffsetTwo.lean)
was inspected on 23 October; it is a later publication of the same seed.
The separately named C34 declaration and this lifting batch were formalised
on 23 October. This result uses the included
[preceding universal bound](../36-20-5/proof.md).
The [historical C34 attaining family](../34-18-3/sources.md) is separate
from the lower-bound premise.

The explicit corollary and Lean formalisation are credited to Rob Gardiner,
with AI assistance. This is a consequence of that published seed using
Schönheim's established method.

## Dated table comparison

The [Covering Repository search form](https://www.coveringrepository.com/systems.aspx) was queried with
(v,k,t,m)=(37,21,6,6) and displayed **74–113**.
The lower 78 improves that displayed entry by 4, while
matching the consequence of the already published seed. The
[construction entry](https://www.coveringrepository.com/history.aspx?id=116508) identifies the separate upper entry,
credited as **Franco Atzeni Method: local search**, with recorded date **03/10/2024** (day/month/year).
The downloaded blocks for this upper entry were not checked by this batch;
the displayed interval is not an independently verified construction or a
published lower-bound proof. This formalisation establishes a lower bound.

[Gordon's public metadata](https://github.com/dmgordo/LJCR/blob/main/coverings/coverdata.json)
inspected on the same date also reports lower 74. Such table entries
and available-download claims do not establish historical priority.

## Limits of the historical comparison

The relevant older originals by Mills, Mills–Mullin and Todorov–Tonchev
were not inspected in full; the [general source account](../2k-minus-c-k-3/sources.md)
retains those qualifications. The current
[sixteen-cell computational deposit](https://zenodo.org/records/23465708)
could not be inspected anew. A previously read inventory supplied no claim
for this triple, and no certificates from it were replayed. These gaps limit
priority and exhaustive-current-comparison claims. They do not affect the
complete mathematical deduction or the unconditional Lean theorem here.
