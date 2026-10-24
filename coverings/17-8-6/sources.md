# Sources and standing

**Comparison/access date: 23 October 2026.** These are dated observations;
release preparation has not repeated the literature search or table queries.

## Proved dependencies and attribution

J. Schönheim, *On coverings*, Pacific Journal of Mathematics **14** (1964),
1405–1411, [proof of Theorem I, p. 1407](https://msp.org/pjm/1964/14-4/pjm-v14-n4-p29-p.pdf#page=4),
supplies the point-link incidence step. Formula (6) states the classical
nested bound; the same step propagates the stronger universal seed here.

The structural seed is this project's [C(14,5,3)≥41 theorem](../14-5-3/proof.md),
first published on **22 October 2026** in v1.4.0. The
[pinned seed proof](https://github.com/renidrag/covering/blob/a2a726abb7ae1e26a37841f730abb90a34469c11/coverings/14-5-3/proof.md)
and its [Lean declaration](https://github.com/renidrag/covering/blob/a2a726abb7ae1e26a37841f730abb90a34469c11/lean/CoveringDesigns/C14_5_3.lean)
were inspected on 23 October. This result uses the included
[preceding universal bound](../16-7-5/proof.md).

The explicit corollary and Lean formalisation are credited to Rob Gardiner,
with AI assistance. This is a consequence of that published seed using
Schönheim's established method.

## Dated table comparison

The [Covering Repository search form](https://www.coveringrepository.com/systems.aspx) was queried with
(v,k,t,m)=(17,8,6,6) and displayed **453–614**.
The lower 502 improves that displayed entry by 49, while
matching the consequence of the already published seed. The
[construction entry](https://www.coveringrepository.com/history.aspx?id=115780) identifies the separate upper entry,
credited as **Moshe Milshtein Method: Tabu Search started from a 615-block covering previously created by Jan de Heer and Steve Muir**, with recorded date **12/01/2024** (day/month/year).
The downloaded blocks for this upper entry were not checked by this batch;
the displayed interval is not an independently verified construction or a
published lower-bound proof. This formalisation establishes a lower bound.

[Gordon's public metadata](https://github.com/dmgordo/LJCR/blob/main/coverings/coverdata.json)
inspected on the same date also reports lower 453. Such table entries
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
