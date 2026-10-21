# C(18,10,3) = 12 and five Schönheim lifting bounds

**Rob Gardiner**

Every covering of the triples of 18 points by 10-element blocks needs at
least 12 blocks. The structural lower-bound proof, together with a known
12-block construction, establishes **C(18,10,3)=12**. Schönheim lifting gives
five further lower bounds. All six conclusions are proved in Lean for
arbitrary finite point types:

| Parameter | Proved result |
|---|---:|
| C(18,10,3) | =12 |
| C(19,11,4) | ≥21 |
| C(20,12,5) | ≥35 |
| C(21,13,6) | ≥57 |
| C(22,14,7) | ≥90 |
| C(23,15,8) | ≥138 |

Read the [mathematical proof](proof.md) for the full argument, construction
and [Lean correspondence](proof.md#appendix-a-lean-correspondence).
The last five results are lower bounds, not exact values. The
[source assessment](sources.md), dated **20 October 2026**, located earlier
lower bounds 19, 32, 52, 82 and 126, respectively; it records the evidence and
remaining historical-priority questions.

## Proof in outline

Point links force every point to occur in at least 6 blocks. An 11-block
cover would therefore have either one point of degree 8 or two of degree 7,
with all other degrees equal to 6. Pairs occurring in exactly 2 blocks would
force a matching whose edges need 16 different supporting blocks, which is
impossible.

With every pair occurring at least 3 times, a rank bound leaves one equality
case. Equality forces five pairs of points with identical supports and six
remaining low-degree points. Counting the two exceptional blocks selects
two paired classes absent from both. Inclusion–exclusion on their actual
supports then produces an uncovered triple.

Starting from $L_0=12$, the lifting argument retains every ceiling in
$L_s=\lceil(18+s)L_{s-1}/(10+s)\rceil$. This gives the sequence
12, 21, 35, 57, 90, 138.

## Supporting results and construction

The proof derives its link, multiplicity and rank conditions. Its reusable
ingredients concern equality in the rank bound, incidence packing and
support intersections. The final covering theorems require only the point
count and coverage conditions; the seed also has an adapter allowing
repeated block occurrences.

The [12-block construction](proof.md#8-historical-attainment) is historical:
the retained La Jolla Covering Repository entry credits “JCD article”.
The included [Lean witness](../../lean/CoveringDesigns/C18_10_3/Witness.lean)
checks the complete block list. Attribution is to Daniel M. Gordon / La Jolla
Covering Repository under CC BY 4.0; [sources](sources.md#historical-attaining-construction)
gives the public archive and source metadata. Schönheim is credited for lifting. Rob Gardiner's contribution
is the structural lower proof and its Lean formalisation, developed with
substantial AI assistance; the construction is not claimed as new.

## Build and verify

The public imports are `CoveringDesigns.C18_10_3` and
`CoveringDesigns.Applications.C18103Lifts`.
`CoveringDesigns.covering_number_18_10_3_on` states both exact attainment and
the universal lower bound. The five lifting contracts are listed in
[Appendix A](proof.md#appendix-a-lean-correspondence).

The [shared verification guide](../../technical-details.md) explains setup.
[Appendix B](proof.md#appendix-b-reuse-boundaries-and-verification) gives the
dependency boundaries, focused verification commands and audit scope.
