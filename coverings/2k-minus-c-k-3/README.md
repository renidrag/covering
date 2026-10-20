# Lower bounds and exact values for $C(2k-c,k,3)$

**Rob Gardiner**

**Structural lower bounds and exact values.** We prove $C(20,11,3)=12$
and bounds for the families $C(2k-c,k,3)$ in the ranges below. The contribution
is the lower-bound argument and its Lean formalisation; known constructions
and established geometric methods supply the upper bounds.

Read the [mathematical proof](proof.md) for the full argument. The
[sources and attribution](sources.md) distinguish the project's arguments,
developed with AI assistance, from their established antecedents.

## Parameter ranges in $(v,k,t)$

Here $C(v,k,t)$ is the minimum number of distinct $k$-element blocks on
$v$ points that contain every $t$-element subset. Every row has **$t=3$**.

| Conditions on $v,k$ | Proved conclusion | Example |
|---|---|---|
| $v=20,\ k=11$ | $C(v,k,3)=12$ | $(20,11,3)$ |
| $v=2k-2,\ 17\le k\le30$ | $13\le C(v,k,3)\le14$ | $(32,17,3)$ |
| $v=2k-2,\ k\ge31$ | $C(v,k,3)=14$ | $(60,31,3)$ |
| $v=2k-3,\ k\ge59$ | $C(v,k,3)=14$ | $(115,59,3)$ |
| $k\ge50,\ \lceil49k/25\rceil\le v\le2k-2$ | $C(v,k,3)=14$ | $(196,100,3)$ |

The final row is exactly the range $c\ge2,\ k\ge25c$ with $c=2k-v$.
The rows overlap; the separate offset-two and offset-three bounds have
better thresholds. Every equality includes an attaining ordinary covering.
The interval $13$–$14$ asserts neither exactness nor a thirteen-block witness.

Against the [dated entries inspected on 19 October 2026](sources.md#comparison-with-recorded-table-entries),
the twenty-point result improves $11$–$12$ to exact twelve, and the
$(36,19,3)$, $(38,20,3)$ and $(48,25,3)$ cases improve $12$–$14$ to $13$–$14$.

## Proof in outline

A small block budget forces many points to have degree six. A pair occurring
in exactly two blocks is called saturated: triple coverage forces those two
actual blocks to cover the ground set. Counting across their exclusive parts
restricts how saturated pairs can share supporting blocks.

The twenty-point proof first uses a boundary-rank argument to force a
saturated pair, then excludes it by shared-block counting. For the family
bounds, capacity inequalities and compatibility between saturated pairs
exclude that alternative. The resulting incidence Gram matrix has
nonnegative pair excess over three. Partitioning or Caro–Tuza selection
gives the general bounds. The sharper offset-two argument combines rank
slack with affine dimension: too many points have too few possible block
supports. At $k=31$, the remaining saturated matching forces the same two
blocks to intersect in both four and sixteen points.

These are independent lower-bound arguments. Attaining constructions complete
the equalities; the family proof does not use $C(20,11,3)=12$ as a premise.

## Supporting results and construction

The proof develops the needed incidence, saturation, rank and selection
lemmas explicitly, assuming standard finite counting and linear algebra.
The sharper family thresholds use the actual-multiplicity form of
Horsley–Singh's selection/rank argument. The strengthened pair floor is proved
inside the hypothetical small-cover case; it is not assumed as a universal
bound for smaller coverings.

The [twelve-block witness](proof.md#8-attainment-a-known-witness-and-weighted-affine-planes)
is displayed in full and checked in Lean. Its dated repository attribution
is Jan de Heer. For the families, weighted expansion of the fourteen planes
of $\mathbb F_2^3$, followed by restriction, padding and deduplication, gives
at most fourteen blocks. The independent lower bounds force exact attainment.
No unavailable historical source is a proof premise.

## Build and verify

The principal public imports are `CoveringDesigns.C20_11_3`,
`CoveringDesigns.TwoKMinusC`, `CoveringDesigns.TwoKMinusTwoTightening`,
`CoveringDesigns.SaturatedMatching` and `CoveringDesigns.TwoKMinusCGeneral`.
Their final statements quantify over arbitrary finite point types, without
unproved structural or classification assumptions. The separate indexed
threefold pair-covering theorem applies for $k\ge33$; the ordinary
triple-covering threshold $k\ge31$ uses additional triple coverage.

The [verification guide](../../technical-details.md) explains dependency
setup and reproduction. [Appendix A](proof.md#appendix-a-lean-correspondence-and-dependency-contracts)
maps the numbered claims to exact Lean declarations and audits.
[Appendix B](proof.md#appendix-b-verification-and-supporting-modules)
gives the verification commands and supporting-module inventory.
