# (7a+4,3a+2,2) coverings with 7 blocks

**Proof and Lean formalisation: Rob Gardiner**

For every integer a≥1, a (7a+4,3a+2,2) covering with 7 blocks has one of
two forms, up to relabelling. Both are built from the Fano plane, with
specified numbers of points sharing each support. The two forms are not
isomorphic.

The proof allows repeated block occurrences and shows that the 7 blocks
must be distinct. Points with the same support are still counted separately.
The result is proved in Lean. Read the [proof](proof.md).

| Range | Exact value | Classification |
|---|---|---|
| a≥2 | C(7a+4,3a+2,2)=7 | Two forms based on the Fano plane |
| a=1 | C(11,5,2)=7 | The same forms, using Stanton's classification |

## Proof in outline

Counting forces exactly two points to lie in 4 blocks each; every other
point lies in 3. The supports of those other points form the lines of a
Fano plane. The block sizes then determine the number of points with
each support and the two possible arrangements of the exceptional points.
Those two points occur together in either 2 or 4 blocks, which distinguishes
the forms. Both constructions use 7 blocks.

## Supporting results and attribution

The exact values were already known, and the classification follows from
earlier results described in [sources.md](sources.md). This account gives
a direct proof and Lean verification. The a=1 case uses the included
[Stanton proof](../11-5-2/README.md).

The proof of [C(19,9,3)=17](../19-9-3/README.md) uses only a=2: the
classification of (18,8,2) coverings with 7 blocks.

## Build and verify

Use `./covering verify seven-block-core` for a≥2 and
`./covering verify seven-block` for all a≥1. Their public entries are
`CoveringDesigns.SevenBlock.Core` and `CoveringDesigns.SevenBlock`;
the classification theorem is `SevenBlock.classification`.

The [proof appendix](proof.md#appendix-a-lean-correspondence-and-evidence-boundary)
links the argument to Lean and lists the dependencies. The shared
[verification guide](../../technical-details.md) explains setup and checking.
