# C(11,5,2) = 7 and the two minimum covering types

**Proof reconstruction and Lean formalisation: Rob Gardiner.**

Credit is for the reconstructed proof and formalisation presented here, not
for first proving the covering number or classification. The original
results retain the historical attributions given below.

**Supporting proof of a known result.** Seven five-element blocks are
necessary and sufficient to cover all pairs of eleven points. Every
seven-block covering belongs to exactly one of two isomorphism types.

**Proof provenance: a reconstruction.** This self-contained Lean proof uses
Rob Gardiner's structural reconstruction, with shortenings made during
formalization. Stanton's original chapter has not been obtained, so this is
not claimed to translate or reproduce his proof.

Read the [self-contained mathematical proof](proof.md) for the full
argument, explicit representatives and source comparisons. Its
[geometry section](proof.md#8-the-intrinsic-geometry-used-by-gppt) proves the
properties used by GPPT; the [correspondence appendix](proof.md#appendix-a-correspondence-with-lean)
maps every stage to its Lean declarations.

## Attribution and contribution

GPPT attribute the classification to R. G. Stanton in their Theorem 3.1.
The known classification is credited to Stanton; no historical novelty is
claimed for the reconstructed argument.

The proof forces a block of five degree-three points. The other six blocks
then determine doubled edges and complementary triples, giving a single
partial template. Its whole-pair and transversal completions are the two
nonisomorphic types. The [source section](proof.md#sources-and-contribution)
identifies the reconstruction and the shortenings made during formalization.

## Role in the project

This proof depends only on the shared counting foundations, Lean and Mathlib.
Its classification and local geometry support the
[twelve-point structural proof](../12-6-3/README.md) and the
[thirteen-point compatibility argument](../13-7-4/README.md).

The numerical minimum, classification and nonisomorphism of the two types
are all proved here; none is imported as an assumption from the literature.

## Build and verify

The public import is `CoveringDesigns.C11_5_2`. Its main theorems are
`CoveringDesigns.covering_number_11_5_2` and
`CoveringDesigns.stanton_classification_unique_on`.
The latter assigns each minimum covering exactly one representative type;
it does not assert a unique point permutation. The local geometry has the
separate imports `CoveringDesigns.C11_5_2.Geometry` and
`CoveringDesigns.C11_5_2.Geometry.Fano`; both depend on this standalone proof.
See the [contracts and verification appendix](proof.md#appendix-b-contracts-dependencies-and-verification)
for the precise boundary between structural arguments, fixed kernel checks
and the recorded audits.

See the [verification guide](../../technical-details.md) for setup and
reproduction. The [component audit](../../lean/audits/C11_5_2.lean) checks
the theorem statements, representatives, nonisomorphism and axiom dependencies.
