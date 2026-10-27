# Sources, attribution and dated comparison

The proof combines earlier geometric and arithmetic results with the
project's positive-load classification. Rob Gardiner, with Codex assistance,
provided the formalisation and covering-level assembly. The following
assessment is dated 26 October 2026; first-publication priority for the
complete family formula remains unresolved.

Z. Füredi, *Covering pairs by q²+q+1 sets*, J. Combin. Theory A **54** (1990),
248–271, [DOI](https://doi.org/10.1016/0097-3165(90)90034-T), supplies the
historical geometric classification and dimension argument. The project's
[PairEquality account](../pair-equality/proof.md) records the precise
classification and twisted-maximality attribution. The current proof uses
that verified interface. Füredi §6 already treats the q²+q-coordinate
geometric strategy; it must not be described as new here.

The positive extension and equal-load classification is the project's
separate [TruncatedPlaneLoads result](../truncated-plane-loads/README.md),
by Rob Gardiner with Codex. It retains positive additional supports and
deduces integer q-divisibility. This assembly imports it unchanged.

J. Bierbrauer, S. Marcugini and F. Pambianco, *Projective planes, coverings
and a network problem*, Designs, Codes and Cryptography **29** (2003), 71–89,
[DOI](https://doi.org/10.1023/A:1024140122167), is a direct historical
antecedent. The inspected author manuscript's Lemma 6 contains the twisted
mate equations; its finite-plane constructions and replication arguments
are relevant antecedents for attainment. We do not claim these arithmetic
or construction ideas as new.

The twisted determinant obstruction is historical. Füredi printed p.250
states the corresponding square condition. Aart Blokhuis, Dieter Jungnickel and Bernhard Schmidt, *On a class of symmetric
divisible designs which are almost projective planes* (2001), pp. 27–34,
[DOI](https://doi.org/10.1007/978-1-4613-0283-4_2), Proposition 1.2 and equation (3), give the relevant
almost-plane determinant calculation and credit Bose–Connor (1952).
Bose–Connor's original was not inspected. The formal proof here derives the Gram identity and determinant directly
from the verified mate interface; none of these external claims is an axiom.

The published-BMP discrepancy remains unresolved. The inspected author
manuscript's Corollary 1 appears to assert whole-family containment in a
projective plane. The preserved positive-extra-support control has a
two-coordinate support intersection, so that stronger reading cannot be
used. Whether the published version or some additional hypothesis resolves
the wording was not established in the retained review. Hall–Horsley–Stinson,
*Bounds on data limits for all-to-all comparison from combinatorial designs*,
[arXiv:2309.00213](https://arxiv.org/abs/2309.00213), gives a related weaker
core conclusion. The present proof relies on the separately verified
core-or-twisted dichotomy and the load theorem, not the disputed clause.

The [LJCR metadata](https://raw.githubusercontent.com/dmgordo/LJCR/main/coverings/coverdata.json)
retrieved on 26 October 2026 records 20–21 for
k=9,10,11,13,14,15,17,18,19,21,22,23, with v=4k.
The retrievals were at 14:54 and 14:57 UTC, with metadata
SHA-256 `0984bb8b4c89fe07268569b9814794e3c8852302d075f0794140f202e83d7fef`.
The theorem establishes 21 throughout those twelve entries; this meaningful
comparison does not establish when the full formula was first proved.

## Barker witness and licence

The retained LJCR metadata credits **Colin Barker**, **Simulated Annealing**,
**1 December 2008, 09:10:02**, for 21 blocks at (44,11,2). The source is the
La Jolla Covering Repository, curated by Daniel M. Gordon. The witness is
licensed [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/),
copyright (c) 2024 Daniel M. Gordon.
The [LJCR record](https://ljcr.dmgordon.org/cover/show_cover.php?v=44&k=11&t=2)
identifies the covering. The source archive was decoded to JSON, with
provenance fields added and the original labels and block order retained.
The [Lean transcription](../../lean/CoveringDesigns/C4k_K_2/Barker.lean)
subtracts one from each label.

The ordered one-based raw bytes have SHA-256
`523a8bdc8338e034c465532bd2207a644d8ae1131688bbcda465aa65d3a9a794`;
the compressed SHA-256 is
`a97881d397f3396d29ae38c91dd8fb5735098fe836e6135305a74bf17972a914`.
Independent correspondence checks connect those data to the Lean family.
Lean proves its block sizes, distinctness and pair coverage. The construction
remains credited to Barker.
