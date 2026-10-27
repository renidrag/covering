# Attribution, preserved witnesses and dated comparisons

Rob Gardiner, with Codex assistance, provided the formalisation and
assembly. Earlier results and constructions retain their original authorship.
The historical assessment below retains its 26 October 2026 date. The
comparison section records the additional 27 October observations. It distinguishes
mathematical dependence, comparison with a dated catalogue and historical
first-publication priority.

## Geometry, loads and arithmetic

**Zoltán Füredi**, *Covering pairs by q²+q+1 sets*, Journal of Combinatorial
Theory, Series A **54** (1990), 248–271,
[DOI](https://doi.org/10.1016/0097-3165(90)90034-T), supplies the historical
geometric classification. The original Theorem 2.2 distinguishes a contained
truncated core from an entire twisted plane. The unchanged included
[PairEquality proof](../pair-equality/proof.md) formalises the needed bridge.
The square obstruction already appears on printed p.250. The current work
does not claim discovery of that obstruction or its order-seven/nine
specialisations.

**Aart Blokhuis, Dieter Jungnickel and Bernhard Schmidt**, *On a class of
symmetric divisible designs which are almost projective planes*, in
*Finite Geometries* (2001), 27–34,
[DOI](https://doi.org/10.1007/978-1-4613-0283-4_2), Proposition 1.2 and
its determinant proof, give the same arithmetic restriction with their
k=q+1. The inspected author PDF credits
Bose–Connor's 1952 theory; the latter original and the full 1985
Lamken–Mullin–Vanstone paper were not obtained. Later restrictions requiring
an abelian Singer group are not applied to arbitrary twisted planes here.

**Jürgen Bierbrauer, Stefano Marcugini and Fernanda Pambianco**, *Projective
planes, coverings and a network problem*, Designs, Codes and Cryptography
**29** (2003), 71–89,
[DOI](https://doi.org/10.1023/A:1024140122167), provides historical weighted
replication and mate-incidence identities. The inspected artifact is a
24-page author manuscript, not the
19-page journal typesetting. Its Corollary 1's whole-family containment
clause has a positive-load counterexample; it is not used as a premise.
The final published version remains an unresolved source comparison.
An error in the unseen published version is not asserted.

That manuscript's Theorem 12 explicitly asserts network exclusions behind
C(70,14,2)≥31 and C(95,19,2)≥31, though its inspected proof uses the disputed
clause. These are prior assertion evidence, not sound substitutes for the
included verified core-load argument. Its Theorem 11 similarly bears on
the earlier (44,11,2) seed. The manuscript's network C(n,k,r) uses block-size
and point-degree upper bounds, rather than our strength notation; exact
point-degree equality licenses these translations. Thus these exclusions
have earlier stated antecedents even though the inspected derivation does
not replace the proof supplied here.

**Joanne Hall, Daniel Horsley and Douglas R. Stinson**, *Bounds on data
limits for all-to-all comparison from combinatorial designs*, Designs,
Codes and Cryptography **92** (2024), 2863–2879,
[DOI](https://doi.org/10.1007/s10623-024-01418-6), was inspected in its final
published version. Its Theorems 4.7 and 4.12 and Lemma 4.9
give related contained-core geometry and arithmetic, with positive weights
and merged duplicate types explicit. They do not justify discarding positive
extra supports. Their dated statements on known examples are not updated
existence or nonexistence claims for 2026.

The complete positive truncated-core multiplicity forms and converse belong
to the project's separately proved [load component](../truncated-plane-loads/proof.md).
This account composes it with the unchanged geometric bridge and the already
proved order-four exclusion. It adds no new classification proof, uniqueness
claim or isomorphism classification. Historical priority of the full load
description and some numerical deductions remains unresolved. One relevant
unread source is D. T. Todorov, *Lower bounds for coverings of pairs by large
blocks*, Combinatorica **9** (1989), 217–225,
[DOI](https://doi.org/10.1007/BF02124682). Its abstract concerns fixed-ratio
lower bounds for sufficiently large block size; the original text was not
obtained, so its implications for these ranges remain unassessed.

## Constructions and exact witness provenance

Affine/projective planes, point replication, restriction and padding are
classical. BMP's weighted-arc construction and Horsley–Singh's affine
construction are historical antecedents. The new wider weighted interface
recovers all qk+r actual points from the geometry; the older verified
endpoint interface alone was not used to infer the larger interval.

| Historical witness | Contributor | Recorded method | Contribution time |
|---|---|---|---|
| (65,13,2), 31 blocks | Flavio Perona | Not specified | 21 May 2011, 03:32:48 |
| (95,19,2), 31 blocks | Jan de Heer and Steve Muir | Private tools | 16 March 2011, 12:50:04 |

Both are preserved La Jolla Covering Repository constructions, curated by
**Daniel M. Gordon**. The retained compressed uint8 rows and one-based JSON
are unchanged. The Lean transcription subtracts one from each label and
keeps the row order. Independent correspondence checks are distinct from
the kernel proofs of uniformity, distinctness and coverage.

| Parameters | Compressed SHA-256 | Ordered raw SHA-256 |
|---|---|---|
| (65,13,2) | `c384aa5d3e8f9e7645bbf9225bf3fc6cfbb787d478db309865a95c04cf4ec32a` | `e3a90d45e3c09454e0f28b74ae9fc6d2566427d538374cc06440ce4f24d04251` |
| (95,19,2) | `31d847886d5b7b215b10eee36b179025b3c69dff8251d2f2698637dbf564b3dd` | `737d45c06ddb51ff1062b9c5ee0ce4bda1f485ac9f8fe68656b5958145ad9cb3` |

The source is [LJCR](https://ljcr.dmgordon.org/), under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/), copyright (c) 2024
Daniel M. Gordon. Archive decoding to JSON adds provenance fields and
preserves labels and block order. The subsequent Lean transcriptions are
[Perona](../../lean/CoveringDesigns/Qk_K_2/Perona.lean) and
[de Heer–Muir](../../lean/CoveringDesigns/Qk_K_2/DeHeerMuir.lean).
The historical catalogue records are
[(65,13,2)](https://ljcr.dmgordon.org/cover/show_cover.php?v=65&k=13&t=2) and
[(95,19,2)](https://ljcr.dmgordon.org/cover/show_cover.php?v=95&k=19&t=2).
The formal geometric constructions are not asserted to equal
any retained generated list. Perona and de Heer–Muir are not credited to
the simple line-weight recipe, whose hypotheses fail for their parameters.

## Schönheim lifting and the retained comparison

**J. Schönheim**, *On coverings*, Pacific Journal of Mathematics **14**
(1964), 1405–1411, Theorem I, p.1407,
[original](https://msp.org/pjm/1964/14-4/pjm-v14-n4-p29-p.pdf), is the
source of the recurrence. All 53 inequalities are consequences of the
unchanged C(4k,k,2) lower family and this recurrence, not separate methods.
The earlier weaker Lean proofs and published accounts remain intact.

The exact LJCR metadata snapshot was retrieved at
**2026-10-26T15:58:28.498822Z**, SHA-256
`0984bb8b4c89fe07268569b9814794e3c8852302d075f0794140f202e83d7fef`.
It comes from the [LJCR metadata](https://raw.githubusercontent.com/dmgordo/LJCR/main/coverings/coverdata.json).
The [complete comparison table](lifting.md) contains all 59 descendants:
53 have matching entries and six have unavailable comparisons. None of the
53 reaches the listed upper bound. Expert curation makes the catalogue comparison informative, but it
is neither a proof premise nor evidence of when each deduction first appeared.
Other historical lower methods might independently imply individual rows.

## Comparison dates and the combined table

The [combined table](bounds.md) is the reader's complete numerical list.
Its 151 parameter triples are distinct: 59 earlier order-four lifts,
78 direct additions and 14 order-six consequences. The earlier component
tables are retained as subsets for verification and existing links.

The 53 earlier LJCR comparisons use the exact 26 October snapshot identified
above. The additional rows retain the 26/27 October 2026 snapshot and refresh:
50 direct additions and nine order-six rows improve the corresponding LJCR
lower entries. Five direct additions and two order-six rows instead use cvkt
claims recorded on 17 October 2026 and read on 27 October, where LJCR
comparisons were unavailable. The remaining six earlier, 23 direct and three
order-six rows have no retained external comparison. A missing comparison
is not evidence of a new result. No fresh external search was performed
when consolidating the table on 27 October.

These are consequences of the stated universal pair bounds and Schönheim's
recurrence. Their proof does not depend on catalogue data. In particular,
the lower-only seed C(70,14,2)≥31 can be lifted without a construction.
The determinant parity test is an explicit simplification of the historical
square obstruction. The primitive quotient uses the proved mate-load equations;
its converse is positive uniform replication. These statements do not assert
existence of a twisted plane or a primitive covering at an unspecified order.

For the unrestricted order-six bound, R. H. Bruck and H. J. Ryser,
*The nonexistence of certain finite projective planes*, Canadian Journal of
Mathematics **1** (1949), 88–93,
[Theorem 1](https://doi.org/10.4153/CJM-1949-009-2), is the historical source
of projective-plane nonexistence. The included [order-six account](../6k-k-2/proof.md)
proves the needed special case and its covering deduction in Lean.
Its two pair seeds and twelve lifts are now verified; no external
nonexistence assertion remains a formal premise.
