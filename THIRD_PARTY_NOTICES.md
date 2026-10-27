# Third-party notices and licence scope

The [MIT licence](LICENSE) applies to this project's original Lean proofs,
software and documentation. It does not relicense the reference papers,
externally sourced material or separately installed dependencies described
below. Their original authorship and applicable terms are retained.

## Reference papers

The following two articles' publisher records link to the
[Creative Commons Attribution 4.0 International licence (CC BY 4.0)](https://creativecommons.org/licenses/by/4.0/).
Combinatorial Press's [copyright policy](https://combinatorialpress.com/copyright-policy/)
also states that authors retain copyright and that its articles are published
under CC BY 4.0. These statements were checked on **14 October 2026**.
The [full licence](https://creativecommons.org/licenses/by/4.0/legalcode.en)
governs reuse, including retention of attribution, a licence link and an
indication of changes. No endorsement of this project by the authors or
publisher is implied.

The [source index](data/sources/manifest.jsonl) records the editions, source
URLs and SHA-256 hashes of the retained files. Both PDFs are reproduced
without changes to their bytes; only their local filenames were chosen here.
The Lean formalizations and proof notes are separate project contributions.

### GPPT paper

**Authors:** Daniel M. Gordon, Oren Patashnik, John Petro and Herbert Taylor.

**Published citation:** *Minimum (12,6,3) Covers*, **Ars Combinatoria 40**
(1995), 161-177. [Publisher's article and licence record](https://combinatorialpress.com/ars-articles/volume-040-ars-articles/minimum-12-6-3-covers/).

**Retained file:** [gppt-1995.pdf](data/sources/gppt-1995.pdf), downloaded from
[Daniel M. Gordon's author-hosted copy](https://dmgordon.org/papers/c-12-6-3.pdf).
This is the **15-page prepublication version dated 23 March 1994**, not the
journal's paginated edition. The filename uses the journal publication year.

**Licence basis:** the publisher declares the article CC BY 4.0. Reproduction
of the retained author version relies on that article-level declaration;
the author-hosted PDF does not supply a separate edition-specific licence
statement. The publisher's declaration is attributed here, not presented as
a new permission obtained directly from the authors.

The [Figure 1](data/gppt-figure1.json) and [Figure 6](data/gppt-figure6.json)
data transcribe the corresponding figures into lists of point labels, with
`T = 10` and `E = 11`. These format and notation changes are the project's;
the constructions and their historical attribution remain GPPT's.

### Mullin paper

**Author:** R. C. Mullin.

**Published citation:** *On Covering Pairs by Quintuples: The Cases
v congruent to 3 or 11 modulo 20*, **Journal of Combinatorial Mathematics
and Combinatorial Computing 2** (1987), 133-146.
[Publisher's article and licence record](https://combinatorialpress.com/jcmcc-articles/volume-002/on-covering-pairs-by-quintuples-the-cases-v-equiv-3-or-11-modulo-20/).

**Retained file:** [mullin-1987-quintuples.pdf](data/sources/mullin-1987-quintuples.pdf),
an unchanged 14-page scan of the published article obtained from the
[publisher's PDF](https://combinatorialpress.com/article/jcmcc/Volume%202/vol-002-paper%2011.pdf).

**Licence:** CC BY 4.0, as linked from the publisher's article record.

## La Jolla covering data

The [thirty-block list](data/ljcr-30-one-based.txt) is from Daniel M. Gordon's
[La Jolla Covering Repository](https://ljcr.dmgordon.org/cover/show_cover.php?k=7&t=4&v=13).
The [JSON version](data/ljcr-30.json) subtracts one from each point label.
The construction is credited to Kari J. Nurmela and Patric R. J. Östergård,
*Upper bounds for covering designs by simulated annealing*, **Congressus
Numerantium 96** (1993), 93-111, as documented in the C(13,7,4) proof.

The [archived LJCR dataset](https://zenodo.org/records/19735294) supplies a
[CC BY 4.0 licence notice](https://zenodo.org/api/records/19735294/files/LICENSE/content)
with **Copyright (c) 2024, Daniel M. Gordon**. Its disclaimer is retained here:

> THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
> IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
> FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
> AUTHOR OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
> LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
> OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
> SOFTWARE.

## Near-half triple coverings

The twelve-block C(20,11,3) witness displayed in the
[canonical proof](coverings/2k-minus-c-k-3/proof.md#8-attainment-a-known-witness-and-weighted-affine-planes)
and encoded in [Witness.lean](lean/CoveringDesigns/C20_11_3/Witness.lean)
is existing covering data. The recorded Covering Repository metadata credits
**Jan de Heer, 16 May 2005**, and names the Dan Gordon Covering Repository
as source. The project uses zero-based point labels and checks the witness
in Lean. This credit and date are repository metadata, not a claim about
first discovery or publication. The [source account](coverings/2k-minus-c-k-3/sources.md#constructions-and-point-links)
records the provenance and retrieval limitations.

The same source account attributes the established counting, selection,
rank and affine-construction methods used in those proofs. No additional
third-party paper or repository payload is needed for that account.

## The C(18,10,3) construction

The [twelve-block historical witness](data/c18103-historical-witness.json)
comes from the La Jolla Covering Repository data described above, under
CC BY 4.0 with attribution to Daniel M. Gordon / La Jolla Covering Repository.
Its retained source metadata records “JCD article” and 14 November 1996;
that incomplete credit does not identify the article or establish a discovery
date. The [source account](coverings/18-10-3/sources.md) explains the limitation.

The data retain the original one-based ordered blocks, source-archive hashes,
licence and catalogue metadata. Archive filenames and identifiers describe
that external source; they are not required local files.
[Witness.lean](lean/CoveringDesigns/C18_10_3/Witness.lean) subtracts one from
point labels and proves cardinality and complete coverage in Lean.
The new lower proof and standard lifted consequences are separate project
contributions credited in the result account.

## Quadruple-covering witnesses and seeds

The [eight-case account](coverings/12u-plus-1-4-3/README.md) retains the
13- and 25-point witnesses and relevant small designs from **Daniel M. Gordon /
La Jolla Covering Repository**, version 1.2, published 24 April 2026,
[Zenodo 19735294](https://zenodo.org/records/19735294), under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). The notices and
licence scope above apply to these data, including their Lean projections.
The [source account](coverings/12u-plus-1-4-3/sources.md) gives the
individual dependencies, historical qualifications and transformations:
one-based to zero-based labels, sorting, derivation/deletion, inflation,
substitution and explicit relabelling. The original 25-point compressed bytes
and copied attribution records are retained. Historical archive paths and IDs
in those records identify their source system, not extra local dependencies.

The six reconstructed larger witnesses and the formalisation are credited to
Rob Gardiner with the classical mathematical and seed-provider credits in that
account. The known optima and dated snapshot improvements are distinguished;
no source data are relabelled as wholly original project material.

## External software dependencies

Lean, Mathlib and the other packages pinned in
[lean/dependencies.json](lean/dependencies.json) retain their respective
upstream licences and notices. Their sources are installed separately by the
[dependency installer](scripts/setup_dependencies.py), which retains the
licence files in those archives. The project's MIT grant does not replace
those licences.

## The C(14,5,3) construction and deletion antecedent

The [43-block historical witness](data/c1453-historical-witness.json) is from
Daniel M. Gordon / La Jolla Coverings Repository, version 1.2,
[Zenodo 19735294](https://zenodo.org/records/19735294), under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
Its retained metadata credits **Nurmela and Östergård, simulated annealing**,
with repository date **1 December 1996**. The original ordered one-based
blocks are retained; the Lean witness subtracts one from each label and
proves cardinality and full triple coverage.

The [source account](coverings/14-5-3/sources.md) credits **Sharad S. Sane**
for the general projective failed-design theorem. The needed deletion lemma
is a self-contained reconstruction of its order-three special case.
The structural lower-bound argument and Lean formalisation are credited to
Rob Gardiner with AI assistance; the historical construction remains
separately attributed. No additional reference paper is reproduced.

## The C(34,18,3) historical construction and lifting corollaries

The [thirteen-block witness](data/c34183-historical-witness.json) comes from
**Daniel M. Gordon / La Jolla Coverings Repository**, version 1.2,
[Zenodo 19735294](https://zenodo.org/records/19735294), under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
The entry credits **LJCR; Multiple of (17,9,3) covering**, recorded on
**20 January 2009**. Its original ordered one-based labels are retained;
the Lean witness subtracts one from each label and independently proves
block distinctness, size and complete triple coverage. The
[source account](coverings/34-18-3/sources.md) identifies the artifact and hashes.
The historical construction is separate from this project's exactness
deduction and Lean connection to the earlier lower theorem.

The two new five-result chains apply the point-link argument in
**J. Schönheim, “On coverings,” Pacific Journal of Mathematics 14 (1964),
1405–1411**, proof of Theorem I, to this project's previously published
lower bounds at (14,5,3) and (34,18,3). Rob Gardiner, with AI assistance,
is credited for the explicit deductions and formalisation. The individual
accounts retain dated comparisons and unresolved historical priority.
No additional reference paper is reproduced.

## Pair-covering witnesses and comparison records

The pair accounts retain three La Jolla Covering Repository constructions:
**Colin Barker**, C(44,11,2)≤21 (1 December 2008);
**Flavio Perona**, C(65,13,2)≤31 (21 May 2011); and
**Jan de Heer and Steve Muir**, C(95,19,2)≤31 (16 March 2011).
Daniel M. Gordon's LJCR records and original compressed block lists retain
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).

The [Barker notice](data/pair-family/barker/NOTICES.txt) and
[Perona/de Heer–Muir notice](data/pair-family/extensions/NOTICES.txt)
accompany their original data and provenance. Label shifts into Lean are
checked separately; the constructions are not attributed to this project.
The 26 October LJCR snapshot and 27 October comparison inventory retain their
dated categories. Metadata projections replace private filesystem locators
with selected public files or explicitly historical identifiers; all numerical
observations, credits, dates and witness hashes are preserved.

Mathematical antecedents and the project's structural additions are distinguished
in the [pair source account](coverings/qk-k-2/sources.md). No reference PDFs or
third-party articles are distributed in this package.
