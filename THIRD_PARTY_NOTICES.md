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
rank and affine-construction methods used in the proofs. No additional
third-party paper or repository payload is included in this release.

## External software dependencies

Lean, Mathlib and the other packages pinned in
[lean/dependencies.json](lean/dependencies.json) retain their respective
upstream licences and notices. Their sources are installed separately by the
[dependency installer](scripts/setup_dependencies.py), which retains the
licence files in those archives. The project's MIT grant does not replace
those licences.
