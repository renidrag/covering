# Sources and attribution

**Reconstruction and Lean formalisation: Rob Gardiner, with AI assistance.**
These exact values were proved in earlier work. This project supplies a
reusable assembly proof, checked seed instances and a checked connection to
its six constructed block lists, plus two checked small cases completing the
admissible range below 100. It claims neither new covering numbers nor globally first
published block lists.

## Historical result and project contribution

For every admissible \(n\equiv1\pmod{12}\), the equality
\(C(n,4,3)=n(n-1)^2/24\) is an established result. Schönheim's recurrence
supplies the lower bound; the attainment result is credited to
Mills (1974). Hartman–Mills–Mullin explicitly include this congruence class
in their abstract and report Mills's result on p. 118. The eight numerical
values therefore follow directly by substitution. Gordon–Stinson's
Theorem 1.27 provides a later confirmation.

The historical construction papers contain mathematical proofs and block
recipes. Hanani gives explicit ingredients and inflation formulas;
Hartman–Mills–Mullin describe block assembly and counting, leaving some
coverage checks to the reader. Our account supplies a separately proved
adaptation and complete concrete seeds, rather than treating those checks
or a catalogue entry as proof premises.

The project's contribution has three parts:

- Reconstruct six optimal labelled block lists at 37, 49, 61, 73, 85 and
  97 points from the shared assembly and checked seeds.
- Recover and verify the existing 13- and 25-point lists with their original
  attribution and data provenance.
- Formalise the assembly, all eight exactness results and the correspondence
  to those actual lists in Lean, with independent file-conversion checks.

The historical theorem covers the entire admissible congruence class.
The unconditional Lean theorem here covers its eight orders below 100;
the reusable general assembly retains explicit seed hypotheses. This is not
a literal formalisation of Mills's unread original or the whole HMM paper.
The six snapshot improvements concern retained construction lists, not
previously unknown covering numbers or an established first publication of
optimal lists.

## Mathematical sources

J. Schönheim, *On coverings*, Pacific Journal of Mathematics 14 (1964),
1405–1411, Theorem I, p. 1407.
[Journal PDF](https://msp.org/pjm/1964/14-4/pjm-v14-n4-p29-p.pdf).
The existing library formalises the iterated recurrence for ordinary coverings;
the present component retains all three intermediate ceilings.

A. Hartman, W. H. Mills and R. C. Mullin, *Covering triples by quadruples:
An asymptotic solution*, Journal of Combinatorial Theory, Series A 41 (1986),
117–138. [DOI 10.1016/0097-3165(86)90119-6](https://doi.org/10.1016/0097-3165(86)90119-6).
The H-design definition and Mills attribution are on p. 118. The assembly is
in the proof of Theorem 6, pp. 120–121; coordinate-sum inflation is Lemma 2.2,
p. 121; three-wise block substitution is Lemma 2.3, p. 122. The even-order
existence result is Theorem 2.4, p. 122.

**Theorem 6 itself has an odd-case domain.** The even-case assembly here is
proved directly from its finite inputs. Its validity is not obtained by
silently enlarging that theorem's domain. The lower-bound sharpness argument
used in Lean to obtain exact class sizes and disjointness is an implementation
adaptation; the support descriptions also give the direct combinatorial proof.

H. Hanani, *On some tactical configurations*, Canadian Journal of Mathematics
15 (1963), 702–722. [DOI 10.4153/CJM-1963-069-5](https://doi.org/10.4153/CJM-1963-069-5).
Definition 3 is on p. 703; inflation/doubling constructions appear in
Propositions 5–7, pp. 704–705. Lemma 3, equation (8), p. 709 supplies the
retained H(6,3,4,3) seed. The two-sextuple 12-point master used here is the
project's explicit one-factor reconstruction, not a claimed transcription
of Hanani's equation (3) or his full even-order induction.

W. H. Mills, *On the covering of triples by quadruples*, Congressus Numerantium
10 (1974), is credited for known attainment by the later sources.
**Mills's original was not inspected.** The preserved account records a
563–581 / 573–581 pagination discrepancy; this formalisation does not resolve
it or claim to reproduce the unread recipe.

L. Ji, *An improvement on covering triples by quadruples*, Journal of
Combinatorial Designs 16 (2008), 231–243; first published online in 2007.
[DOI 10.1002/jcd.20156](https://doi.org/10.1002/jcd.20156).
Its abstract explicitly attributes attainment outside the 7 modulo 12 class
to Mills; its reference list identifies his 1974 paper. This is corroborating
historical evidence, not an additional premise or construction used in Lean.
Only the abstract and references were inspected.

D. M. Gordon and D. R. Stinson, *Coverings*, handbook chapter,
[author-hosted PDF](https://dmgordon.org/papers/hcd.pdf), Theorem 1.19, p. 2
(Schönheim recurrence), and Theorem 1.27, p. 3 (known exact range), supply a
later confirmation. The mathematical lower bound in Lean uses the project's
existing Schönheim theorem, not a literature assumption.

The preserved pilot and seed assessment inspected the HMM and Hanani originals
and the Gordon–Stinson passages on **22 October 2026**. This formalisation
reuses their retained accounts and data; it makes no new retrieval claim.

## Seed data and reuse terms

Copied LJCR-derived data retain **Daniel M. Gordon / La Jolla Coverings
Repository** attribution: version 1.2, published 24 April 2026,
[Zenodo record 19735294](https://zenodo.org/records/19735294),
[DOI 10.5281/zenodo.19735294](https://doi.org/10.5281/zenodo.19735294),
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).

This includes the 78-block (13,4,3) filling, the recovered 600-block
(25,4,3) witness, SQS(10), SQS(14), and the
2-(25,4,1) master underlying the retained 4-GDD of type 3^8. Derived/deleted
small GDDs retain that provenance. Original one-based labels were shifted to
zero-based labels; rows were sorted, and the documented derivations,
deletions, inflations, substitutions and relabellings were applied. The Lean
projections and selector tables are further deterministic transformations.
Historical metadata saying “JCD article” does not identify the constructors
of those particular lists. These data are not relabelled as wholly original
project material.

Affine SQS(8) and SQS(16), the coordinate-sum ingredients, the K6 factors,
the affine 4-GDD route for five holes and the two-sextuple master retain the
recipe attribution in the seed account. Small retained intermediate designs
may be checked directly in Lean instead of formalising the history of their
acquisition. Their incidence obligations are still discharged in the kernel.
The unused Stanton alternative 25-point master and Sage software leads are
not dependencies of these six witnesses. No third-party program was copied.

## The two retained small witnesses

The thirteen-point result reuses the existing JSON filling and its existing
Lean literal family and validity/cardinality proofs. Its projection is not
regenerated into a second maintained construction. It already attained 78
in the archived catalogue.

On **22 October 2026**, the twenty-five-point data were recovered read-only
from CVKT's `catalogue/25/4/3.json` through its explicit artifact record,
not inferred from a recorded check. The construction artifact is
`artefact:7aacc415-956e-5ab7-8128-ede6fa83c35e`, retained from
`covers.json /C(25,4,3)` in LJCR's Zenodo 19735294 snapshot. The
[original artifact](../../data/quadruple-assembly/C-25-4-3.blocks.zst)
is the unchanged 1,448-byte zstd frame, with SHA256
`d85a3d73470ad85ee3bd2796e0f32107f2bf5b968482a8a924bf678ee5449381`.
Its 2,400 decoded uint8 bytes have SHA256
`3bbd515956e07c60d83292c0d516ecbecae7d91069910b32a34e270dff61cccf`.
They encode 600 four-entry rows in the original point/block order, with
one-based labels. Subtracting one, sorting each row and sorting all rows
gives the retained normalized JSON. The independent boundary checker
validates every step and the explicit covering independently.

Exact copies of the [catalogue](../../data/quadruple-assembly/provenance/catalogue-25-4-3.json),
[artifact](../../data/quadruple-assembly/provenance/artifact-25-4-3.json),
[source](../../data/quadruple-assembly/provenance/source-ljcr.json),
[reference](../../data/quadruple-assembly/provenance/reference-ljcr.json)
and [Gordon attribution](../../data/quadruple-assembly/provenance/contributor-gordon.json)
records preserve the chain. Their historical IDs and paths describe that
source system; verification in this project uses only the copied local data.
The catalogue's upper claim records 600 and an earlier check records full
coverage, but neither is a Lean premise. Its historical observation says
“JCD article”, dated 14 November 1996. This does not identify the constructor
of the particular list. We credit Daniel M. Gordon/LJCR as the retained
source and provider under CC BY 4.0 without inferring an individual
constructor. No source was reacquired over the network.

The two small values complete the finite range; they are not improvements
to their already attaining archived constructions. The eight-case exactness
theorem is a finite consolidation of known mathematics, not an infinite
seed-existence theorem or a new covering-number claim.

## Dated comparison with the preserved LJCR snapshot

The comparison supplied and retained for this reconstruction on
**22 October 2026** is:

| v | Snapshot construction | Reconstructed optimum |
| ---: | ---: | ---: |
| 37 | 2,001 | 1,998 |
| 49 | 4,708 | 4,704 |
| 61 | 9,155 | 9,150 |
| 73 | 15,774 | 15,768 |
| 85 | 24,997 | 24,990 |
| 97 | 37,256 | 37,248 |

The snapshot supplied larger constructions for these six orders, although
their exact values were already established in the literature. We have not
established why the snapshot lacked optimal block lists.

The source search on 22 October 2026 covered the papers and retained data
described above, author-hosted material, and SageMath documentation and
public source code. We recovered construction recipes and seed designs, but
did not locate complete optimal block lists for these six orders in the
sources inspected. The six lists distributed here were reconstructed from
those ingredients. The 13- and 25-point lists were already present in the
retained catalogue and were recovered unchanged apart from the documented
normalisation.

This comparison concerns the preserved snapshot; the search was not
exhaustive, and Mills's original paper remains uninspected. It does not
establish that optimal lists were unavailable elsewhere or that these are
their first publication.
