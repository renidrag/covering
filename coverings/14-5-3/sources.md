# Sources, provenance and historical scope

**Rob Gardiner's covering-design project, with AI assistance.** The structural
reconstruction, independent AI review, simplification, documentation and Lean
formalisation are credited in that sense. An independent AI review is not
human peer review. Historical authors retain credit for their results and
construction; no numerical first-discovery claim is made here.

## Historical upper construction

The 43-block witness is credited to **Nurmela and Östergård, simulated
annealing**, with repository date **1 December 1996**. Its preserved ordered
blocks and source metadata are in
[`data/c1453-historical-witness.json`](../../data/c1453-historical-witness.json).
Original labels 1–14 are shifted by one in the Lean witness. The original
215 label bytes have SHA-256
`173772ab8d73847ff258f4f5ae2859d0fbe7e312483e1afc23d58c721bd22f93`.
This timestamp belongs to the construction record; it is not evidence of
optimality or a date of first proof of the lower bound.

The source archive is **Daniel M. Gordon, La Jolla Coverings Repository,
version 1.2**, published 24 April 2026,
[Zenodo record 19735294](https://zenodo.org/records/19735294).
Its [licence file](https://zenodo.org/records/19735294/files/LICENSE?download=1)
provides **Creative Commons Attribution 4.0 International**, crediting
Daniel M. Gordon. The archive and its local indexed reader were inspected
read-only. The public result depends on the retained blocks and the kernel
proof of their properties, not on access to that local reader or archive.

The Covering Repository's [search form](https://www.coveringrepository.com/systems.aspx)
was inspected on 21 October 2026 for V=14, K=5, T=M=3 and displayed 37–43
with that construction credit. This is dated source evidence, not a claim
that an unchanged table proves novelty. Gordon's
[errata](https://dmgordon.org/errata/) explicitly withdraw the mistaken
optimality star attached to the older 47-block (14,5,3) construction.
Neither that star nor the older construction establishes exactness here.

## Known deletion antecedent

**Sharad S. Sane, “On Affine and Projective Failed Designs,” Journal of
Combinatorial Mathematics and Combinatorial Computing 9 (1991), 209–219.**
The [publisher's abstract](https://combinatorialpress.com/jcmcc-articles/volume-009/on-affine-and-projective-failed-designs/)
defines a projective failed design as a pair cover with parameters
(q²+q+1,q+1,q²+q+2 occurrences) having no block deletable to a projective
plane, and states that these configurations never exist. At q=3 this is
the known antecedent of the needed fourteen-block deletion lemma.

The abstract and indexed introduction were inspected. The full scanned
general proof was not successfully obtained. The proof in this account is
a self-contained special-case reconstruction; it does not claim to reproduce
Sane's proof or establish his arbitrary-order theorem. It explicitly permits
repeated occurrence images and proves existence of the removable four-set
as an actual block occurrence. Sane's statement is attribution, not an
unformalised premise of the Lean proof.

**Zoltán Füredi, “A projective plane is an outstanding 2-cover,” Discrete
Mathematics 74 (1989), 321–324**, [DOI](https://doi.org/10.1016/0012-365X(89)90143-X),
is closely related earlier work. Its accessible abstract concerns a two-block
gap when the corresponding projective plane does not exist. That hypothesis
does not hold at order three. The full original proof was not obtained;
no stronger deletion or parent-cover conclusion is attributed to it here.

## Other inspected sources and limits

The bounded assessment on 21 October 2026 inspected the following sources.
The present formalisation rechecked Sane's publisher statement, the Zenodo
record and licence, and Gordon's errata; it did not undertake a new general
priority search.

- **Gordon and Stinson, “Coverings,” Handbook of Combinatorial Designs**,
  [chapter](https://www.dmgordon.org/papers/hcd.pdf), Theorems 1.19 and 1.25:
  Schönheim's bound gives 37 for this parameter and the exact pair-cover
  value is C(13,4,2)=13. The chapter also lists the upper bound 43. The
  formal proof derives its own equality-link properties from incidence.
- **Dai, Li and Toulouse**, [covering-design paper, Table 2](https://w1.cirrelt.ca/~toulouse/CD-BL-MT.pdf):
  the displayed row has lower 37 and upper 43; its 42-block trial has
  nonzero cost three. It is neither a covering witness nor an exclusion.
- **Chee and Ling, “Projective Covering Designs”**,
  [paper](https://ymchee66.github.io/home/PDF/projectivecov.pdf): related
  pair-cover constructions and excess congruences, without the complete
  noncollinear triple-completion argument used here.
- **Tamás Szőnyi, design lecture notes**,
  [Proposition 4.16 and Corollary 4.17](https://szonyitamas.web.elte.hu/bldesign.pdf):
  exact extension divisibility. Their exact-triple hypothesis cannot be
  imposed on a cover with excess; the present pair identity keeps all
  excess terms at their actual locations.
- **Daniel Horsley and Rakhi Singh, “New lower bounds for t-coverings”**,
  [arXiv:1706.06825v2](https://arxiv.org/html/1706.06825v2), equation (3):
  a displayed quotation of Mills–Mullin, read literally at this parameter,
  would give 45, contradicting the checked 43-block witness. That quotation
  is not used. This observation does not refute the unread original
  Mills–Mullin theorem or establish what its full hypotheses were.

The inspected sources did not establish an earlier complete implication of
40 or 41. The missing original proofs and bounded search prevent a definitive
priority assessment. The self-contained structural proof and kernel-checked
contracts do not depend on settling that historical question. The interval
41–43 is the result formalised here; excluding 41 or 42, producing a new
construction and generalising to arbitrary prime powers are outside it.
