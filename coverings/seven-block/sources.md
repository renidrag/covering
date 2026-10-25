# Sources and attribution

24 October 2026. Rob Gardiner, with AI assistance.

## Earlier results and this proof

The numerical family C(7a+4,3a+2,2)=7, a≥1, follows from Gordon and
Stinson, “Coverings,” *Handbook of Combinatorial Designs*, second edition,
pp.365–373, [Theorem 1.31(5)](https://dmgordon.org/papers/hcd.pdf).
Its conditions hold because 2<(7a+4)/(3a+2)<7/3 and 7k−3v=2.

For a≥2, the structural classification also follows from Zoltán Füredi,
“Covering pairs by q²+q+1 sets,” *Journal of Combinatorial Theory, Series A*
**54** (1990), 248–271,
[Theorem 2.5](https://doi.org/10.1016/0097-3165(90)90034-T).
The [author-hosted paper](https://users.renyi.hu/~furedi/PUBS3/furedi_084_covering_pairs_JCTA_1990.pdf)
states the theorem on p.250 and proves it in §8, pp.268–269.
At q=2, an intersecting hypergraph on seven vertices without a Fano plane
has fractional matching number at most 11/5. Weighting each dual support
by its number of actual points divided by 3a+2 gives a fractional matching
of total weight (7a+4)/(3a+2)>11/5. A Fano core is therefore forced;
the incidence equations recover the two forms. This is a deduction from
the published theorem, not evidence that the exact all-a classification
was previously printed.

The [proof here](proof.md) establishes the classification directly through
integer support slack and seven-position recognition. Its Lean proof does
not assume Füredi's theorem. The contribution here is this explicit proof
and formalisation; the classification is supporting mathematics for
[C(19,9,3)=17](../19-9-3/README.md), without a first-discovery claim.

## The a=1 case

R. G. Stanton, “Isomorphism classes of small covering designs with block
size five,” *Combinatorial Design Theory*, North-Holland (1987), 441–448,
is credited for the known (11,5,2) classification. His original chapter was
not obtained. The two classes are reproduced in Gordon, Patashnik, Petro
and Taylor, “Minimum (12,6,3) Covers,” *Ars Combinatoria* **40** (1995),
161–177, §3, Theorem 3.1 and the following remarks:
[author version](https://dmgordon.org/papers/c-12-6-3.pdf).
The a=1 adapter uses the included [Stanton reconstruction](../11-5-2/proof.md).
The a≥2 proof is independent of that adapter.

## Other sources and access limits

Mills, “Covering designs I: Coverings by a small number of subsets,”
*Ars Combinatoria* **8** (1979), 199–315, and Mills–Mullin, “Coverings
and packings,” *Contemporary Design Theory*, Wiley (1992), 371–399,
remain unread originals. No claim about their precise classification
scope follows from that access limitation.

Hall, Horsley and Stinson, “Bounds on data limits for all-to-all comparison
from combinatorial designs,” *Designs, Codes and Cryptography* **92**
(2024), 2863–2879,
[DOI 10.1007/s10623-024-01418-6](https://doi.org/10.1007/s10623-024-01418-6),
provides context for weighted duality and projective-plane recognition.
Its load-3/7 equality statement is not the finite-excess-two classification
used here, and is not a premise of the formal proof.
