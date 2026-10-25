# Sources and contribution

This component implements a complete elementary argument reviewed on
25 October 2026. Mathematical account and formalisation: Rob Gardiner,
with AI assistance. Historical priority for the general parity estimate
and its 774 consequence is unresolved; formalisation is a separate contribution.

## Established geometric ingredients

Z. Füredi, *A projective plane is an outstanding 2-cover*, Discrete
Mathematics 74 (1989), 321–324,
[DOI](https://doi.org/10.1016/0012-365X(89)90143-X).
Theorem 2.1 states that a pair cover on q²+q+1 points with q²+q+2 blocks
of size q+1 contains a projective plane. This is an abstract plane, not an
assumed finite-field construction. The original statement and proof were read.

S. S. Sane, *On Affine and Projective Failed Designs*, JCMCC 9 (1991),
209–219, [original paper](https://combinatorialpress.com/article/jcmcc/Volume%2009/vol-009-paper%2025.pdf).
Theorem 3.1 and its five proof assertions, printed pp.210–212, give the
elementary regular/irregular-point deletion argument reconstructed in the
proof. The note on p.219 credits Füredi's earlier result. These pages were
visually inspected. The indexed proof treats coincident occurrences separately
and deletes an actual index, preserving all other input occurrences.

C. J. Colbourn, G. Kéri, P. P. Rivas Soriano and J.-C. Schlage-Puchta,
*Covering and Radius-Covering Arrays: Constructions and Classification*,
[author preprint, 3 March 2010](https://old.sztaki.hu/~keri/arrays/Colbourn_Keri_Rivas-Soriano_Schlage-Puchta.pdf),
Theorem 8.1 and proof, pp.23–24. The authors combine plane deletion with
residual-triple counting for covering arrays. They prove that any (q+2)-set
in an odd-order plane with q≥5 has at least two collinear triples, citing
Dembowski, *Finite Geometries*, §3.2.25(a), for unique oval completion.
The original 2010 proof was read; Dembowski's original was not retrieved.
Covering-array numerical bounds are not ordinary covering numbers.

## The earlier ordinary-covering consequence

Replacing h by 2 in the proof gives, for odd q≥5,

\[
C(n+1,q+2,3)\ge\min\left\{
\left\lceil\frac{(n+1)(n+2)}{q+2}\right\rceil,
n+\left\lceil\frac{N}{\binom{q+2}3-2}\right\rceil\right\}.
\]

Indeed every point has degree at least n. A degree n or n+1 link contains
n actual plane occurrences by exact pair counting or Füredi–Sane deletion.
Those occurrences cover none of its N noncollinear triples. Each remaining
block avoiding the root covers at most binom(q+2,3)−2 such triples by the
2010 lemma; a block containing the root covers at most binom(q+1,3), which
is no larger. Counting demand-occurrence pairs gives the second branch.
If no such low degree occurs, summing degrees gives the first branch.

The two branches are respectively (151,149), (381,375), (778,770) at
q=5,7,9. Thus published ingredients already imply 149 and 375. This does
not claim that the cited paper prints these ordinary covering numbers or
establish who first drew this consequence. At q=9 the present all-plane
parity estimate gives h=3 and improves this deduction to 774.

## Scope and comparison limits

Balister, Bollobás, Füredi and Thompson,
[*Minimal symmetric differences of lines in projective planes*](https://arxiv.org/abs/1303.4117),
and Ball and Csajbók,
[*On sets of points with few odd secants*](https://arxiv.org/abs/1711.10876),
provide stronger results in the Desarguesian setting PG(2,q). Those hypotheses
cannot be transferred to arbitrary point links without proof. This component
uses only its included parity and incidence arguments.

On 25 October 2026 a fresh retrieval of
[Gordon/LJCR data](https://raw.githubusercontent.com/dmgordo/LJCR/main/coverings/coverdata.json)
gave lower entries 143, 368 and 762 for the three applications. Requests to
the Covering Repository returned HTTP 403; its current entries were not
established. These are dated, source-specific comparisons, not world-best
or priority claims. The relevant original Mills–Mullin statement was not
obtained; the problematic secondary quotation in Horsley–Singh is not used.
These historical access limits do not affect the self-contained proof.
