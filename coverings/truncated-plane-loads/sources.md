# Sources and contribution

**26 October 2026. Rob Gardiner's project, prepared with Codex.**

## The argument formalised here

Rob Gardiner's project, with Codex assistance, developed the support,
common-coordinate and equal-load argument proved in [proof.md](proof.md).
It classifies positive real loads and proves the converse, integer
divisibility, actual-point expansion and a conditional adapter for existing
coverings. The support lemma counts the q core members through a coordinate;
the group and core counts then determine all weights.

The source assessment of 26 October 2026 found no complete statement of
these positive multiplicity forms in the inspected sources. Historical
first-publication priority remains unresolved. The earlier geometric
classification and replication methods have the following roles.

## Historical ingredients and their role

* Zoltán Füredi, *Covering pairs by q²+q+1 sets*, Journal of Combinatorial
  Theory, Series A **54** (1990), 248–271, DOI
  [10.1016/0097-3165(90)90034-T](https://doi.org/10.1016/0097-3165(90)90034-T),
  Theorem 2.2, pp.249–250, and §§3,6–7.
  Its fractional geometric classification supplies a contained truncated
  plane or another geometric alternative in the broader application.
  Its generalised-cover reduction does not by itself evaluate the
  positive truncated-core loads classified here.
* Jürgen Bierbrauer, Stefano Marcugini and Fernanda Pambianco,
  *Projective planes, coverings and a network problem*, Designs, Codes and
  Cryptography **29** (2003), 71–89, DOI
  [10.1023/A:1024140122167](https://doi.org/10.1023/A:1024140122167).
  The inspected author manuscript provides weighted replication constructions,
  geometric reductions and the separate twisted-plane double count.
* Joanne Hall, Daniel Horsley and Douglas R. Stinson, *Bounds on data limits
  for all-to-all comparison from combinatorial designs*, Designs, Codes and
  Cryptography **92** (2024), 2863–2879, DOI
  [10.1007/s10623-024-01418-6](https://doi.org/10.1007/s10623-024-01418-6),
  Theorem 4.7 and Lemmas 4.8–4.9. The inspected final version explicitly
  provides a subset whose dual is affine, consistent with a contained core.

These historical results motivate the supplied-core hypothesis. None is
imported as an unproved assertion into this component. Weighted replication
and elementary point-degree counting are established methods; the project
contribution is the compatible extension and load classification and its
formal implementation. Numerical applications are proved in the
[C(4k,k,2) account](../4k-k-2/proof.md) and its
[further consequences](../qk-k-2/proof.md).

## Version qualification and the finite control

The inspected BMP source is a 24-page author manuscript, not the
19-page final journal typesetting. Its Corollary 1 promotes a contained
core to whole-family plane containment. The positive extended example
has a two-coordinate intersection and contradicts that author-version
clause. The final 2003 article was not obtained, so this is not described
as a correction to its unseen wording. Checking that final version remains
the principal source question for historical attribution; it is independent
of the self-contained proof here.

The concrete q=4 example uses the standard order-four affine geometry.
Its [Lean definition](../../lean/CoveringDesigns/TruncatedPlaneLoads/Examples.lean)
checks the truncated incidence axioms directly and proves expansion through
the general theorem. It supplies the extended form with t=2 and s=1,
including a core/extra intersection of size two. No external certificate
supplies the proof. Independent data checks establish correspondence with the original
finite control; the mathematical claims are proved in Lean.
