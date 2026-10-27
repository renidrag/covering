# Projective points and hyperplanes

**Proof reconstruction and Lean formalisation: Rob Gardiner, with Codex assistance.**

This supporting excerpt contains the finite projective geometry used by the pair constructions. The selected modules are GeometricSum, Points and Geometry; the pair account proves the needed line-intersection and expansion results. Attribution: Gordon, Kuperberg and Patashnik, following Ray–Chaudhuri; formalisation by Rob Gardiner. Write G(q,n)=Σ_{i<n}q^i, with G(q,0)=0.

The inspected sources are [GKP HTML](https://arxiv.org/html/math/9502238#S3)
and [GKP PDF](https://arxiv.org/pdf/math/9502238), §III (PDF p. 2) and
bibliography (PDF p. 10). GKP attributes Theorem 2 to D. K. Ray–Chaudhuri,
“Combinatorial information retrieval systems for files”, *SIAM Journal on
Applied Mathematics* **16**(5), 973–992 (1968), specifically Corollary 1,
reference [25]. This account follows GKP and supplies the linear-algebra and
ceiling details. The Ray–Chaudhuri original was not obtained or read; this is
not claimed to be a literal formalisation of that original paper.

Over an arbitrary finite field F of size q, initially let V=Fin(m+1)→F.
Use Mathlib's `Projectivization F V`, the quotient of nonzero vectors by
nonzero scalar multiples. A projective point p has its canonical one-dimensional
`p.submodule`. For any subspace S define its point set by p.submodule≤S.
This gives representative-independent membership directly. Define a block
for a projective dual direction d by S=ker(d.rep). The dual direction type is
the existing `AffineConstructions.Direction F (m+1)`.

Reuse Mathlib `Projectivization.card_of_finrank`, `map`, `map_injective`,
`mk_rep`, `submodule_mk`, `finrank_submodule`, the nonzero-dual kernel-dimension
theorem and the proper-subspace annihilating-functional theorem already used
by `AffineConstructions.Geometry`. Mathlib's kernel/span duality can derive
proportionality without a new foundational theory. The existing
`AffineConstructions.exists_field` constructs GaloisField p r internally
from IsPrimePow q; no existence premise will be exposed in the endpoint.

## Geometry

For a nonzero vector x, its projective point belongs to S exactly when x∈S:
span{x}≤S iff x∈S. Consequently membership in ker(f) is f(x)=0. Rescaling
x by a nonzero scalar preserves this equation, as does rescaling f. Thus the
chosen representatives of both projective classes have no mathematical effect.

The inclusion S→V induces an injective projective map. Its image is exactly
the points p with p.submodule≤S: one direction follows by linearity, and for
the reverse take p.rep∈S, which is nonzero. This is an equivalence from ℙ F S
to the subtype of points in S. Hence its finite point set has size
G(q,finrank F S), including S=0. For V of dimension m+1, Mathlib's projective
cardinality theorem gives G(q,m+1). A nonzero functional has a kernel of
dimension m because its image is the one-dimensional field. Therefore every
block has size G(q,m).

The dual also has dimension m+1, so its projectivisation has G(q,m+1)
directions. This index count alone is insufficient. A subspace is recovered
from its projective point set: zero belongs automatically, and each nonzero
vector belongs iff its projective point does. Thus equal actual blocks imply
equal kernels. If nonzero f,g have the same kernel, g belongs to span{f}
(the singleton instance of Mathlib's intersection-of-kernels/span duality).
Therefore g=a f; nonzeroness forces a≠0. They determine the same dual
projective point. The block map is injective, and its finite image has exactly
G(q,m+1) distinct members. The image is an ordinary `Family`, not an occurrence
count; reuse Finset image/cardinality and the existing family definitions.

For any finite set T of at most m projective points, take its representative
image R. The span W of R has dimension at most |R|≤|T|≤m<m+1. A proper
subspace is annihilated by some nonzero functional f, so all of T belong to
the hyperplane defined by [f]. This uses no independence assumption. For
T=∅ the span is zero and the same strict dimension bound applies. Dependent
sets only make the dimension smaller. The family is therefore uniform and
covers every tested m-set (indeed every set of size at most m).

## Lean correspondence


| Module | Contracts |
|---|---|
| `GeometricSum` | `G` abbreviates unchanged `AffineSchoenheim.geom`; `index_le_geom`, `geom_le_succ`, `geom_add`, `bernoulli_nat` give the elementary estimates and decomposition. |
| `Points` | `LiesIn`, `mk_liesIn`, `liesIn_iff_rep`; `subspacePointsEquiv`, `points`, `mem_points`, `points_card`, `points_injective`; `Point`, `point_card`. General subspaces are allowed, including zero. |
| `Geometry` | `functional_mk_liesIn`, `rescale_incidence`, `kernel_mk_rep`, `dual_eq_of_kernel_eq`; `exists_annihilating_of_span_lt`, `exists_annihilating_direction`; `Direction`, `hyperplane`, `mem_hyperplane`, `hyperplane_mk`, `kernel_finrank`, `hyperplane_card`, `direction_card`, `hyperplane_injective`, `hyperplanes_cover`, `family`, `family_card`, `family_isCover`, `empty_covered`. |
