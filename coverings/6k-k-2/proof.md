# Lower bounds for C(6k,k,2)

**Proof reconstruction and Lean formalisation: Rob Gardiner, with Codex assistance.**

## Abstract and conventions

We prove **C(6k,k,2)≥43 for every k≥6**, including the same lower bound
for indexed families with repeated blocks. A hypothetical 42-block cover
would give a truncated plane or a twisted plane of order 6. A determinant
calculation excludes the twisted case. Completing the truncated plane gives
an integer incidence matrix whose reduction modulo 3 would have rank at
most 21 and at least 22. This contradiction proves the bound. The
[numerical table](numerical.md) gives two pair bounds and twelve lifts.

An indexed family is a map B from a finite occurrence set I to the
k-element subsets of a finite point set X. Pair coverage means every
two-element subset of X lies in B(i) for some i. Occurrences, rather than
distinct images, are counted. An ordinary family is a set of distinct
blocks. The covering number C(v,k,t) is its minimum size when every
t-subset of a v-point set must be covered.

**Theorem 1.** If k≥6, |X|=6k and B is an indexed pair covering by
k-element blocks, then |I|≥43. Consequently C(6k,k,2)≥43 for all k≥6.

All vector spaces below are finite-dimensional. Vectors are columns;
x·y means the bilinear dot product Σ xᵢyᵢ, without conjugation.
Total isotropy means x·y=0 for every pair of vectors in the subspace,
including equal vectors. J denotes the appropriately indexed all-ones
matrix, and I in matrix expressions denotes the identity. No matrix in
the algebraic obstruction is assumed to have binary entries.

## 1. The discriminant obstruction

**Lemma 2 (standard-dot dimension bound).** Over any field, a totally
isotropic subspace U of Kⁿ has 2 dim U≤n.

Choose a basis of U as the rows of a matrix N. Its rows are independent,
so rank N=dim U, and isotropy gives NNᵀ=0. Thus im Nᵀ lies in ker N.
Rank-nullity and equality of row and column ranks give
2 rank N=rank N+rank Nᵀ≤n. This argument uses no order on K.

**Lemma 3 (fixed discriminant).** Let F=F₃ and E=F⁴². A symmetric
42×42 matrix G over F with det G=1 has no 21-dimensional subspace U
such that xᵀGy=0 for all x,y∈U.

Choose a basis of U. Rank-nullity for the quotient gives dim(E/U)=21.
Choose a quotient basis and representatives in E. Together with the basis
of U these representatives form a basis of E: spanning follows by first
matching the quotient, and independence by first passing a relation to the
quotient. Its Gram matrix has the form

\[
T=\begin{pmatrix}0&B\\B^{\mathsf T}&D\end{pmatrix},
\]

where all blocks are 21×21. The zero block follows from isotropy, and
symmetry gives the lower-left block. If C is the change-of-basis matrix
from the coordinate basis, then T=CᵀGC. Since det C≠0 and every nonzero
square in F₃ is 1, det T=(det C)² det G=1.

Let S exchange the two blocks of rows. Its determinant is (−1)²¹=−1.
One direct determinant calculation uses

\[
S=\begin{pmatrix}I&I\\I&0\end{pmatrix}
  \begin{pmatrix}I&0\\-I&I\end{pmatrix}.
\]

The factors have determinants (−1)²¹ and 1 by the block determinant
formulas with an identity or triangular block. But
ST=[[Bᵀ,D],[0,B]], so det T=−(det B)². A square in F₃ is 0 or 1,
whose negatives are never 1. This contradicts det T=1. The calculation
does not require B to be invertible.

**Lemma 4 (sum-zero bound).** A totally isotropic subspace U of F₃⁴³
whose vectors have coordinate sum zero has dimension at most 20.

Lemma 2 first gives dim U≤21. The sum-zero space V has the explicit
coordinate isomorphism

\[
z\longmapsto (z_1,\ldots,z_{42},-\sum_{i=1}^{42}z_i).
\]

Its inverse forgets the last coordinate; the sum-zero equation proves
the inverse identity. The transported dot product has Gram matrix
H=I₄₂+J₄₂, because its value on z,w is z·w+(Σz)(Σw).
The rank-one determinant identity det(I+uvᵀ)=1+vᵀu gives
det H=1+42=1 in F₃. If dim U=21, its inverse image in this chart
contradicts Lemma 3. For any other 43-element coordinate set, a bijection
with the displayed coordinates transports the subspace, sums and pairings.

## 2. Integer lifts and the modular kernel

**Lemma 5 (prime-kernel isotropy).** Let S,T be finite sets, p a prime
natural number, a an integer with p∤a, and B an integer matrix with rows S
and columns T. If BᵀB=pa I+J, then ker(B mod p) is totally isotropic for
the standard dot product over Fₚ.

If T is empty, the conclusion is the empty sum. Otherwise let M=B mod p
and take x,y∈ker M. Reduction of the integer identity gives MᵀM=J.
Thus Jx=Jy=0. Reading any coordinate shows Σx=Σy=0.

Choose coordinatewise integer lifts X,Y. Reduction commutes with sums
and products, so every coordinate of BX and BY, and both ΣX and ΣY,
is divisible by p. Over the integers,

\[
(BX)\cdot(BY)=X^{\mathsf T}B^{\mathsf T}BY
=pa(X\cdot Y)+(\sum X)(\sum Y).
\]

The left side is a sum of products each divisible by p². The final term
is also divisible by p². Subtracting gives p²∣pa(X·Y). Since p≠0,
cancel one factor p; primality and p∤a then give p∣X·Y. Reduction gives
x·y=0. No additive property of the chosen lifting function is used.
The proof permits an empty row set, rectangular shapes, negative a and
arbitrary integer entries.

## 3. The rank contradiction

**Proposition 6.** There is no integer matrix A on finite line and point
sets L,T, each of cardinality 43, satisfying all three identities

\[
\sum_t A_{lt}=7\quad(l\in L),\qquad
AA^{\mathsf T}=6I_L+J_L,\qquad A^{\mathsf T}A=6I_T+J_T.
\]

Reduce A modulo 3 to obtain M, and let R be its row space, of dimension r. Write
σ for coordinate sum. Every row has sum 1, and MMᵀ=J means every two
rows have dot product 1. Identify their transposes with coordinate vectors:
arbitrary row combinations xᵀ=cᵀM and yᵀ=dᵀM satisfy

\[
\sigma(x)=\sum c,\qquad x\cdot y=(\sum c)(\sum d)
=\sigma(x)\sigma(y).                                      \tag{1}
\]

Let W={x∈R:σ(x)=0}. The map σ:R→F₃ is surjective because one row
has sum 1, and its scalar multiples have every possible sum. Rank-nullity
gives dim W+1=dim R=r. Equation (1) makes W totally isotropic. Its
vectors also have coordinate sum zero, so Lemma 4 gives dim W≤20 and
hence r≤21.

Apply Lemma 5 to A with p=3,a=2, using the **column** Gram identity.
The kernel K of the same M is totally isotropic. Lemma 2 gives
2 dim K≤43, so dim K≤21. Rank-nullity for M gives r+dim K=43,
and therefore r≥22, a contradiction. The row Gram identity and column
Gram identity have different roles; neither is obtained by simply
transposing the other. No equality between the rank of a matrix and
the rank of its Gram matrix over F₃ is used.

## 4. Completion of the actual truncated core

**Proposition 7.** A truncated projective plane of order 6 does not exist.

Suppose P is such a core on a finite coordinate set I, partitioned into
seven groups of six. Its core supports have size seven, meet each group
once, and distinct supports intersect once. There are 36 supports. Each
coordinate lies in six core supports; two distinct coordinates have
core codegree zero in the same group and one in different groups.
The size and cardinality statements follow from the supplied fields by
the incidence counts in the included [truncated-plane account](../truncated-plane-loads/proof.md).

Adjoin a new point ∞ to the original 42 coordinates. Keep every original
core support as a line, and add each of the seven groups together with ∞.
These definitions preserve the original coordinates and support subsets.
There are 43 point labels and 43 line labels, and every line has size seven.

Distinct core lines intersect once by the core intersection field. A core
line meets a group line once by transversality. Two different group lines
meet just at ∞ because their original fibres are disjoint. Therefore every
two distinct line labels have intersection size one. They cannot represent
the same seven-element subset, so the 43 lines are distinct.

The point counts follow independently:

| Points | Core contribution | Group-line contribution | Total |
|---|---:|---:|---:|
| ∞, degree | 0 | 7 | 7 |
| Original x, degree | 6 | 1 | 7 |
| ∞ and original x, codegree | 0 | 1 | 1 |
| Distinct originals in the same group | 0 | 1 | 1 |
| Originals in different groups | 1 | 0 | 1 |

Let A(l,x) be the integer indicator of membership in these actual lines.
Line size gives row sums seven. Line intersections give AAᵀ=6I+J:
the diagonal is seven and every off-diagonal entry is one. The separate
degree and codegree counts give AᵀA=6I+J with the same entries on the
point indices. Proposition 6 now contradicts the existence of P.

## 5. Covering deduction and numerical consequences

By [Lemma 2 of the pair-divisibility proof](../4k-k-2/proof.md#2-from-actual-coverings-to-geometric-equality),
a cover in Theorem 1 has |I|≥42. At equality, every point lies in seven
occurrences. Its support is the set of those occurrence indices. Distinct
supports intersect, and the number of points with each support, divided by
k, gives positive weights of load 1 at each coordinate.

[Füredi’s equality classification](../pair-equality/proof.md) therefore
gives a truncated core or a twisted plane of order 6 on the same
coordinates. Proposition 7 excludes the core. For the twisted case,
[Proposition 2 of the determinant argument](../qk-k-2/proof.md#2-determinants-and-the-remaining-lower-bounds)
gives an integer incidence matrix D satisfying

\[
(\det D)^2=5^{21}7^{22}.
\]

The exponent of the prime 5 is odd, so the right side cannot be an integer
square. This excludes the twisted case as well. Thus equality at 42 is
impossible and |I|≥43. An ordinary family can be indexed by its own
blocks, proving C(6k,k,2)≥43.

Taking k=6 and k=12 gives C(36,6,2)≥43 and C(72,12,2)≥43. For either
seed, apply the included universal [Schönheim lifting theorem](../lifting-comparison/proof.md)
repeatedly: from a universal bound b at (v−1,k−1,t−1), the next bound is
⌈vb/k⌉ at (v,k,t). The universality is supplied by Theorem 1 on every
finite point and occurrence type. Repeating six times gives the twelve
positive-step rows in the [numerical table](numerical.md), with every
intermediate ceiling retained. Ordinary adapters follow as above. No
attaining construction or exactness conclusion follows from these bounds.

## Sources and contribution

R. H. Bruck and H. J. Ryser, *The nonexistence of certain finite projective
planes*, Canadian Journal of Mathematics **1** (1949), 88–93,
[Theorem 1](https://doi.org/10.4153/CJM-1949-009-2), is the historical
source of order-six nonexistence.
The present formalisation supplies the specialised discriminant and
integer-lift route above; it does not formalise the full Bruck–Ryser theorem
or assert that this route reproduces their original proof.

The equality classification is due to Zoltán Füredi, *Covering pairs by
q²+q+1 sets*, Journal of Combinatorial Theory, Series A **54** (1990),
248–271, Theorem 2.2 and §7. Its [included proof and source discussion](../pair-equality/proof.md#sources-and-proof-provenance)
retain the distinct roles and limitations of the Bierbrauer–Marcugini–Pambianco
manuscript and Hall–Horsley–Stinson comparison. The twisted determinant
and mate-incidence methods retain their historical credit. The lifting is
Schönheim's classical recurrence, already formalised in the library.

The contribution here is Rob Gardiner’s formalisation and assembly of these
ingredients, with Codex. The [numerical table](numerical.md) records nine
improvements over the 26/27 October 2026 LJCR snapshot, two further
improvements over retained cvkt claims, and three bounds without comparison
entries. These dated comparisons do not determine historical priority of
the covering corollaries.

## Appendix A. Lean correspondence

Unless qualified otherwise, declarations and import suffixes below are
relative to `CoveringDesigns.C6k_K_2`. The twisted exclusion belongs to
`CoveringDesigns.PairConsequences`. Helpers for lifts, block determinants
and the sum-zero chart are private.

| Mathematical statement | Import suffix | Declaration |
|---|---|---|
| Theorem 1, indexed occurrences | `.LowerBound` | `indexed_lower_bound` |
| Theorem 1, ordinary families | `.LowerBound` | `lower_bound` |
| Lemma 2, any field and finite coordinate type | `.Isotropic` | `isotropic_finrank_le` |
| Lemma 3, arbitrary U and symmetric G on Fin 42 | `.Discriminant` | `no_isotropic_half` |
| Lemma 4, any 43-element coordinate type | `.Isotropic` | `sum_zero_isotropic_finrank_le` |
| Coordinate-sum linear map used in both transports | `.Isotropic` | `coordinateSum` |
| Lemma 5, finite rectangular integer matrices, prime p, p∤a | `.PrimeKernel` | `kernel_totally_isotropic` |
| Proposition 6, native finite line and point types | `.Matrix` | `no_order_six_matrix` |
| Actual line map and integer matrix | `.Completion` | `completedLine`, `completedIncidence` |
| Completion cardinalities, size and distinctness | `.Completion` | `completed_points_card`, `completed_lines_card`, `completed_line_size`, `completed_lines_injective` |
| Intersections, degrees and codegrees | `.Completion` | `completed_intersection`, `completed_degree`, `completed_codegree` |
| Row sums and both Gram identities | `.Completion` | `completed_row_sum`, `completed_row_gram`, `completed_column_gram` |
| Proposition 7, only the actual Plane premise | `.LowerBound` | `no_plane_six` |
| Order-six twisted exclusion in §5 | `CoveringDesigns.PairConsequences.Arithmetic` | `PairConsequences.no_twisted_six` |
| Fourteen rows, ordinary and indexed | `.Numerical` | `lower_bound_v_k_t`, `indexed_lower_v_k_t` for each row |

The general indexed contract has finite decidable-equality types I,X,
k≥6, `Fintype.card X=6*k`, and `Multicover.IsCover B k 2 1`.
The latter is exactly occurrence uniformity plus pair coverage. It does not
require injectivity of B. The ordinary contract needs only a finite X,
k≥6, its cardinality and `IsCover C k 2`. Decidable equality is an
implementation instance, not an extra mathematical hypothesis. The
explicit audit restatements expand both covering predicates.

The discriminant contract quantifies over every submodule U and symmetric
G with determinant one, assumes only finrank U=21 and pairwise G-isotropy,
and concludes False. `Basis.sumQuot` constructs the full basis from a
submodule basis and a quotient basis; neither basis is a premise.
The prime-kernel contract has independent finite row and column types,
arbitrary integer entries and exactly p∤a; it includes empty index types.
The matrix obstruction assumes both Gram identities and row sums, and
the completion derives all of them rather than leaving geometric premises.

The [component audit](../../lean/audits/C6k_K_2.lean) checks every public
declaration's full type and transitive axioms. The allowed foundations are
exactly `propext`, `Classical.choice`, and `Quot.sound`; auxiliary declarations
may use a subset. There are no admissions, new axioms, native proof assertions
or external certificates. The public modules import no research scripts.
The numerical checker validates inventory correspondence and deterministic
text; Lean proves the bounds and the ceiling evaluations.

The completion module is independent of the obstruction, and all established
components remain independent of the new modules. The earlier
`PairConsequences.indexed_six` and `lower_bound_six` retain their 6∤k
premises. The theorem in this account removes that restriction. The
[shared verification guide](../../technical-details.md) distinguishes source
checks, Lean compilation, theorem/axiom audits and subsequent record validation.
