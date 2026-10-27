# Affine coverings and point transformations

**Proof reconstruction and Lean formalisation: Rob Gardiner, with Codex assistance.**

This supporting account includes the affine construction, expansion and point reduction used by the pair-covering results. The mathematical argument and correspondence below are retained from the complete source account.

## Scope and contracts (saved before Lean implementation)

Source: Daniel Horsley and Rakhi Singh, *New lower bounds for t-coverings*,
[arXiv:1706.06825v2, §4](https://arxiv.org/html/1706.06825v2#S4), the affine
geometry paragraph and Lemma 8. The version is the revision dated 4 October
2017, checked on 16 October 2026. The HTML gives an unambiguous statement and
argument for this lemma. The geometric prerequisite is described as classical
in the paper; the details below supply its proof rather than treating it as
an assumption. The theorem and construction are not new. Rob Gardiner is
credited for this project's formalisation.

For a prime power q and positive naturals m,t, set

    k = m*q^(t-1),    H = q*((q^t-1)/(q-1)).

The principal contract is: for every finite point type α of cardinality v,
if k≤v≤m*q^t, there exists C : Family α such that IsCover C k t and
C.card≤H. In particular every member of C has exactly k points and every
t-element subset of α is contained in a member of C. Blocks are distinct
finite sets. The explicit lower restriction k≤v states the usual valid
parameter range, implicit in the source's covering-number notation. The
boundary v=k is included. We derive t≤k rather than assume it. No field,
affine covering or construction witness is an input to this theorem.

Independent reusable contracts are:

1. **Coverage of smaller subsets.** If Covers C t and t≤|α|, every subset
   of α of size at most t is contained in a block.
2. **Blow-up.** From IsCover C k t on α and t≤|α|, construct a family on
   α×M with IsCover at block size k*|M| and strength t, of size at most
   C.card. In its intended use |M|>0. The transformation may also support
   empty M where its hypotheses and conclusion permit it.
3. **Point reduction.** If IsCover C k t, |β|≤|α| and k≤|β|, construct a
   family on β with the same k,t and no more blocks. This implies the
   standard monotonicity for t≤k≤v'≤v, and may hold under fewer assumptions.
   Relabelling across equal finite cardinalities uses the existing theorem.
4. **Affine prerequisite.** For a finite field F and positive t, construct
   a family on Fin t → F of block size |F|^(t-1), strength t and size at most
   |F|*((|F|^t-1)/(|F|-1)). Its point count is |F|^t.

## Structural argument

### Affine hyperplanes and their count

Put V=F^t. A nonzero linear functional ℓ:V→F is surjective, so each fibre
ℓ⁻¹(c) is a translate of ker ℓ. Rank–nullity gives dim ker ℓ=t−1 and hence
every fibre has q^(t−1) points. We use the projective space of the dual V*
to index directions, with one classically chosen nonzero representative
per direction. An index is a direction together with c∈F. Mathlib's
projective cardinality theorem counts directions as (q^t−1)/(q−1): each
direction contains exactly q−1 nonzero scalar multiples. It also gives
the exact identity q^t−1=number_of_directions*(q−1), proving divisibility.
Here q≥2, so the denominator is positive. This quotient-space presentation
replaces explicit normalisation of the first nonzero coordinate; it proves
the same structural count without enumeration.

To cover a t-element set T, choose p∈T (t>0). The differences x−p for
x∈T\{p} span a subspace of dimension at most t−1, strictly below dim V=t.
A nonzero linear functional annihilates this proper subspace. It has a
constant value on T. The chosen representative of its projective direction
is a nonzero scalar multiple, so it too has a constant value on T. Thus T
lies in one of our fibres. Taking the image of all indices produces an
ordinary Family. Its cardinality is at most the number of indices; no
unproved identification of indices with distinct blocks is used.

### Blow-up and reduction

For blow-up replace each A by A×M. Sizes multiply. The projection to α
of a t-element set in α×M has at most t points. Extend that projection to
t points using t≤|α|, cover it in α, and lift the containing block. The
image family has at most as many distinct blocks as the original family.

For reduction embed β into α. Pull each original block back to β. Its
size is at most k, so extend it to a k-element subset of β, possible since
k≤|β|. Choose such an extension for each original block. If T⊆β has
t points, its injective image in α has t points, lies in an original
block, and therefore T lies in the corresponding extended pullback.
Again an image family cannot increase the block count, even if several
extensions coincide. This is the source's point-deletion monotonicity,
proved directly for any reduction in cardinality.

### Prime powers and assembly

Write q=p^r with p prime and r>0. Mathlib's GaloisField p r is a field
with exactly q elements, discharging existence for nonprime prime powers
as well. Apply the affine construction, blow up with Fin m, and reduce
to Fin v. Relabel to the requested arbitrary finite point type.
Since q≥2, induction gives t≤q^(t−1) for t≥1; multiplying by m≥1 gives
t≤k. The product point count is m*q^t. All quotients are natural and
their divisibility and positive denominators are proved.

Classical choice is used for representatives, finite-field instances,
padding subsets and relabellings. The proof is existential, not an
algorithm enumerating hyperplanes or covering configurations. All these
choices and cardinality arguments are kernel checked.

## Fixed checks and boundaries

The general theorem supplies arbitrary-type witnesses for (v,k,t;H):
(9,3,2;12), (16,4,2;20), (8,4,3;14), (17,6,2;12).
They use respectively (q,m,t)=(3,1,2),(4,1,2),(2,1,3),(3,2,2).
The second checks a nonprime prime power; the fourth uses both transformations.
Additional contracts check t=1, m=1, v=k and v=m*q^t. These are upper
construction bounds, with no claim of exact covering numbers or novelty.

## Source-to-Lean correspondence

All project declarations below are in `CoveringDesigns.AffineConstructions`,
with calibration declarations in its `Examples` namespace.

| Source claim or prerequisite | Exact scope and Lean declarations | Reuse or adaptation |
| --- | --- | --- |
| A small affine point set lies in a hyperplane | `exists_constant_functional`: any nonempty finite set of at most dim V points, over any field and finite-dimensional V | Difference span and Mathlib's annihilating dual functional; supplied detail for the classical geometry paragraph |
| Affine hyperplanes have q^(t−1) points | `functional_fiber_card`, `hyperplane_card` | Translation to the kernel, rank–nullity and finite-vector-space cardinality |
| AG(t,q) has q^t points | `affine_points_card` | Cardinality of a finite function type |
| Hyperplane directions and indices | `direction_card`, `direction_count_exact`, `hyperplane_indices_card` | Mathlib `Projectivization.card''`, applied to the dual; projective representatives replace geometric flats or coordinate normalisation |
| Classical affine covering | `hyperplanes_cover`, `affine_cover` | Image of all direction/constant indices; only an upper bound on distinct blocks is needed |
| Image families may merge blocks | `exists_family_of_blocks` | Generic finite-image cardinality inequality, independent of geometry |
| Blow-up in Lemma 8 | `covers_subset_of_card_le`, `blow_up` | Explicitly extends the projection to t points; permits any finite fibre, including empty fibres where the conclusion remains valid |
| Point-deletion monotonicity | `reduce_points` | Direct reduction by an embedding and padding; needs only k≤|β|≤|α|, and hence covers the standard t≤k range |
| Relabelling | `exists_cover_of_card_eq` | Reuses unchanged `relabel_isCover` and `relabel_card` from `Foundations.Relabelling` |
| Prime-power field existence | `exists_field` | Mathlib `GaloisField p r`, `GaloisField.card`; p prime, r>0, including q=4 |
| Exact quotient and parameter validity | `denominator_pos`, `quotient_exact`, `quotient_eq_sum`, `strength_le_block_size`, `block_size_le_points` | Natural divisibility from the geometric series, q≥2 and exact inequalities |
| Lemma 8 | `lemma8_fin`, `lemma8` | All prime powers, positive m,t and k≤v≤m*q^t; no field or covering witness among the inputs |
| Fixed checks and interval boundaries | `Examples.upper_bound_9_3_2`, `upper_bound_16_4_2`, `upper_bound_8_4_3`, `upper_bound_17_6_2`, `strength_one`, `no_blow_up`, `lower_endpoint`, `upper_endpoint`, `duplicate_blocks_collapse` | Existential witnesses from the general theorem, plus a structural image-duplication check |

The final theorem uses the source's positive m,t. The transformation proofs
are slightly more general: no positivity of the fibre is needed for the
blow-up proposition, and point reduction does not need t≤k. These stronger
helper contracts do not enlarge or restrict the stated Lemma 8 contract.
No assumption about a finite field remains in `lemma8`: its field witness
is obtained from the prime-power hypothesis. The numerical examples call
this theorem rather than supplying independent finite configurations.

The geometry file imports the general transformations and Mathlib's
projectivization, dual-space and finite-vector-space results. The construction
file adds Galois fields and prime powers. The transformations import only
the existing basic definitions, relabelling and finite-set/type mathematics.
There are no dependencies on the project's lower-bound or selection
components, individual covering results or exploratory code.
