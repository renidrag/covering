# C(12,6,3) = 15 and the structure of minimum coverings

**Proof adaptation and Lean formalisation: Rob Gardiner.**

Credit is for the adapted proof and formalisation presented here, not
for first proving the covering number or classification. The original
results retain the historical attributions given below.

**Supporting proof of known results.** Fifteen six-element blocks are
necessary and sufficient to cover all triples of twelve points. Every
minimum covering is isomorphic either to a completion of GPPT's Figure 1
partial covering or to its exceptional Figure 6 covering. These alternatives
are disjoint.

**Proof provenance: an adaptation of known results.** This is a self-contained
Lean proof of these conclusions, not a literal translation of GPPT's paper.
Minimum-pair compatibility and the repeated-triple branch follow GPPT with
revised counting. The numerical lower bound and the branch with no repeated
triple of minimum points use replacement arguments, described below.

Read the [self-contained mathematical proof](proof.md) for the argument,
including explicit constructions, shortness symmetry and the projective
branch. The [correspondence appendix](proof.md#appendix-a-correspondence-with-lean)
maps its claims to Lean, and the [contract appendix](proof.md#appendix-b-contracts-dependencies-and-verification)
states exactly what the formal results assert. The source comparison
identifies the historical proofs followed or replaced.

## Attribution and contribution

The numerical minimum and structural alternatives are due to Gordon,
Patashnik, Petro and Taylor (GPPT), Theorems 4.4 and 5.9 of
*Minimum (12,6,3) Covers* (1995).

This project proves them from its [Stanton reconstruction](../11-5-2/README.md).
Minimum-pair compatibility follows GPPT Lemma 5.2 in an at-most-fifteen-block
form, which then proves the numerical lower bound in place of the paper's
Section 4 argument. The repeated-triple branch follows Lemma 5.8 with shorter
excess bookkeeping. Projection, Fano-plane geometry and the seven-cap lemma
replace the argument of Lemmas 5.6–5.7 for the other branch.

These choices make the structural prerequisites self-contained and reusable
in Lean. The [source section](proof.md#sources-and-contribution) distinguishes
the arguments followed or replaced from the established results; no
historical novelty is claimed for these supporting arguments.

## Structural proof and separate catalogue check

The structural proof works with arbitrary completions of Figure 1.
Together with the local GPPT lemmas, it supplies the prerequisite for the
[new thirteen-point result](../13-7-4/README.md).

A separate finite calculation maps all 1,568 normalized Figure 1 completions
into the first 67 entries of a retained catalogue; Figure 6 supplies the last.
Lean checks every isomorphism witness. This proves **catalogue completeness**,
not pairwise nonisomorphism of all 68 entries. The paper's element-minimality
assertions are also outside the formal result.

The catalogue calculation is independent of the thirteen-point proof.
The retained [Figure 1](../../data/gppt-figure1.json),
[Figure 6](../../data/gppt-figure6.json) and
[catalogue](../../data/links-68.json) record the explicit families.

## Build and verify

The public import `CoveringDesigns.C12_6_3` exposes the numerical theorem,
structural reduction and catalogue-completeness theorem:

- `CoveringDesigns.covering_number_12_6_3`
- `CoveringDesigns.gppt_structural_reduction`
- `CoveringDesigns.gppt_classification`

Use `CoveringDesigns.C12_6_3.Structural.Reduction` for the structural result
without importing the catalogue or completion-verification modules.

The [shared verification guide](../../technical-details.md#gppt-verification-and-fresh-replay)
gives the focused verification and fresh-replay instructions. The
[proof appendices](proof.md#appendix-a-correspondence-with-lean) give the exact
contracts and the organization of the formal proof.
