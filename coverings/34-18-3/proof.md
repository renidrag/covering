# The exact covering number $C(34,18,3)=13$

**Exactness deduction and Lean formalisation: Rob Gardiner, with AI assistance.**
23 October 2026.

## Abstract

Every covering of the triples of a thirty-four-point set by eighteen-element
blocks has at least thirteen blocks. A historical LJCR family of thirteen
blocks attains this bound. We combine the project's existing lower theorem
with that particular family to prove $C(34,18,3)=13$, including actual
attainment on every thirty-four-point set. The finite witness and the
connection to the lower bound are checked in Lean.

## Statement and contribution

A **$(v,k,t)$ covering** is a family of distinct $k$-element subsets
of a $v$-point set such that every $t$-element subset is contained in a block.
Its minimum size is $C(v,k,t)$.

**Theorem 1.** On every thirty-four-point set $V$, there is a family of
thirteen distinct eighteen-element blocks covering all triples of $V$.
Every such covering family has at least thirteen blocks. Hence
$$
C(34,18,3)=13.
$$

The lower theorem is a proved result of this project, first public on
19 October 2026 and retained in its 22 October cumulative package. The upper family is the historical
LJCR construction recorded in 2009. The contribution here is to identify
their matching bounds and formally connect the actual family to the
exactness statement.

The Covering Repository query of 23 October 2026 displayed 12–13.
Theorem 1 resolves that displayed interval. The
[source assessment](sources.md) distinguishes the old construction,
earlier lower bounds and this deduction; historical priority for the exact
value remains unresolved.

## 1. The lower bound

**Lemma 2.** Every $(34,18,3)$ covering has at least thirteen blocks.

*Proof.* The project's proved
[offset-two lower theorem](../2k-minus-c-k-3/proof.md) states that, for
every integer $k\ge18$, every ordinary triple covering on $2k-2$ points
by $k$-element blocks has at least thirteen blocks. Its hypotheses are
only the point count, $k\ge18$, and the covering condition.

Set $k=18$. Then $2k-2=34$ and $18\ge18$, so the theorem applies to
every $(34,18,3)$ covering. ∎

All structural restrictions needed in the lower argument are proved inside
the cited component. Its separate fourteen-block exactness theorem has a
different range and is not used here.

## 2. The historical attaining family

Work first on $V_0=\{1,\ldots,34\}$. For a set
$A\subseteq\{1,\ldots,17\}$, write
$A+17=\{a+17:a\in A\}$. Define
$$
B_i=A_i\cup(A_i+17)\qquad(1\le i\le13)
$$
using the following nine-element sets.

| $i$ | $A_i$ |
| ---: | --- |
| 1 | $\{1,2,3,5,11,12,13,14,15\}$ |
| 2 | $\{1,2,4,7,9,11,13,15,16\}$ |
| 3 | $\{1,2,6,8,10,11,13,15,17\}$ |
| 4 | $\{1,3,4,6,10,11,12,13,16\}$ |
| 5 | $\{1,3,7,8,9,11,12,13,17\}$ |
| 6 | $\{1,4,5,8,11,13,14,16,17\}$ |
| 7 | $\{1,5,6,7,9,10,11,13,14\}$ |
| 8 | $\{2,3,4,6,7,8,9,10,16\}$ |
| 9 | $\{2,3,6,7,9,10,12,15,17\}$ |
| 10 | $\{2,4,5,7,9,12,14,16,17\}$ |
| 11 | $\{2,5,6,8,10,12,14,15,16\}$ |
| 12 | $\{3,4,5,6,10,14,15,16,17\}$ |
| 13 | $\{3,4,5,7,8,9,12,14,15\}$ |

Expanding the table gives exactly the thirteen ordered rows in the
[retained historical witness](../../data/c34183-historical-witness.json).
The paired notation records the source's multiple construction.

**Proposition 3.** The family $\mathcal B=\{B_1,\ldots,B_{13}\}$ is a
$(34,18,3)$ covering with exactly thirteen distinct blocks.

*Proof.* Each displayed $A_i$ contains nine distinct points in the first
half of $V_0$. Its translate contains nine points in the disjoint second
half, so $|B_i|=18$. The thirteen $A_i$ are distinct, and
$B_i\cap\{1,\ldots,17\}=A_i$, so the thirteen $B_i$ are distinct.

Coverage is an explicit finite check on this displayed family:
$$
\text{for every }T\in\binom{V_0}{3},
\quad\text{there is an }i\in\{1,\ldots,13\}\text{ with }T\subseteq B_i.
$$
Enumerating the $\binom{34}{3}=5,984$ possible triples and testing their
containment in these thirteen sets leaves no uncovered triple. The retained
checker performs this calculation, and the Lean proof independently proves
the containment property for the same literal family. The appendix explains
the formal finite check and its correspondence to the table. Thus
$\mathcal B$ is a cover of size thirteen. ∎

The computation checks one specified construction. It does not search for
coverings or supply the lower-bound argument.

## 3. Proof of Theorem 1

Let $V$ be any set of cardinality 34. Choose a bijection $f:V_0\to V$.
The family $\{f(B_i):1\le i\le13\}$ has thirteen distinct blocks
of size eighteen. For any triple $T\subseteq V$, the inverse image
$f^{-1}(T)$ is a triple of $V_0$ and lies in a block $B_i$ by Proposition 3.
Therefore $T\subseteq f(B_i)$, proving attainment on $V$.

Lemma 2 applies to every covering on $V$ and gives the matching lower
bound. Together, the actual attaining family and the universal lower
bound prove Theorem 1. ∎

## Appendix A. Lean correspondence

| Mathematical statement | Formal declaration or definition |
| --- | --- |
| Offset-two prerequisite | `CoveringDesigns.TwoKMinusC.OffsetTwo.thirteen_le_card` |
| Lemma 2 | `CoveringDesigns.lower_bound_34_18_3` |
| Historical block list and family | `CoveringDesigns.knownBlocks13_34_18_3`, `CoveringDesigns.knownCover13_34_18_3` |
| Proposition 3 | `CoveringDesigns.knownCover13_34_18_3_card`, `CoveringDesigns.knownCover13_34_18_3_isCover` |
| Transported historical family | `CoveringDesigns.knownCover13_34_18_3_on` |
| Theorem 1 on arbitrary labels | `CoveringDesigns.covering_number_34_18_3_on` |
| Canonical-label specialisation | `CoveringDesigns.covering_number_34_18_3` |

The [lower wrapper](../../lean/CoveringDesigns/C34_18_3/LowerBound.lean)
specializes the unchanged offset-two theorem at $k=18$.
The [witness module](../../lean/CoveringDesigns/C34_18_3/Witness.lean)
contains the fully expanded historical list with each source label $x$
replaced by $x-1$, giving points of type `Fin 34`.

Ordinary `decide +kernel` proves list distinctness, family cardinality
and uniformity. A finite predicate checks that every three points
$a,b,c$ lie together in a listed block, allowing repeated points as well.
The reduction is split by $a$ to bound memory use. `Finset.card_eq_three` then converts that statement
into coverage of every three-element finite set. This is kernel-checked
computation, with no external exclusion certificate or native assertion.

The existing `relabel` interface transports the actual family along a
bijection with `Fin 34`, preserving size and coverage.
The [public exactness theorem](../../lean/CoveringDesigns/C34_18_3.lean)
requires only `[Fintype α]` and `Fintype.card α = 34` and concludes:
```lean
(∃ C : Family α, IsCover C 18 3 ∧ C.card = 13) ∧
(∀ C : Family α, IsCover C 18 3 → 13 ≤ C.card)
```
Here `Family α = Finset (Finset α)`, so cardinality counts distinct blocks.
No symmetry, degree, pair-multiplicity or classification hypothesis is exposed.

The [component audit](../../lean/audits/C34_18_3.lean) checks all twelve
public theorem contracts, the literal family and transport, and an expanded
ordinary-family restatement of exactness. Principal and expanded contracts
must use exactly `propext`, `Classical.choice` and `Quot.sound`;
helper theorems may use a subset. Dependency checks keep the lower and witness
branches separate.

## Appendix B. Provenance and verification

The source credits **LJCR**, “Multiple of (17,9,3) covering”, recorded on
**20 January 2009**. Daniel M. Gordon / La Jolla Covering Repository retains
CC BY 4.0 attribution. That timestamp establishes recorded construction
availability, not first proof of exactness.

The original ordered 234 label bytes have SHA-256
`5f8cd4bcedf84fd8032fa2b324e073115f7baaa8729ef437149c7151d19dfa3f`.
The [input manifest](inputs.json) pins the retained witness and
[transcription checker](../../scripts/check_c34183_witness.py).
That checker binds the JSON rows to the historical byte hash and the Lean
literals after the label shift. Lean separately proves the covering
properties; Python provenance checks supply no mathematical premise.

The [source account](sources.md) identifies the archive, artifact and
dated comparison. The [README](README.md#build-and-verify) and
[shared verification guide](../../technical-details.md) give reproduction
instructions. `./covering verify` compiles and audits the Lean proofs;
`./covering check` checks source/data consistency, and
`./covering audit` validates saved proof evidence without compiling.
