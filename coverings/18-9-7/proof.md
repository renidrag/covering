# A Schönheim corollary: $C(18,9,7)\ge1004$

**Deduction and Lean formalisation: Rob Gardiner, with AI assistance.**
23 October 2026.

## Statement and dependency

A **$(v,k,t)$ covering** is a family of distinct $k$-element subsets
of a $v$-point set such that every $t$-element subset lies in a block.
Write $C(v,k,t)$ for the smallest possible number of blocks.

**Theorem 1.** On every 18-point set, every family of 9-element
blocks covering all 7-element subsets has at least 1004 blocks.
Thus $C(18,9,7)\ge1004$.

**Proved dependency.** We use
[$C(17,8,6)\ge502$](../17-8-6/proof.md):
every $(17,8,6)$ covering, on every point set of size 17,
has at least 502 blocks. This universal statement applies to each point
link below.

Schönheim supplies the lifting argument. The structural seed is this project's
[proof of $C(14,5,3)\ge41$](../14-5-3/proof.md), published on 22 October 2026.
This account records its fourth lifting corollary and the corresponding
Lean formalisation. A cover of size 1004 is not part of the conclusion.

The bound improves the lower entry 906 in the Covering Repository query
of 23 October 2026 by 98. The [source assessment](sources.md) records
this dated comparison and leaves historical priority unresolved.

## Proof of Theorem 1

Let $\mathcal C$ be such a covering on an 18-point set $V$.
For each $x\in V$, form
$$
\mathcal C_x=\{B\setminus\{x\}:B\in\mathcal C,\ x\in B\}.
$$
Its blocks have size 8. Every 6-subset $S$ of $V\setminus\{x\}$
is covered: a block of $\mathcal C$ containing $S\cup\{x\}$ leaves a
block of $\mathcal C_x$ containing $S$. Deletion is injective on blocks
through $x$, since adjoining $x$ recovers the original block. Thus
$\mathcal C_x$ is an ordinary $(17,8,6)$ covering, with as many
blocks as the number $d(x)$ of original blocks through $x$.

The proved dependency gives $d(x)\ge502$ for every $x$.
Counting point-block incidences gives
$$
9|\mathcal C|=\sum_{x\in V}d(x)\ge18\cdot502=9036.
$$
Since $|\mathcal C|$ is an integer,
$$
|\mathcal C|\ge\left\lceil18\cdot502/9\right\rceil
=\left\lceil9036/9\right\rceil=1004.
$$
The argument applies to every such covering on every 18-point set,
proving Theorem 1. ∎

## Appendix A. Lean correspondence

| Mathematical statement | Formal declaration |
| --- | --- |
| Schönheim point-link step | `CoveringDesigns.Schoenheim.lift_lower_bound` |
| Immediate universal premise | `CoveringDesigns.lower_bound_17_8_6` |
| Theorem 1 | `CoveringDesigns.lower_bound_18_9_7` |
| Expanded ordinary-family contract | `CoveringDesigns.Audit18_9_7.lower_bound_explicit` |

The [lower-bound module](../../lean/CoveringDesigns/C18_9_7/LowerBound.lean)
applies the existing lifting interface with
`v=17, k=8, t=6, m=502`.
Those interface parameters describe the smaller cover; its conclusion
has 18 points, block size 9 and strength 7.
The preceding theorem discharges its universally quantified smaller-cover
premise. Ordinary kernel reduction evaluates the natural-number ceiling.

The [public entry](../../lean/CoveringDesigns/C18_9_7.lean) exposes:
```lean
theorem lower_bound_18_9_7 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 18) (hC : IsCover C 9 7) :
    1004 ≤ C.card
```

Here `Family α = Finset (Finset α)`; `IsCover` says that every block
has size 9 and every 7-subset is contained in a block.
No seed or structural hypothesis remains for the caller.

The dependency chain uses the seed's lower module and the preceding lifts.
The 41 proof internally uses structural completion lemmas, including
`completion_at_least_27`. Its separate downstream `C14_5_3.Completion28`
module is absent from this chain. The [input manifest](inputs.json)
records the direct interfaces.

The [full-contract audit](../../lean/audits/C18_9_7.lean) checks the
arbitrary-label type and restates it using explicit block sizes and subset
containment. Both the principal theorem and its expanded restatement must
use exactly `propext`, `Classical.choice` and `Quot.sound`.
The [README](README.md#build-and-verify) gives reproduction commands.
`./covering verify` compiles and audits the proofs;
`./covering audit` validates the resulting record without compiling.

## References

1. J. Schönheim, *On coverings*, Pacific Journal of Mathematics **14**
   (1964), 1405–1411, Theorem I and its point-incidence proof.
   [Original paper](https://msp.org/pjm/1964/14-4/pjm-v14-n4-p29-p.pdf).
2. Rob Gardiner, with AI assistance, [a structural proof of
   $41\le C(14,5,3)\le43$](../14-5-3/proof.md).
   The source account there credits the known supporting results.
3. [Dated comparison and source limitations](sources.md), assessed
   23 October 2026.
