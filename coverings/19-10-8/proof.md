# A Schönheim corollary: $C(19,10,8)\ge1908$

**Deduction and Lean formalisation: Rob Gardiner, with AI assistance.**
23 October 2026.

## Statement and contribution

A **$(v,k,t)$ covering** is a family of distinct $k$-element subsets
of a $v$-point set such that every $t$-element subset lies in a block.
Write $C(v,k,t)$ for the smallest possible number of blocks.

**Theorem 1.** On every 19-point set, every family of 10-element
blocks covering all 8-element subsets has at least 1908 blocks.
Thus $C(19,10,8)\ge1908$.

The structural input is this project's
[proof that $C(14,5,3)\ge41$](../14-5-3/proof.md), published on
22 October 2026. Schönheim's theorem propagates that universal lower
bound through the following five corollaries, retaining every intermediate
ceiling:

| Cover being bounded | Universal premise for each point link | Exact ceiling |
| --- | --- | --- |
| [$(15,6,4)$](../15-6-4/proof.md) | Every $(14,5,3)$ cover has at least 41 blocks. | $\lceil15\cdot41/6\rceil=\lceil615/6\rceil=103$ |
| [$(16,7,5)$](../16-7-5/proof.md) | Every $(15,6,4)$ cover has at least 103 blocks. | $\lceil16\cdot103/7\rceil=\lceil1648/7\rceil=236$ |
| [$(17,8,6)$](../17-8-6/proof.md) | Every $(16,7,5)$ cover has at least 236 blocks. | $\lceil17\cdot236/8\rceil=\lceil4012/8\rceil=502$ |
| [$(18,9,7)$](../18-9-7/proof.md) | Every $(17,8,6)$ cover has at least 502 blocks. | $\lceil18\cdot502/9\rceil=\lceil9036/9\rceil=1004$ |
| $(19,10,8)$ | Every $(18,9,7)$ cover has at least 1004 blocks. | $\lceil19\cdot1004/10\rceil=\lceil19076/10\rceil=1908$ |

This note proves the chain and identifies its final row with Theorem 1.
The preceding accounts give each intermediate result and its formal
declaration. A cover of size 1908 is not part of the conclusion.

The bound improves the lower entry 1722 in the Covering Repository query
of 23 October 2026 by 186. This is a dated comparison; the
[source assessment](sources.md) leaves historical priority unresolved.
The seed and these numerical deductions belong to this project's proof
account; the general lifting theorem is due to Schönheim.

## 1. The universal lifting step

**Lemma 2 (Schönheim).** Let $2\le t\le k\le v$ and let $m$ be a
nonnegative integer. Suppose **every** $(v-1,k-1,t-1)$ covering, on
**every** point set of size $v-1$, has at least $m$ blocks. Then every
$(v,k,t)$ covering $\mathcal C$ satisfies
$$
|\mathcal C|\ge\left\lceil\frac{vm}{k}\right\rceil.
$$

*Proof.* For a point $x$, let $d(x)$ be the number of blocks containing it,
and form its point link
$$
\mathcal C_x=\{B\setminus\{x\}:B\in\mathcal C,\ x\in B\}.
$$
Each member has $k-1$ points. If $S$ is any $(t-1)$-subset avoiding $x$,
some block of $\mathcal C$ contains the $t$-set $S\cup\{x\}$; its
remainder contains $S$. Thus $\mathcal C_x$ is a covering on the
remaining $v-1$ points. Deletion of $x$ is injective on blocks through $x$,
because adjoining $x$ recovers the original block. Consequently
$|\mathcal C_x|=d(x)\ge m$.

Count pairs $(x,B)$ with $x\in B\in\mathcal C$. Each block contributes
$k$ incidences and each point contributes $d(x)$, so
$$
k|\mathcal C|=\sum_x d(x)\ge vm.
$$
Since $|\mathcal C|$ is an integer and $k>0$, the stated ceiling follows. ∎

This is the point-link proof of the classical inequality. The premise is a
theorem about all smaller coverings; one construction with $m$ blocks
would not supply it.

## 2. Proof of Theorem 1

Start with the proved universal bound $C(14,5,3)\ge41$. Apply Lemma 2
to the five rows of the opening table in order. In every row,
$2\le t\le k\le v$, and the preceding result supplies the lemma's
premise for every smaller covering on every point set of the required size.
The displayed ceiling therefore proves a universal lower bound, which is
available as the next row's premise. The last row gives
$C(19,10,8)\ge1908$, proving Theorem 1. ∎

Every intermediate ceiling is kept. The five corollaries in the full chain
give $103,236,502,1004,1908$ from the same seed. The improvement over the
classical chain comes from the stronger 41 starting bound; the lifting
argument is Schönheim's.

## Appendix A. Lean correspondence

| Mathematical statement | Formal declaration |
| --- | --- |
| Lemma 2 | `CoveringDesigns.Schoenheim.lift_lower_bound` |
| Immediate universal premise | `CoveringDesigns.lower_bound_18_9_7` |
| Theorem 1 | `CoveringDesigns.lower_bound_19_10_8` |
| Expanded ordinary-family contract | `CoveringDesigns.Audit19_10_8.lower_bound_explicit` |

The [lower-bound module](../../lean/CoveringDesigns/C19_10_8/LowerBound.lean)
applies the existing lifting interface with
`v=18, k=9, t=7, m=1004`.
Those interface parameters describe the smaller cover; its conclusion
has 19 points, block size 10 and strength 8.
The preceding theorem discharges its universally quantified smaller-cover
premise. Ordinary kernel reduction evaluates the natural-number ceiling.

The [public entry](../../lean/CoveringDesigns/C19_10_8.lean) exposes:
```lean
theorem lower_bound_19_10_8 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 19) (hC : IsCover C 10 8) :
    1908 ≤ C.card
```

Here `Family α = Finset (Finset α)`; `IsCover` says that every block
has size 10 and every 8-subset is contained in a block.
No seed or structural hypothesis remains for the caller.

The dependency chain uses the seed's lower module and the preceding lifts.
The 41 proof internally uses structural completion lemmas, including
`completion_at_least_27`. Its separate downstream `C14_5_3.Completion28`
module is absent from this chain. The [input manifest](inputs.json)
records the direct interfaces.

The [full-contract audit](../../lean/audits/C19_10_8.lean) checks the
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
