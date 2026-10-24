# A Schönheim corollary: $C(38,22,7)\ge135$

**Deduction and Lean formalisation: Rob Gardiner, with AI assistance.**
23 October 2026.

## Statement and proved dependency

A **$(v,k,t)$ covering** is a family of distinct $k$-element subsets of a
$v$-point set covering every $t$-element subset. Its minimum size is $C(v,k,t)$.

**Theorem 1.** Every $(38,22,7)$ covering has at least 135 blocks.

**Universal premise.** The included [preceding result](../37-21-6/proof.md)
proves that every $(37,21,6)$ covering, on every point set
of size 37, has at least 78 blocks. This is a proved theorem, not an
additional hypothesis on the covering in Theorem 1.

We apply the point-link step in Schönheim's proof of Theorem I [1] with
the preceding proved bound. The root seed is this project's
[lower theorem $C(34,18,3)\ge13$](../34-18-3/proof.md#1-the-lower-bound).
This corollary makes an existing consequence explicit; no attaining construction is
asserted. The [source account](sources.md) separates attribution, dated
comparison and unresolved priority.

## Proof of Theorem 1

Let $\mathcal C$ be such a covering on $V$, where $|V|=38$.
For $x\in V$, set
$$
\mathcal C_x=\{B\setminus\{x\}: B\in\mathcal C,\ x\in B\}.
$$
Its blocks have size 21. For every 6-subset $S$ of
$V\setminus\{x\}$, the set $S\cup\{x\}$ has size 7, so some
block of $\mathcal C$ contains it. Deleting $x$ leaves a link block
containing $S$. Deletion is injective on blocks through
$x$: adjoining $x$ recovers the original block. Thus $\mathcal C_x$ is an
ordinary $(37,21,6)$ cover with exactly $d(x)$ blocks,
where $d(x)$ counts the original blocks through $x$.

The universal premise gives $d(x)\ge78$ for every point. Therefore
$$
22|\mathcal C|=\sum_{x\in V}d(x)\ge38\cdot78=2964,
$$
and integrality gives
$$
|\mathcal C|\ge\left\lceil\frac{38\cdot78}{22}\right\rceil
=\left\lceil\frac{2964}{22}\right\rceil=135.
$$
This proves Theorem 1 on every 38-point set. ∎

## Appendix A. Lean correspondence

| Mathematical statement | Formal declaration |
| --- | --- |
| Universal premise | `CoveringDesigns.lower_bound_37_21_6` |
| Point-link step | `CoveringDesigns.Schoenheim.lift_lower_bound` |
| Theorem 1 | `CoveringDesigns.lower_bound_38_22_7` |
| Expanded ordinary-family contract | `CoveringDesigns.Audit38_22_7.lower_bound_explicit` |

The [lower module](../../lean/CoveringDesigns/C38_22_7/LowerBound.lean)
imports `CoveringDesigns.C37_21_6.LowerBound`, which already
provides the Schönheim interface.
It applies `lift_lower_bound` with
`v=37, k=21, t=6, m=78`; these describe the smaller cover.
The preceding universal theorem discharges its quantified link premise.
Ordinary kernel reduction evaluates the ceiling.

The [public entry](../../lean/CoveringDesigns/C38_22_7.lean) exposes:
```lean
theorem lower_bound_38_22_7 {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 38) (hC : IsCover C 22 7) :
    135 ≤ C.card
```

Here `Family α = Finset (Finset α)`. The covering condition says every
block has size 22 and every 7-subset lies in a block. There is no
caller-supplied seed, structural condition or decidable-equality assumption.

The [audit](../../lean/audits/C38_22_7.lean) checks this full arbitrary-label
contract and proves the explicit finite-set restatement. Both must use
exactly `propext`, `Classical.choice` and `Quot.sound`.
The [input manifest](inputs.json) names the prerequisite interfaces.
This chain imports the C34 lower module, not its witness or exactness entry;
the preserved general theorem retains its own earlier dependencies.

The [verification commands](README.md#build-and-verify) distinguish
fresh compilation (`./covering verify`) from validation of the resulting
record (`./covering audit`).

## References

1. J. Schönheim, *On coverings*, Pacific J. Math. **14** (1964), 1405–1411,
   [proof of Theorem I, p. 1407](https://msp.org/pjm/1964/14-4/pjm-v14-n4-p29-p.pdf#page=4).
   We use its point-link step with the stronger universal premise above.
2. Rob Gardiner, with AI assistance, [the C34 lower theorem](../34-18-3/proof.md)
   and the [immediate prerequisite](../37-21-6/proof.md).
3. [Dated source comparison and priority limitations](sources.md).
