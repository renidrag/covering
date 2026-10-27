# Iterated lifting of covering lower bounds

**Proof reconstruction and Lean formalisation: Rob Gardiner, with Codex assistance.**

This supporting excerpt gives the algebra, exact recurrence and universal covering lift used by the pair-covering consequences. A residual seed must be a proved universal lower bound.

## Source and scope

Horsley and Singh, *New lower bounds for t-coverings*, arXiv:1706.06825v2,
[Section 5, Remark 14 and the paragraph after Theorem 15](https://arxiv.org/html/1706.06825v2#S5),
read 16 October 2026. Equation (2) supplies the point-link lift. Remark 14
compares a matrix-bound expression with repeated lifting of b_s+1. We
make the denominators, rounding qualification and independent seed-validity
hypothesis explicit. The theorem and underlying comparison are attributed
to Horsley and Singh; lifting to Schönheim; this project's formalisation
to Rob Gardiner.

The numerical result allows s=0, zero seeds and real coefficients of either
sign, provided the displayed denominator is positive. Indexed coverings
retain every block occurrence, including repetitions. The covering lift
works for all natural multiplicities, hence in particular every positive λ.
The ordinary-family adapter is used only at λ=1.

## Algebra

Use the existing LargeDefect.ratio(N,K,m,α,β) for CB. Here N,K,m are
natural counts and α,β are real; put D=K(α−β)+1. If K≠0 and D≠0,
clearing denominators proves

    N(m+1)/K − CB = N(m+1−Kβ)/(K D).

For K>0,D>0,N≥0, the threshold Kβ≤m+1 gives CB≤N(m+1)/K.
If N>0 the weak and strict comparisons are equivalent to their respective
thresholds; equality is equivalent to Kβ=m+1. At N=0 both ratios vanish.
There is no need for α≥2β, or even β≤α, in these statements. The latter
is one useful sufficient condition for D>0, already proved in the library.

## Exact iteration and the binomial comparison

Define I(v,k,s;h) as the existing Multicover.bound h v k s, reinterpreting
its initial argument as an arbitrary seed. This is an interface to an
existing recurrence, not a second implementation:

    I(v,k,0;h)=h,
    I(v,k,s+1;h)=ceilDiv(v I(v−1,k−1,s;h),k).

For s≤k≤v, prove the stronger division-free inequality

    choose(v,s) h ≤ choose(k,s) I(v,k,s;h).

Induct on s, generalising v,k. The base is equality. In the successor
case k,v>0, the induction hypothesis and the ceiling inequality give

    v choose(v−1,s) h
      ≤ choose(k−1,s) v I(v−1,k−1,s;h)
      ≤ choose(k−1,s) k I(v,k,s+1;h).

Use n choose(n−1,s)=(s+1)choose(n,s+1) twice and cancel the positive
factor s+1. Since choose(k,s)>0, the exact ceiling API yields the collapsed
ceiling bound. This proves a lower estimate on the nested ceilings; it does
not identify them. Natural subtraction is valid in the induction because
s+1≤k≤v, and all cancelled factors are positive.

Combining the real algebra and this inequality gives

    ceil(CB) ≤ ceilDiv(choose(v,s)(m+1),choose(k,s))
             ≤ I(v,k,s;m+1)

when Kβ≤m+1 and D>0. We use the existing natural ceiling, so a negative
real bound is clipped to zero; the implication remains valid. For
nonnegative CB it is the usual integer ceiling. The strict threshold also
gives this weak integer inequality: strictness need not survive rounding.
For v=3,k=2,s=1,m=1,α=2,β=0 the real numbers are 12/5<3, while
both rounded bounds are 3. For I(8,5,2;1), the inner ceiling is 2 and the
outer ceiling is 4; the collapsed ceiling is only ceil(28/10)=3.

## Covering interpretation

Assume s≤t≤k≤v and a universal lower bound h for indexed λ-coverings
on v−s points, block size k−s, strength t−s. For any indexed covering
B:ι→Finset α on v points, prove I(v,k,s;h)≤card ι by induction on s.
The base applies the seed to B. In the successor step every point link
is a covering on v−1 points with block size k−1 and strength t−1.
The induction hypothesis supplies the universal lower bound for those
links; Multicover.lift_lower_bound performs the next ceiling. The identities
(n−1)−s=n−(s+1) identify its residual parameters. Link indices are subtypes
of occurrence indices, so equal blocks are never merged.

This includes t=s and the existing strength-zero covering definition. For
ordinary Family coverings, the existing deduplication bridge turns an
ordinary universal seed into an indexed λ=1 seed, and the ofFamily adapter
returns the conclusion for the original family cardinality. No such
deduplication is used at higher multiplicity.

Combining the numerical comparison with this lift requires the **additional**
universal bound m+1 for the residual covering. A universal bound m, or a
numerical threshold involving m, supplies no such fact.

## Intended public interfaces and correspondence

| Claim | Intended Lean interface | Correspondence/adaptation |
| --- | --- | --- |
| Difference identity; weak, strict, equal comparisons | `difference_identity`, `ratio_le_iff_threshold`, `ratio_lt_iff_threshold`, `ratio_eq_iff_threshold` | Explicit algebra behind Remark 14; only denominator positivity |
| Exact arbitrary-seed recurrence | `iterate`, `iterate_zero`, `iterate_succ` | Reuses Multicover.bound; all ceilings retained |
| Collapsed estimate | `binomial_mul_le`, `collapsed_le_iterate` | Structural binomial induction |
| Rounded comparison | `ceiling_le_collapsed`, `remark14`, `remark14_strict` | Weak rounded conclusion even for strict real threshold |
| Universal indexed lift | `lift_coverLower`, `indexed_lower_bound` | Equation (2), occurrence-preserving links, explicit seed |
| Ordinary lift | `family_lower_bound` | Existing λ=1 adapters and deduplication bridge |
