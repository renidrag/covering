# Schönheim’s lower bound and lifting

**Proof reconstruction and Lean formalisation: Rob Gardiner, with Codex assistance.**

This supporting account states the ordinary-family recurrence and universal link-bound interface.

## Mathematical account

Let `C` be a family of distinct `k`-subsets of a `v`-element set, with every
`t`-subset contained in a block, where `1 ≤ t ≤ k ≤ v`. For a point `p`,
delete `p` from each block containing it. The resulting link `C_p` is a
`(v-1,k-1,t-1)` covering: append `p` to any `(t-1)`-subset and use coverage
in `C`. Deletion is injective among blocks containing `p`, so `|C_p|` is
exactly the degree `d(p)`.

If every point link has at least `m` blocks, double counting incidences gives

\[
v m\le\sum_p d(p)=k|C|.
\]

Since `|C|` is an integer and `k > 0`, this implies `|C| ≥ ⌈v m/k⌉`.
This implication accepts any proved link bound, including stronger bounds
than the recursively defined one.

For `t=1`, covering all points gives `v ≤ k|C|`, hence `|C| ≥ ⌈v/k⌉`.
For `t>1`, induction applied to each link gives
`m=S(v-1,k-1,t-1)`. The incidence implication then gives `S(v,k,t)`.
The definition `S(v,k,0)=1` makes the same recurrence express the base case.
No division by zero occurs in this induction, including the boundary `t=k=v`.

This is the λ = 1 specialisation of Schönheim's Theorem I and its nested
ceiling expression, not the later existence/construction results. The source
uses `n,l` where this library uses `v,t`: J. Schönheim, “On coverings”,
*Pacific Journal of Mathematics* **14** (1964), 1405–1411,
[Theorem I, p. 1407](https://msp.org/pjm/1964/14-4/pjm-v14-n4-p29-p.pdf).
Historical credit belongs to Schönheim. The formal interfaces, Lean proofs
and verification integration are contributions of this project.

## Exact interfaces

Names below are in `CoveringDesigns.Schoenheim`. The ambient type `α` is
universe-polymorphic with `[Fintype α] [DecidableEq α]`; `C : Family α`.
`Family`, `Uniform`, `Covers`, `IsCover` and `link` are the existing definitions.

* `ceilDiv a b = (a + b - 1) / b` uses natural-number division.
  `ceilDiv_le_iff` proves `ceilDiv a b ≤ c ↔ a ≤ b*c` when `0 < b`,
  identifying it as the least integer upper quotient.
* `bound (v k t : ℕ) : ℕ` has equations `bound v k 0 = 1` and
  `bound v k (t+1) = ceilDiv (v * bound (v-1) (k-1) t) k`.
  `bound_succ_div` exposes the integer formula, and `bound_one` exposes
  the singleton-cover base case. Values outside the valid range are merely
  those of this total natural-number function; no covering claim is made there.
* `bound_of_links`: for `hk : 0 < k`, `hu : Uniform C k` and
  `hl : ∀ p, m ≤ (link C p).card`, proves
  `ceilDiv (Fintype.card α * m) k ≤ C.card`.
  No covering hypothesis is needed for this counting implication.
* `lift_lower_bound`: if `Fintype.card α = v+1`, `IsCover C (k+1) (t+1)`,
  and for every finite type `β` in the same universe and family `D`,
  `Fintype.card β = v → IsCover D k t → m ≤ D.card`, proves
  `ceilDiv ((v+1)*m) (k+1) ≤ C.card`.
  This packages the application of a previously proved covering bound to links.
* `lower_bound`: given `1 ≤ t`, `t ≤ k`, `k ≤ Fintype.card α` and
  `IsCover C k t`, proves `bound (Fintype.card α) k t ≤ C.card`.
* The three `lower_bound_v_k_t` examples assume `Fintype.card α = v`
  and `IsCover C k t`, and conclude respectively `7 ≤ C.card`,
  `14 ≤ C.card`, and `26 ≤ C.card`.

## Correspondence with the existing foundations

| Mathematical step | Lean declaration |
|---|---|
| A link is a smaller covering | `link_isCover` |
| Deletion preserves the star's cardinality | `link_card` |
| A point deletion leaves `v-1` points | `complement_point_card` |
| Count each block once per point it contains | `degree_sum_of_uniform` |
| Sum a common degree lower bound | `incidence_lower_bound` |
| Cover all singletons | `one_cover_bound` |
| Integer rounding | `ceilDiv_le_iff`, using `Nat.div_le_iff_le_mul_add_pred` |
| Lift link counts and induct on strength | `bound_of_links`, `lower_bound` |

The foundations remain unchanged. The proof imports neither Stanton, GPPT,
the C(12,5,2) result nor the C(13,7,4) result. Closed example arithmetic is
checked by ordinary kernel reduction.

The component audit checks the full interfaces and restates the main theorem
using explicit finite-set conditions. Its axiom checks allow only Lean's
standard `propext`, `Classical.choice` and `Quot.sound`; the recorded audit
also checks the exact foundational dependency set for the main theorem and
its explicit restatement. No admitted proof, additional axiom, native
computation or external search certificate is used.
