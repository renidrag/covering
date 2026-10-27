# Lower bounds for C(6k,k,2)

**Proof reconstruction and Lean formalisation: Rob Gardiner, with Codex assistance.**

We prove **C(6k,k,2) ≥ 43 for every k ≥ 6**. The lower bound also holds
when block occurrences may repeat.

The [mathematical proof](proof.md) gives C(36,6,2)≥43 and C(72,12,2)≥43,
and twelve further lower bounds by Schönheim lifting. The
[numerical table](numerical.md) lists all fourteen bounds and every
intermediate ceiling. The [combined table](../qk-k-2/bounds.md) includes
these rows alongside all other numerical consequences of the pair results.

| Parameters | Conclusion |
|---|---|
| k≥6 | C(6k,k,2)≥43 |
| (36,6,2), (72,12,2) | Lower bound 43 |
| (37,7,3), (73,13,3) | Lower bounds 228 and 242 |
| Six successive lifts from each pair bound | Twelve lower bounds in total, through strength 8 |

## Proof in outline

Incidence counting gives a lower bound of 42. At equality, Füredi’s
classification forces a truncated plane or a twisted plane of order 6.
A determinant calculation excludes the twisted case. Completing the
truncated plane by adding one point and seven lines gives a projective
plane of order 6.

Its integer incidence matrix, reduced modulo 3, would have rank at most 21
and at least 22. The upper bound uses a discriminant obstruction on the
42-dimensional sum-zero space. The lower bound uses integer lifts modulo 9
to show that the kernel is totally isotropic. The contradictory rank bounds
exclude 42 blocks and prove the result.

## Attribution and contribution

Bruck–Ryser (1949) proved that no projective plane of order 6 exists.
This account formalises a specialised proof using finite-field linear
algebra and integer lifts. The equality classification is due to Füredi,
and the numerical lifts use Schönheim’s recurrence. The
[source section](proof.md#sources-and-contribution) gives the attribution
and the dated numerical comparisons.

## Build and verify

Import `CoveringDesigns.C6k_K_2` for the complete result, or its `.LowerBound`
module for the general covering theorem. The [proof appendix](proof.md#appendix-a-lean-correspondence)
states the supported interfaces and audit scope. Use `./covering verify 6k-k-2`
and then `./covering audit 6k-k-2`; the [shared guide](../../technical-details.md)
explains setup, source checks, compilation and verification-record validation.
