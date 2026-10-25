# Sources and attribution

24 October 2026. Rob Gardiner, with AI assistance.

## Lower bound and supporting classification

The new argument rules out 16 blocks. It is also formalised in Lean.
The proof uses the two-form classification of seven-block
(18,8,2) coverings, proved in the included [supporting account](../seven-block/proof.md).
That classification is supporting mathematics, not a claim of first discovery.

The known result C(18,8,2)=7 is included in Gordon and Stinson,
“Coverings,” *Handbook of Combinatorial Designs*, second edition, pp.365–373,
[Theorem 1.31(5)](https://dmgordon.org/papers/hcd.pdf).
Füredi, “Covering pairs by q²+q+1 sets,” *Journal of Combinatorial Theory,
Series A* **54** (1990), 248–271,
[Theorem 2.5](https://doi.org/10.1016/0097-3165(90)90034-T), also gives a
way to prove the required Fano structure: 18/8>11/5, so the dual support family
contains a Fano plane. Incidence equations then recover the two forms.
The included elementary Lean proof establishes the classification directly
and does not assume Füredi's theorem.

Horsley and Singh, “New lower bounds for t-coverings,” *Journal of
Combinatorial Designs* **26** (2018), 369–386,
[Table 1](https://arxiv.org/html/1706.06825v2#S7), includes these parameters;
the standard choice of smaller-cover bounds gives C(19,9,3)≥16. The
source search of 24 October 2026 found no earlier proof of C(19,9,3)≥17. LJCR's
[public metadata](https://raw.githubusercontent.com/dmgordo/LJCR/main/coverings/coverdata.json)
then recorded 16–17. These observations do not establish historical priority.
Mills (1979) and Mills–Mullin (1992) remained unavailable; their absence is
not a premise of the mathematical proof.

## Belic's 17-block construction

LJCR credits **Rade Belic**, with a record dated **11 June 1997**, for the
17-block construction. The retained source is Daniel M. Gordon's
[LJCR v1.2 deposit](https://zenodo.org/records/19735294), dated 24 April 2026,
frame `covers.json /C(19,9,3)`. The deposit date does not date the construction.
Licence: **CC BY 4.0; Daniel M. Gordon / La Jolla Covering Repository**.

The [canonical input](../../data/c1993-belic-witness.json) preserves the
one-based block order and full provenance. Its original ordered 153-byte
source has SHA-256
`53bd57d226f1d42fb579bbb4538e888d78ef6f55afe93c150b8c726e70ae2841`.
[inputs.json](inputs.json) registers the retained input and correspondence
checks. Lean shifts every label down by one and independently proves
uniformity, distinctness and complete triple coverage for that literal family.
