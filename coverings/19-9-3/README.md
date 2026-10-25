# C(19,9,3)=17

**Rob Gardiner**

We prove **C(19,9,3)=17**. The new argument shows that 16 blocks cannot
cover all triples. Rade Belic's known construction uses 17 blocks. Lean
verifies both the lower bound and the construction.

Read the [proof](proof.md), which includes the 17 blocks and an
[appendix linking the argument to Lean](proof.md#appendix-a-lean-correspondence-and-verification).

## Proof in outline

A covering with 16 blocks would have at least 8 points lying in 7 blocks
each. The proof uses the classification of their links to show that
there are exactly 8 such points. The blocks meet these points in the
14 planes of AG(3,2). Counting and parity then show that the remaining
11 points leave a triple uncovered.

The main step is showing how these minimum links constrain one another
because they share blocks from the same covering.

## Supporting results and construction

Take the 7 blocks containing a minimum-degree point and remove that
point from each. This gives a (18,8,2) covering with 7 blocks. Its two possible forms are proved in the included
[classification](../seven-block/proof.md). This is the a=2 case of the
general result; the proof here does not need the other values of a.

LJCR recorded Belic's construction on 11 June 1997. The
[sources](sources.md) give the earlier results and construction credit,
including CC BY 4.0 attribution to Daniel M. Gordon / La Jolla Covering
Repository.

## Build and verify

`CoveringDesigns.covering_number_19_9_3_on` proves the result for any set
of 19 points. Use `./covering verify 19-9-3`; the
[shared guide](../../technical-details.md) explains setup and verification.
