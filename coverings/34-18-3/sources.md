# Construction and theorem sources

Assessed **23 October 2026**. This formalisation introduces no fresh
historical-priority conclusion.

- **Lower theorem:** the preserved
  [offset-two module](../../lean/CoveringDesigns/TwoKMinusC/OffsetTwo.lean),
  `thirteen_le_card`, with its
  [existing proof account](../2k-minus-c-k-3/README.md).
- **Historical construction:** Daniel M. Gordon / La Jolla Covering
  Repository, [Zenodo version 1.2](https://zenodo.org/records/19735294),
  CC BY 4.0. Entry credit: “LJCR; Multiple of (17,9,3) covering”;
  timestamp 2009-01-20 19:36:43.
  [LJCR page](https://ljcr.dmgordon.org/cover/show_cover.php?v=34&k=18&t=3).
- **Exact artifact:** `artefact:a17c4aa7-0a69-59aa-acd4-1b6c694122ec`.
  Compressed-frame SHA-256
  `878a46e477ed08a152692d3960b2f52740eaa858cab2b93c88780054bc4dcc8a`;
  decoded-byte hash and ordered block list are in the
  [new retained witness](../../data/c34183-historical-witness.json).
  No CVKT file is modified or required by the public Lean proof.
- **Dated comparison:** the [Covering Repository form](https://www.coveringrepository.com/systems.aspx),
  queried on 23 October 2026 with (v,k,t,m)=(34,18,3,3), displayed 12–13;
  its [history entry](https://www.coveringrepository.com/history.aspx?id=111990)
  credits the historical construction. Gordon's public metadata reported
  the same interval. A displayed lower entry is not an exactness proof.
- **Project check:** the included [checker](../../scripts/check_c34183_witness.py)
  binds the historical decoded-byte hash to the retained rows and the shifted
  Lean literals, and checks all 5,984 triples. The Lean kernel independently
  verifies the actual family, its thirteen distinct blocks and coverage.
- **Earlier lower theorem:** the offset-two result was first public on
  19 October 2026; see the [release history](../../RELEASE_HISTORY.md).
  It already supplies lower thirteen at k=18. The historical upper family
  and this theorem imply exactness mathematically before the separate
  C34 declaration. The project contribution here is their explicit connection.
- **Priority limits:** the full older originals by Mills, Mills–Mullin and
  Todorov–Tonchev were not inspected; the [general sources](../2k-minus-c-k-3/sources.md)
  record the gaps. A fresh read of the [sixteen-cell computational deposit](https://zenodo.org/records/23465708)
  was unavailable. No independent earlier explicit exactness statement was
  established by the bounded search. Historical priority remains unresolved.

The thirteen-block family is not this project's construction. The new
contribution here is a kernel-checked connection of that family to the
existing lower theorem and an explicit exactness interface.
