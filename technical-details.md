# Verifying the published proofs

This repository contains the following Lean components:

| Import | Main results |
|---|---|
| `CoveringDesigns.C11_5_2` | Minimum seven; exactly two minimum isomorphism types |
| `CoveringDesigns.C12_6_3` | Minimum fifteen; structural alternatives; separate catalogue completeness |
| `CoveringDesigns.C13_7_4` | Minimum thirty |
| `CoveringDesigns.C18_10_3` | Minimum twelve |
| `CoveringDesigns.Applications.C18103Lifts` | Five higher-strength lower bounds from that twelve-block minimum |

The Stanton–GPPT–C13 dependency order is shared foundations, the eleven-point
classification, the twelve-point reduction, then the thirteen-point proof.
The thirteen-point result uses arbitrary completions of GPPT's structural
forms. It imports neither the catalogue nor completion-verification modules.

## C(34,18,3)=13 and two direct lifting chains

The [C34 account](coverings/34-18-3/README.md) connects the earlier universal
lower theorem to the historical LJCR thirteen-block family. Import
`CoveringDesigns.C34_18_3` and use `covering_number_34_18_3_on` for necessity
and an actual attaining family on arbitrary finite labels. The
[witness](data/c34183-historical-witness.json) and
[checker](scripts/check_c34183_witness.py) retain its source correspondence.

The [first chain](coverings/19-10-8/README.md) gives lower bounds
103,236,502,1004,1908 at (15,6,4) through (19,10,8), starting from 41 at
(14,5,3). The [second chain](coverings/39-23-8/README.md) gives
24,44,78,135,229 at (35,19,4) through (39,23,8), starting from 13 at
(34,18,3). Every step uses the preceding universal lower theorem and
retains its ceiling. Each result has its own `CoveringDesigns.Cv_k_t`
entry, `.LowerBound` module and full-contract audit. The lower chains do
not depend on the C34 historical witness or an attaining-family hypothesis.

For a focused check, use `./covering verify 34-18-3`,
`./covering verify 19-10-8` or `./covering verify 39-23-8`, followed by the
matching `./covering audit` command. Every intermediate parameter is also
a target; whole-library verification includes all eleven components.
`./covering check` validates the C34 historical data and Lean transcription;
the Lean kernel separately proves the family's covering properties.

## C(19,9,3)=17 and the seven-block classification

Read the [C19 account](coverings/19-9-3/README.md) for the proof that 16
blocks cannot suffice and for Belic's known 17-block construction. The
[supporting account](coverings/seven-block/README.md) proves the two forms
of minimum pair coverings and credits the earlier results. Both of its
documented targets are included:

```sh
./covering verify seven-block-core
./covering audit seven-block-core
./covering verify seven-block
./covering audit seven-block
./covering verify 19-9-3
./covering audit 19-9-3
```

The core proves the general a≥2 classification independently of Stanton;
the all-a adapter adds a=1. C19 uses only a=2. Its main lower-bound import
closure has 45 project modules. The full C19 target has 69 steps because
its unchanged audit also checks the witness and retained older completion
and fifteen-block rank results through separate verification roots. Those
alternatives are not prerequisites of the shorter lower-bound theorem.
Whole-package verification includes all three targets without duplicate
module compilations.

`./covering check` verifies the [witness inputs](coverings/19-9-3/inputs.json),
including exact agreement of the retained original text, the attributed
[JSON witness](data/c1993-belic-witness.json) and the Lean literal after its
label shift. Every input resolves inside the package. These integrity and
coverage checks are separate from the Lean theorem and axiom audits.

## Lower bounds for C(q²+q+2,q+2,3), odd q≥3

The [account](coverings/q2-plus-q-plus-2-q-plus-2-3/README.md) proves
C(32,7,3)≥149, C(58,9,3)≥375 and C(92,11,3)≥774 as instances of one
family theorem. Import `CoveringDesigns.ProjectiveLinkBounds` and use
`indexed_completion_lower_bound` for indexed blocks or
`completion_lower_bound` for ordinary families. Both require only the
stated parameters and covering conditions.

```sh
./covering verify projective-link-bounds
./covering audit projective-link-bounds
```

The [proof appendix](coverings/q2-plus-q-plus-2-q-plus-2-3/proof.md#appendix-lean-correspondence)
identifies the parity, deletion and completion interfaces. The dedicated
audit checks full theorem types, expanded covering assumptions and
transitive axioms. Source checks preserve the independent proof without
deletion and prohibit dependencies from older components on this addition.
There is no construction data or external certificate in this component.

## Set up dependencies

Install Lean **4.34.1** with Lake available on the path. Dependency setup and verification need Python **3.14+** with the
standard-library `compression.zstd` module. The tested CI series is declared in
[.python-version](.python-version). No third-party Python packages are required
for verification. Use a project virtual environment; do not replace system Python. From the repository root:

```sh
python3.14 -m venv .venv
. .venv/bin/activate
export ELAN_TOOLCHAIN="$(cat lean/lean-toolchain)"
python3 scripts/setup_dependencies.py
lake -d lean build Mathlib
```

The [installer](scripts/setup_dependencies.py) downloads the sources pinned
in [lean/dependencies.json](lean/dependencies.json), checks their hashes,
and extracts them under `lean/vendor/`. Mathlib is pinned to **v4.34.1**.
The dependency build is needed once for a new installation. Keep
`ELAN_TOOLCHAIN` set when running the commands below from the repository
root: Elan selects the toolchain before Lake processes `-d lean`, so the
nested toolchain file alone is insufficient when no default is configured.

An existing pinned dependency installation and its caches can be reused
with `python3 scripts/setup_dependencies.py --reuse-existing /path/to/vendor`.
The installer validates its provenance before creating local links.

## Reproduce verification

The recorded workflow uses the same Python **3.14+** environment and runs on
**macOS or Linux**. `doctor` rejects missing zstd support; the original compressed
witness check is required and cannot be skipped:

```sh
./covering doctor
./covering check
./covering verify
./covering audit
```

`doctor` checks prerequisites. `check` checks source boundaries, input hashes,
the explicit covering data and deterministic generated witnesses; it does
not verify Lean proofs. `verify` recompiles every project module, with up to
two compiler commands by default, then runs the component and combined Lean
audits serially. It reuses upstream
dependency caches, never project proof success on a fresh run.
`audit` checks the resulting records against the current inputs without
rebuilding.

For a focused verification, use `./covering verify 11-5-2`,
`./covering verify 12-6-3` or `./covering verify 13-7-4`. Each includes its
prerequisites. `./covering status` reports progress; after a failed or
interrupted run, use the resume command printed by the CLI. Changed proof
inputs or verification scripts require a new verification.

`./covering plan` and fresh `./covering verify` runs default to at most two
compiler commands. Use `--workers 1` for a serial local run or `--workers 2`
to choose two explicitly. The shared GitHub workflow pins `--workers 1`.
Each build waits until every direct project prerequisite has passed; all audits
run serially after the builds. Both modes use identical canonical step IDs,
commands and contract/axiom checks. The serial prerequisite check loads Lake's configuration
before any concurrent compiler commands. Every step has its own log and record;
one coordinator owns the workspace lock and updates shared state atomically.

On failure or interruption the CLI stops new work, cancels and drains all active
commands, and records failed, cancelled and unstarted steps. Resume revalidates
the canonical prefix's logs, snapshots and output hashes, then rebuilds the
entire remaining tail, including any earlier out-of-order successes. Omitting
`--workers` on resume preserves the recorded count, including one worker when
fresh runs default to two. Changing the count or verification scripts requires a
new run. A completed record still requires every theorem and exact axiom audit.

Commands have time limits and, by default, a sampled process-group memory
limit of **8192 MiB per command**. With two workers, two such groups can run
concurrently: this is not a combined workspace memory cap. The sampled limit
can overshoot a brief peak.
Use `--no-memory-guard` with `doctor`, `run`, `plan` or `verify` to omit this
optional watchdog. `--memory-mib` still sets Lean's own `-M` limit during
verification. Logs explicitly record whether the watchdog was enabled;
resuming a run preserves that choice, and auditing validates it. The CLI
manages timeouts, recovery and verification records in either mode.
Use `./covering plan` to inspect its commands before running them.

For an ordinary build and the combined theorem audit:

```sh
lake -d lean build CoveringDesigns
lake -d lean env lean lean/audits/All.lean
```

These commands check Lean code and theorem contracts but do not produce
the recorded workflow's command-by-command evidence.

## GitHub Actions

Branch pushes changing only citation metadata, release history, the root
README, attribution notices, this guide or the Markdown result accounts
skip the workflow. Changes to proofs, witnesses, manifests, tools, tests,
dependency pins or the workflow still run full verification, including when
mixed with documentation changes. Pull requests, tag pushes and manual
**Run workflow** requests retain full verification. For a release snapshot
whose documentation-only push was skipped, run the workflow manually on
that revision before recording its verification. A skipped push does not
create a fresh proof-verification result.

The [Lean verification workflow](.github/workflows/lean-verification.yml)
runs on the events described above. Its proof job exports
`ELAN_TOOLCHAIN` from `lean/lean-toolchain` for every later step, so commands
launched from the repository root use the pin without a configured Elan default.
It installs that toolchain and the checksum-verified dependency sources,
then fetches Mathlib's upstream build cache for the imported dependencies.
The cache downloader runs inside Mathlib to accommodate the archive-based
path dependencies; the workflow checks that their pinned revisions agree
with Mathlib's own manifest and links the cache's standard package paths
to those installed sources. It does not change either manifest.

Two required jobs run independently. The proof job starts with no project
build cache or previous verification records. It runs the source checks,
`./covering verify --workers 1 --no-memory-guard` and `./covering audit`. All published
components, including the separate GPPT catalogue theorem, are compiled and
audited. The exact standard-axiom guards and theorem contracts are the same
as in local verification. The tools job needs only Python and runs the full
verification-tool test suite and record-validation controls.

The existing **Lean proofs and audits** check waits for both jobs and passes
only when both succeed. A failed, skipped or cancelled prerequisite cannot
produce a passing check. This final gate aggregates their results; the proof
job performs every compilation and Lean audit.

The proof job runs one compiler command at a time on Ubuntu, with two Lean
threads and a 60-minute job limit.
Dependency downloads and proof verification omit the optional process-group
memory watchdog. Lean retains its own `-M6144` setting; this is not an
aggregate process-group RSS limit. Each module has 300 seconds and each
Lean audit 60 seconds. The tools job has a 20-minute limit. Each job's logs
and verification records are retained in separate downloadable artifacts for
30 days, including records from failed runs when available.

The README badge links to the workflow history and reports GitHub's live
status. A passing run means all of the required steps above succeeded for
that run's revision. Before the first successful run, the badge is not
evidence of completed GitHub verification. A private repository's badge is
not available to outside readers; see GitHub's
[status-badge documentation](https://docs.github.com/en/actions/how-tos/monitor-workflows/add-a-status-badge).

## GPPT verification and fresh replay

For a focused verification of C(12,6,3), including its Stanton prerequisite
and local geometry, run:

```sh
./covering check
./covering verify 12-6-3
./covering audit 12-6-3
```

`check` includes the retained completion data and its deterministic generator;
it does not verify Lean proofs. The focused `verify` rebuilds the component
and its prerequisites and runs the GPPT theorem audit. A whole-library run
additionally runs all component audits, including the standalone Stanton and
C13 audits.

For a fresh sequential replay on macOS or Linux that excludes existing
project build artifacts, use:

```sh
./covering run --name gppt-structural-fresh --timeout 600 \
  --memory-mib 6144 -- lake -d lean env python3 scripts/recheck_gppt.py
```

The [replay script](scripts/recheck_gppt.py) recompiles every project module
in GPPT's dependency closure, including Stanton, into a temporary tree.
Only the pinned dependency caches are reused. Each module has a sixty-second
limit, except the completion checks, which have a 180-second allowance.
The outer command has a ten-minute limit and a sampled aggregate RSS guard
of six GiB. The watchdog automatically uses `libproc` on macOS or `/proc` on
Linux; its sampled limit is not a hard operating-system allocation cap.

This replay records compiler commands, module hashes and runtimes in
`results/gppt-structural-fresh.json`, separately from the ordinary verification
records. The bounded command's log and record are retained under
`results/commands/`. A whole-library verification followed by `./covering audit`
checks the public theorem contracts, exact axiom sets, source boundaries and
input hashes.

The mathematical contracts and module correspondence are in the
[GPPT proof appendices](coverings/12-6-3/proof.md#appendix-a-correspondence-with-lean).
Use `CoveringDesigns.C12_6_3.Structural.Reduction` for the structural result
without importing the separate catalogue calculation; the full public import
is `CoveringDesigns.C12_6_3`.

## C(18,10,3) and its lifted lower bounds

Read the [result account](coverings/18-10-3/README.md), its
[structural proof and Lean correspondence](coverings/18-10-3/proof.md), and
[attribution and source discussion](coverings/18-10-3/sources.md).
The exact eighteen-point result and the five lifted lower bounds are included
in the full verification above. Focused verification uses:

```sh
./covering verify 18-10-3
./covering audit 18-10-3
./covering verify c18103-lifts
./covering audit c18103-lifts
```

The public imports are `CoveringDesigns.C18_10_3` and
`CoveringDesigns.Applications.C18103Lifts`. The seed audit also retains the
reusable square-support lemmas; the simplified covering deduction and its
lifts do not use them. The lifts depend only on the seed's lower bound and
the existing iterated lifting theorem. They do not assume an attaining
construction for the higher-strength parameters.

## Statements and trust checks

`Family α` means `Finset (Finset α)`, so blocks are distinct.
`IsCover C k t` requires exact block size `k` and coverage of every
`t`-element subset. Each covering-number theorem asserts both an explicit
covering of the stated size and a lower bound for every covering.

The [Lean audits](lean/audits/) check theorem types and axiom dependencies.
The public results use only `propext`, `Classical.choice` and `Quot.sound`.
There are no native assertions. The source audit checks component independence,
input fingerprints and the absence of admissions.

Small coordinate checks, explicit constructions and relabellings produce
ordinary proof terms checked by Lean's kernel. The separate twelve-point
catalogue calculation also checks every isomorphism witness in the kernel.
Python proposes its data; it supplies no trusted mathematical assertions.
That theorem proves completeness of the catalogue, with no assertion that
all 68 entries are pairwise nonisomorphic.

The proof appendices for
[Stanton](coverings/11-5-2/proof.md#appendix-a-correspondence-with-lean),
[GPPT](coverings/12-6-3/proof.md#appendix-a-correspondence-with-lean) and
[C(13,7,4)](coverings/13-7-4/proof.md#appendix-a-lean-correspondence-and-dependency-checks)
give their exact contracts and formal proof organization. Each component
README links the mathematical argument and identifies its contribution.

## Verification-tool checks

The [scripts](scripts/) run verification, check inputs and regenerate explicit
witness data. The [workflow tests](tests/) and
[watchdog fixtures](lean/pilots/VerificationControls/) check these tools;
they are separate from the mathematical proofs. To run them:

```sh
./covering run --name workflow-tests --timeout 900 -- \
  python3 -B -m unittest discover -s tests -v
./covering controls
```

## Verification records

Running the workflow creates `results/library-verification.json` and its
supporting logs under `results/runs/`. These describe the exact inputs and
commands checked. An incomplete or stale record does not verify changed
sources. A newly downloaded source package should be verified locally.

The repository includes the proof sources, dependency pins, explicit data
and verification tools needed to produce a new verification. The
[source index](data/sources/manifest.jsonl) records the URLs and hashes of
the included reference papers.

## Licensing and attribution

Original project material is available under the [MIT licence](LICENSE).
The [third-party notices](THIRD_PARTY_NOTICES.md) identify the separate
licences, editions and attributions for the reference papers, covering data
and external dependencies.

## Eight optimal quadruple coverings

Read the [eight-case account](coverings/12u-plus-1-4-3/README.md), its
[proof and Lean correspondence](coverings/12u-plus-1-4-3/proof.md), and
[sources and data attribution](coverings/12u-plus-1-4-3/sources.md).
The recommended interface is
`CoveringDesigns.covering_number_one_mod_twelve_below_100_on` in
[FiniteRange.lean](lean/CoveringDesigns/QuadrupleAssembly/FiniteRange.lean).
It supplies an attaining ordinary family and a universal lower bound on
arbitrary finite labels for 4≤n<100 and n%12=1. The general assembly remains
conditional on explicit seeds; this is not an infinite-order exactness theorem.

`./covering verify quadruple-assembly` and `./covering audit quadruple-assembly`
provide focused compilation and separate record validation. Whole-library
verification includes this account. `./covering check` independently compares
all eight distributed witnesses with their Lean literals, checks the original
25-point zstd frame through exact decompression and label conversion, and checks
deterministic regeneration. The parsers and converter are external tools, not
formally verified parsers. Lean checks the actual families and their structural
correspondence. Historical source identifiers in comments and provenance JSON
are documentary; the input manifest resolves all operational files locally.

## The bound 41 ≤ C(14,5,3) ≤ 43

Read the [result account](coverings/14-5-3/README.md), its
[structural proof and Lean correspondence](coverings/14-5-3/proof.md), and
[sources and construction attribution](coverings/14-5-3/sources.md).
The principal interface is `CoveringDesigns.covering_interval_14_5_3_on`
in [C14_5_3.lean](lean/CoveringDesigns/C14_5_3.lean). It proves the universal
lower bound 41 and supplies an actual 43-block covering on arbitrary
fourteen-point labels. A separate lower interface permits repeated block
occurrences. The exact value remains undetermined.

`./covering verify 14-5-3` compiles the component, its prerequisites and its
complete theorem/axiom audit; `./covering audit 14-5-3` validates the recorded
verification separately. Whole-library verification includes the component.
`./covering check` also checks the retained historical block list against its
Lean transcription and independently tests all 364 triples. Lean proves the
attaining family's cardinality and coverage in the kernel.

## Lower bounds and exact values for $C(2k-c,k,3)$

Read the [canonical account](coverings/2k-minus-c-k-3/README.md), then its [proof and Lean correspondence](coverings/2k-minus-c-k-3/proof.md) and [sources](coverings/2k-minus-c-k-3/sources.md). The supporting proofs, audit contracts and verification inputs are included in this repository.

The full verification command above covers the first three results and all of these additional components. Each listed target also accepts `./covering verify TARGET` and `./covering audit TARGET`. Supporting audits retain their complete existing contracts and examples.

| Target | Public import |
|---|---|
| `caro-tuza` | `CoveringDesigns.CaroTuza` |
| `schoenheim` | `CoveringDesigns.Schoenheim` |
| `17-9-5` | `CoveringDesigns.C17_9_5` |
| `weighted` | `CoveringDesigns.Weighted` |
| `multicover` | `CoveringDesigns.Multicover` |
| `multicover-large-defect` | `CoveringDesigns.MulticoverLargeDefect` |
| `point-reduction` | `CoveringDesigns.PointReduction` |
| `20-11-3` | `CoveringDesigns.C20_11_3` |
| `two-k-minus-two` | `CoveringDesigns.TwoKMinusTwo` |
| `two-k-minus-two-equality` | `CoveringDesigns.TwoKMinusTwoEquality` |
| `two-k-minus-c` | `CoveringDesigns.TwoKMinusC` |
| `two-k-minus-c-general` | `CoveringDesigns.TwoKMinusCGeneral` |
| `two-k-minus-two-tightening` | `CoveringDesigns.TwoKMinusTwoTightening` |
| `rank-slack-capacity` | `CoveringDesigns.RankSlackCapacity` |
| `saturated-matching` | `CoveringDesigns.SaturatedMatching` |
| `34-18-3` | `CoveringDesigns.C34_18_3` |
| `15-6-4` | `CoveringDesigns.C15_6_4` |
| `16-7-5` | `CoveringDesigns.C16_7_5` |
| `17-8-6` | `CoveringDesigns.C17_8_6` |
| `18-9-7` | `CoveringDesigns.C18_9_7` |
| `19-10-8` | `CoveringDesigns.C19_10_8` |
| `35-19-4` | `CoveringDesigns.C35_19_4` |
| `36-20-5` | `CoveringDesigns.C36_20_5` |
| `37-21-6` | `CoveringDesigns.C37_21_6` |
| `38-22-7` | `CoveringDesigns.C38_22_7` |
| `39-23-8` | `CoveringDesigns.C39_23_8` |
| `seven-block-core` | `CoveringDesigns.SevenBlock.Core` |
| `seven-block` | `CoveringDesigns.SevenBlock` |
| `19-9-3` | `CoveringDesigns.C19_9_3` |
| `projective-link-bounds` | `CoveringDesigns.ProjectiveLinkBounds` |
