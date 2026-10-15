# Verifying the published proofs

This repository contains the following Lean components:

| Import | Main results |
|---|---|
| `CoveringDesigns.C11_5_2` | Minimum seven; exactly two minimum isomorphism types |
| `CoveringDesigns.C12_6_3` | Minimum fifteen; structural alternatives; separate catalogue completeness |
| `CoveringDesigns.C13_7_4` | Minimum thirty |

Their structural dependency order is shared foundations, the eleven-point
classification, the twelve-point reduction, then the thirteen-point proof.
The thirteen-point result uses arbitrary completions of GPPT's structural
forms. It imports neither the catalogue nor completion-verification modules.

## Set up dependencies

Install Lean **4.34.1** with Lake available on the path. Initial dependency
setup needs Python **3.12+**. From the repository root:

```sh
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

The recorded workflow uses Python **3.10+** and runs on **macOS or Linux**:

```sh
./covering doctor
./covering check
./covering verify
./covering audit
```

`doctor` checks prerequisites. `check` checks source boundaries, input hashes,
the explicit covering data and deterministic generated witnesses; it does
not verify Lean proofs. `verify` recompiles the project modules serially and
runs the component and combined Lean audits. It reuses dependency caches.
`audit` checks the resulting records against the current inputs without
rebuilding.

For a focused verification, use `./covering verify 11-5-2`,
`./covering verify 12-6-3` or `./covering verify 13-7-4`. Each includes its
prerequisites. `./covering status` reports progress; after a failed or
interrupted run, use the resume command printed by the CLI. Changed proof
inputs or verification scripts require a new verification.

Commands have time limits and, by default, a sampled aggregate process-group
memory limit of **8192 MiB**. The sampled limit can overshoot a brief peak.
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

The [Lean verification workflow](.github/workflows/lean-verification.yml)
runs on pushes, pull requests and manual dispatch. It exports `ELAN_TOOLCHAIN`
from `lean/lean-toolchain` for every later step, so commands launched from the
repository root use the pin without requiring a configured Elan default.
It installs that toolchain and the checksum-verified dependency sources,
then fetches Mathlib's upstream build cache for the imported dependencies.
The cache downloader runs inside Mathlib to accommodate the archive-based
path dependencies; the workflow checks that their pinned revisions agree
with Mathlib's own manifest and links the cache's standard package paths
to those installed sources. It does not change either manifest.

Each run starts with no project build cache or previous verification records.
It runs the source checks, verification-tool tests and record-validation
controls, then `./covering verify --no-memory-guard` and `./covering audit`. All published components,
including the separate GPPT catalogue theorem, are compiled and audited.
The exact standard-axiom guards and theorem contracts are the same as in
local verification.

The job runs on Ubuntu with two Lean threads and a 60-minute job limit.
Dependency downloads and proof verification omit the optional process-group
memory watchdog. Lean retains its own `-M6144` setting; this is not an
aggregate process-group RSS limit. Each module has 300 seconds and each
Lean audit 60 seconds. Logs and verification
records are attached to the workflow run as downloadable artifacts for
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
./covering run --name workflow-tests --timeout 60 -- \
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
