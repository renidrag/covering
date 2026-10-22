# Exact values for $C(12u+1,4,3)$, $1\le u\le8$

**Reconstruction and Lean formalisation: Rob Gardiner, with AI assistance.**

**These exact values were proved in earlier work.**
Mills's 1974 attainment result,
explicitly reported by Hartman–Mills–Mullin (1986), covers every admissible
\(n\equiv1\pmod{12}\), with Schönheim's bound proving optimality.
This project reconstructs explicit block lists and verifies the eight cases
below 100 in Lean. See the
[historical attribution and scope](sources.md#historical-result-and-project-contribution).

For every integer **4≤n<100 with n≡1 (mod 12)**, the library proves
\(C(n,4,3)=n(n-1)^2/24\): every ordinary covering has at least that
many blocks and an actual family attains it, on arbitrary finite labels.
These are exactly the eight orders below. The thirteen-point result reuses
the existing filling; twenty-five points uses a recovered historical witness;
the remaining six use one shared structural assembly. Each attaining family
is connected to its actual distributed block list.

| v | u | C(v,4,3) | Distributed witness |
| ---: | ---: | ---: | --- |
| 13 | 1 (base case) | 78 | [Existing filling JSON](../../data/quadruple-assembly/witnesses/blocks-13-4-3-78.json) |
| 25 | 2 (base case) | 600 | [Normalized historical JSON](../../data/quadruple-assembly/blocks-25-4-3-600.json) |
| 37 | 3 | 1,998 | [Original 37-point JSON](../../data/quadruple-assembly/witnesses/blocks-37-4-3-1998.json) |
| 49 | 4 | 4,704 | [49-point JSON](../../data/quadruple-assembly/witnesses/blocks-49-4-3-4704.json) |
| 61 | 5 | 9,150 | [61-point JSON](../../data/quadruple-assembly/witnesses/blocks-61-4-3-9150.json) |
| 73 | 6 | 15,768 | [73-point JSON](../../data/quadruple-assembly/witnesses/blocks-73-4-3-15768.json) |
| 85 | 7 | 24,990 | [85-point JSON](../../data/quadruple-assembly/witnesses/blocks-85-4-3-24990.json) |
| 97 | 8 | 37,248 | [97-point JSON](../../data/quadruple-assembly/witnesses/blocks-97-4-3-37248.json) |

Our contribution is the reusable assembly proof, fully checked seed instances,
six reconstructed optimal block lists, and Lean proofs connecting every named
attaining family to its distributed file. The thirteen- and twenty-five-point
lists are recovered historical constructions, also checked and connected to
the formal families. The six reconstructed lists improve the constructions
in the preserved LJCR snapshot by respectively 3, 4, 5, 6, 7 and 8 blocks.
The two small lists already attained their catalogue values.

The preserved La Jolla Covering Repository (LJCR) snapshot listed larger
constructions for those six orders, although earlier papers had established
their exact values. In the sources we inspected, we found construction
recipes but did not locate complete optimal block lists for those orders.
We reconstructed those lists and verified them and their optimality in Lean.
See [sources.md](sources.md) for the dated comparison, search scope and
attribution.

## Proof in outline

For the six cases with u≥3, pair 2u groups of six into u holes of twelve
and adjoin one common point.
Use an H(2u,6,4,3), a 3-GDD of type 12^u, the checked 78-block 13-point
filling and a one-factorisation of K6. The four actual block classes are
the H-design blocks, GDD triples with the common point, the fillings, and
unions of matched pairs in groups from different holes.

A direct coverage argument and exact incidence counts give an upper budget
of 6u²(12u+1). The three Schönheim ceilings give the same lower bound.
Sharpness forces exact class sizes, injective source maps and pairwise
disjointness. The theorem accepts arbitrary seeds satisfying its contracts;
there is no symmetry or cross-seed compatibility assumption.

For thirteen and twenty-five points, the existing Schönheim theorem gives
ceilings (6,24,78) and (12,96,600). The reused filling and the checked
600-block historical file attain them. The parameter conditions exhaust
exactly these eight orders; 24 divides n(n−1)² in every case. The range
theorem excludes n=1 and makes no all-order seed-existence claim.

The [proof](proof.md) gives the complete argument and seed dependency table.
This is a directly proved even-case adaptation of Hartman–Mills–Mullin;
their cited odd-case theorem is not applied outside its domain. Mills's
original construction remains uninspected.

## Supporting results and data boundary

The coherent Lean entry is
[QuadrupleAssembly.lean](../../lean/CoveringDesigns/QuadrupleAssembly.lean).
It exposes the conditional ordinary-family construction, its counts and
separation, shared substitution, and all eight unconditional exactness
applications. The recommended finite-range interface is
`covering_number_one_mod_twelve_below_100_on` in
[FiniteRange.lean](../../lean/CoveringDesigns/QuadrupleAssembly/FiniteRange.lean). Each application includes
arbitrary finite labels.

Small retained designs are checked in the Lean kernel. Binary inflation,
Latin inflation and block substitution then supply the large input seeds.
The [input manifest](inputs.json) pins the authoritative files and records
each projection. The external converter is deliberately not described as a
verified JSON parser: an independent restricted-literal checker compares the
complete projected block multisets with the original JSON. Lean proves that
each of the six projected assembly families equals its labelled structural
assembly. The two small-case named families equal the literal families
checked by Lean; thirteen points reuses the existing proof unchanged. The
25-point original zstd frame, decoded one-based bytes, normalized JSON and
Lean literals are checked for exact block correspondence. File ordering
and JSON metadata are outside that family equality; point identities are kept.

Daniel M. Gordon / LJCR-derived data retain their CC BY 4.0 attribution,
including both small witnesses and the relevant seed designs. See
[sources.md](sources.md) for transformations and reuse terms.

## Build and verify

From the repository root:

```sh
./covering doctor
./covering check
./covering verify quadruple-assembly
./covering audit quadruple-assembly
```

See the shared [verification guide](../../technical-details.md) for setup.
The focused verification compiles the component and its prerequisites, checks
the full contracts and permitted axioms, and records source fingerprints.
The final audit validates those records separately; it is not another
compilation. No solver, CVKT, seed acquisition or network access is needed
with the retained local Lean dependencies. Historical-frame checking uses
Python 3.14’s standard-library `compression.zstd`.

The deterministic projection can be checked or regenerated with:

```sh
./covering run --name quadruple-projection-check --timeout 60 -- python3 scripts/quadruple_data.py --check
./covering run --name quadruple-boundary-check --timeout 60 -- python3 scripts/check_quadruple_data.py
./covering run --name quadruple-projection --timeout 60 -- python3 scripts/quadruple_data.py
```

Regeneration writes only generated Lean projections whose bytes differ. The
witness files are authoritative inputs; it does not reacquire or replace them.
The manifest records their locations and original source identifiers. Source
identifiers in retained data and Lean comments document provenance; they are
not instructions to open another repository. Every verification input is local.
