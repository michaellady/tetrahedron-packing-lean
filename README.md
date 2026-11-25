# Regular tetrahedron packing in Lean 4

This project verifies the density of the periodic packing of congruent regular tetrahedra constructed by Chen, Engel and Glotzer. Lean proves that the tetrahedra have pairwise disjoint interiors and that the fraction of covered volume in expanding axis-aligned cubes converges to exactly **4000/4671**. The literature survey in the research report found no later result determining the unrestricted optimum.

[Chen, Engel and Glotzer, *Dense crystalline dimer packings of regular tetrahedra*, Theorem 1](https://arxiv.org/abs/1001.0586v3)

## Verify the proof

With [Elan](https://github.com/leanprover/elan) installed, run these commands from the repository root. The project pins Lean 4.36.0 and a Mathlib commit.

```sh
lake exe cache get
lake build
```

The build prints the theorem's axiom dependencies.

```text
'TetrahedronPacking.record_spatial_density' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The [registry statement](Challenge.lean) specifies the published coordinates,
their common edge length, pairwise interior disjointness, and the density
limit. The [solution](Solution.lean) links that statement to the existing
packing proof. The Challenge contains a statement stub for Comparator and
the Solution builds independently of it.

With Bubblewrap installed, run the comparison from the repository root.

```sh
PATH="$(lean --print-prefix)/bin:$PATH" lake comparator
```

## Explore the proofs

- [Record geometry](TetrahedronPacking/RecordGeometry.lean) checks regularity and lifts finite integer separation checks to the infinite periodic packing.
- [Record density](TetrahedronPacking/RecordDensity.lean) proves the covered-volume limit.
- [Cell checker](TetrahedronPacking/CellChecker.lean) and [improvement theorem](TetrahedronPacking/CellImprovement.lean) give a verification path for a finite integer-coordinate witness that beats the published density.
- [Restricted determinant](TetrahedronPacking/RestrictedDeterminant.lean) verifies the algebraic density bound in the published double-dimer parameter region.

The exact Python replays use the standard library.

```sh
python3 replay.py
python3 benchmark_exact.py
python3 restricted_probe.py
```

The [research report](REPORT.md) documents the prior-art search, the scope of the formal results, and the benchmarks.

The [simulation benchmark](benchmarks/README.md) provides exact periodic-cell coordinates and an overlap control as JSON.

## Clearance certificate

The separate Comparator entry `comparator-clearance.json` verifies that
the expanded four-particle dimer cell remains nonoverlapping under a
coordinatewise fractional vertex error of at most `77892/10^9`. The proof
checks a finite table of integer support gaps and quantization bounds.
It compares the embedded rational reference with any perturbed fractional
vertices in an invertible cell basis. The source branch also records a
checked 82-particle example and the exact-arithmetic comparison with
HOOMD-blue. [Source and reproduction](https://github.com/michaellady/tetrahedron-packing-lean/tree/acead5a7dfe61c0037f807d42836f2c58b2a5318)
