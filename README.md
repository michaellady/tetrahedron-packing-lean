# Regular tetrahedron packing in Lean 4

This project verifies the density of the periodic packing of congruent regular tetrahedra constructed by Chen, Engel and Glotzer. Lean proves that the tetrahedra have pairwise disjoint interiors and that the fraction of covered volume in expanding axis-aligned cubes converges to exactly **4000/4671**. The literature survey in the research report found no later result determining the unrestricted optimum.

[Chen, Engel and Glotzer, *Dense crystalline dimer packings of regular tetrahedra*, Theorem 1](https://arxiv.org/abs/1001.0586v3)

## Verify the proof

With [Elan](https://github.com/leanprover/elan) installed, run these commands from the repository root. The project pins Lean 4.19.0 and a Mathlib commit.

```sh
lake exe cache get
lake build
```

The build prints the theorem's axiom dependencies.

```text
'TetrahedronPacking.record_spatial_density' depends on axioms: [propext, Classical.choice, Quot.sound]
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
It also includes [clearance certificates and rounded-particle controls](benchmarks/README.md#clearance-under-coordinate-uncertainty) for the dimer and the published quasicrystal approximant.
