import TetrahedronPacking.CellDensity

/-!
A distinct one-piece cell tests the checker on the lattice packing of
Appendix D1, density 18/49. One primitive basis column is sheared by
three times another, making valid shift coordinates reach magnitude three.
-/

namespace TetrahedronPacking

open Filter MeasureTheory Set Matrix
open scoped Pointwise Topology

def shearedLatticeCell : IntegerCell 1 where
  vertices _ := ![![3, 3, 3], ![3, -3, -3], ![-3, 3, -3], ![-3, -3, 3]]
  periods := !![3, -1, -1; 17, 6, -1; -4, -1, 6]
  inverseNumerator := !![35, 7, 7; -98, 14, -14; 7, 7, 35]
  denominator := 196
  axes := [![1, 1, -1], ![1, 1, 1], ![1, -1, 1], ![1, 0, 0],
    ![1, -1, -1], ![0, 1, 0], ![0, 0, 1]]

theorem shearedLattice_inverse : shearedLatticeCell.inverseValid := by decide +kernel

example : (![0, 3, 0] : Fin 3 → ℤ) ∈ integerShiftBox
    (shearedLatticeCell.lower 0 0) (shearedLatticeCell.upper 0 0) := by decide +kernel

example : shearedLatticeCell.checkRegular 72 0 = true := by decide +kernel

set_option maxRecDepth 20000 in
theorem shearedLattice_pair_checks : ∀ i j, shearedLatticeCell.checkPair i j = true := by
  decide +kernel

/-- A duplicate at a remote period translation must be rejected. -/
example :
    let g : IntegerCell 2 := {
      vertices := fun i a r => shearedLatticeCell.vertices 0 a r +
        if i = 1 then shearedLatticeCell.shift ![4, 0, 0] r else 0
      periods := shearedLatticeCell.periods
      inverseNumerator := shearedLatticeCell.inverseNumerator
      denominator := shearedLatticeCell.denominator
      axes := shearedLatticeCell.axes }
    g.checkPair 0 1 = false := by decide +kernel

theorem shearedLattice_spatial_density :
    let L := Submodule.span ℤ (range (shearedLatticeCell.basis shearedLattice_inverse))
    Tendsto (fun R : ℝ =>
      volume.real ((⋃ p : Fin 1 × L, (p.2 : Fin 3 → ℝ) +ᵥ shearedLatticeCell.piece p.1) ∩
        Metric.closedBall 0 R) / volume.real (Metric.closedBall (0 : Fin 3 → ℝ) R))
      atTop (𝓝 (18 / 49 : ℝ)) := by
  have hn : shearedLatticeCell.volumeNumerator = 432 := by decide +kernel
  have hd : |shearedLatticeCell.periods.det| = 196 := by decide +kernel
  have h := shearedLatticeCell.spatial_density_of_checks shearedLattice_inverse shearedLattice_pair_checks
  rw [hn, hd] at h
  convert h using 1
  norm_num

#print axioms shearedLattice_spatial_density

end TetrahedronPacking
