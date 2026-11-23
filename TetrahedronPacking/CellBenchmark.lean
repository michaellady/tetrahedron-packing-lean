import TetrahedronPacking.CellDensity

/-!
# End-to-end 32-piece benchmark

This fixture repeats the four-piece record in a 2 × 2 × 2 supercell.
Lean computes every relevant shift and projection offset from the vertex
and period data. The candidate inverse and axes are checked in Lean.
-/

namespace TetrahedronPacking

open Filter MeasureTheory Set Matrix
open scoped Pointwise Topology

def doubledCell : IntegerCell 32 where
  vertices i a r :=
    let q := i.val / 4
    recordVertex ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩ a r +
      (q % 2 : ℤ) * recordPeriod 0 r + ((q / 2) % 2 : ℤ) * recordPeriod 1 r +
      ((q / 4) % 2 : ℤ) * recordPeriod 2 r
  periods := Matrix.of fun r j => 2 * recordPeriod j r
  inverseNumerator := !![84132, 297648, -164376;
    -200448, 27648, 317952; 274176, -202752, 59904]
  denominator := 344383488
  axes := [![1, 1, 1], ![1, -5, 1], ![1, 1, -5], ![5, -1, -1], ![1, 1, -1],
    ![1, -1, -3], ![1, -1, 1], ![1, -1, -1], ![1, 3, -1], ![3, -1, 1]]

theorem doubledCell_inverse : doubledCell.inverseValid := by decide +kernel

example : doubledCell.vertices 4 0 0 = 704 ∧ doubledCell.vertices 4 0 0 ≠ 320 := by decide

example : ({ doubledCell with denominator := 0 } : IntegerCell 32).inverseValid → False := by
  decide

example : ({ doubledCell with vertices := fun _ => doubledCell.vertices 0 } :
    IntegerCell 32).checkPair 0 1 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem doubledCell_pair_checks : ∀ i j, doubledCell.checkPair i j = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem doubledCell_regular_checks : ∀ i, doubledCell.checkRegular 460800 i = true := by
  decide +kernel

theorem doubledCell_regular (i : Fin 32) :
    (doubledCell.edgeMatrix i).det ≠ 0 ∧
      ∀ a b : Fin 4, a ≠ b →
        ∑ r, (doubledCell.realVertex i a r - doubledCell.realVertex i b r) ^ 2 = 460800 :=
  (doubledCell.regular_of_checkRegular _ i (doubledCell_regular_checks i)).2

theorem doubledCell_spatial_density :
    let L := Submodule.span ℤ (range (doubledCell.basis doubledCell_inverse))
    Tendsto (fun R : ℝ =>
      volume.real ((⋃ p : Fin 32 × L, (p.2 : Fin 3 → ℝ) +ᵥ doubledCell.piece p.1) ∩
        Metric.closedBall 0 R) / volume.real (Metric.closedBall (0 : Fin 3 → ℝ) R))
      atTop (𝓝 (4000 / 4671 : ℝ)) := by
  have hn : doubledCell.volumeNumerator = 7077888000 := by decide +kernel
  have hd : |doubledCell.periods.det| = 1377533952 := by decide +kernel
  have h := doubledCell.spatial_density_of_checks doubledCell_inverse doubledCell_pair_checks
  rw [hn, hd] at h
  norm_num at h ⊢
  exact h

#print axioms doubledCell_pair_checks
#print axioms doubledCell_regular
#print axioms doubledCell_spatial_density

end TetrahedronPacking
