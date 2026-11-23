module

public import TetrahedronPacking.CellInput
public import Mathlib.LinearAlgebra.Matrix.Notation
import all Init.Data.String.Basic
import all Init.Data.ToString.Basic
import all Init.Data.String.Defs
import all Init.Data.Nat.ToString
import all Init.Data.Int.ToString

@[expose] public section

/-!
# Certifying the published JSON fixture

The kernel checks the canonical JSON against the record coordinates. It
checks the integer inverse and separation certificates, then applies the
spatial density theorem. The negative fixture moves a duplicate of the
first particle three periods away; its corresponding pair fails.
-/

namespace TetrahedronPacking

open Filter MeasureTheory Set Matrix
open scoped Pointwise Topology

def publishedInput : CellInput 4 := ⟨160, recordPeriod, recordVertex⟩

def remoteDuplicateInput : CellInput 4 :=
  { publishedInput with
    tetrahedra := fun i a r =>
      if i = 1 then recordVertex 0 a r + 3 * recordPeriod 1 r else recordVertex i a r }

def recordInputCell (input : CellInput 4) : IntegerCell 4 :=
  input.toIntegerCell !![84132, 297648, -164376; -200448, 27648, 317952; 274176, -202752, 59904]
    172191744
    [![1, 1, 1], ![1, -5, 1], ![1, 1, -5], ![5, -1, -1], ![1, 1, -1],
      ![1, -1, -3], ![1, -1, 1], ![1, -1, -1], ![1, 3, -1], ![3, -1, 1]]

set_option maxRecDepth 20000 in
theorem publishedInput_json :
    publishedInput.canonicalJson = include_str "../benchmarks/ceg.json" := by decide +kernel

set_option maxRecDepth 20000 in
theorem remoteDuplicateInput_json :
    remoteDuplicateInput.canonicalJson = include_str "../benchmarks/ceg-remote-duplicate.json" := by
  decide +kernel

set_option maxRecDepth 20000 in
example : publishedInput.canonicalJson ≠ remoteDuplicateInput.canonicalJson := by
  rw [publishedInput_json, remoteDuplicateInput_json]
  decide +kernel

example :
    let g := recordInputCell publishedInput
    g.periods 0 1 = 90 ∧ g.periods 0 1 ≠ 576 ∧ g.vertices 1 0 1 = -320 ∧
      g.vertices 1 0 1 ≠ (recordInputCell remoteDuplicateInput).vertices 1 0 1 := by decide +kernel

theorem publishedInput_inverse : (recordInputCell publishedInput).inverseValid := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem publishedInput_checks :
    ∀ i j, (recordInputCell publishedInput).checkPair i j = true := by decide +kernel

set_option maxRecDepth 20000 in
theorem remoteDuplicateInput_rejected :
    (recordInputCell remoteDuplicateInput).checkPair 0 1 = false := by decide +kernel

theorem publishedInput_regular :
    ∀ i, (recordInputCell publishedInput).checkRegular 460800 i = true := by decide +kernel

theorem publishedInput_spatial_density :
    let g := recordInputCell publishedInput
    let L := Submodule.span ℤ (range (g.basis publishedInput_inverse))
    Tendsto (fun R : ℝ =>
      volume.real ((⋃ p : Fin 4 × L, (p.2 : Fin 3 → ℝ) +ᵥ g.piece p.1) ∩ Metric.closedBall 0 R) /
        volume.real (Metric.closedBall (0 : Fin 3 → ℝ) R))
      atTop (𝓝 (4000 / 4671 : ℝ)) := by
  let g := recordInputCell publishedInput
  have hn : g.volumeNumerator = 884736000 := by decide +kernel
  have hd : |g.periods.det| = 172191744 := by decide +kernel
  have h := g.spatial_density_of_checks publishedInput_inverse publishedInput_checks
  rw [hn, hd] at h
  have ratio : ((884736000 : ℤ) : ℝ) / (6 * ((172191744 : ℤ) : ℝ)) = 4000 / 4671 := by
    norm_num
  simpa only [ratio] using h

#print axioms publishedInput_json
#print axioms remoteDuplicateInput_json
#print axioms remoteDuplicateInput_rejected
#print axioms publishedInput_regular
#print axioms publishedInput_spatial_density

end TetrahedronPacking
