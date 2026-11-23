module

public import TetrahedronPacking.CellDensity

@[expose] public section

/-!
# A conditional record-improvement certificate

The same integer data certify common edge length, nondegeneracy,
disjoint interiors of the infinite orbit, and a strict density inequality.
-/

namespace TetrahedronPacking.IntegerCell

open Filter MeasureTheory Set
open scoped Pointwise Topology

/-- Soundness for a strict improvement witness. The inequality compares
integer cross-products, with a positive period covolume supplied by h. -/
theorem regular_packing_beats_record {m : ℕ} (g : IntegerCell m) (h : g.inverseValid)
    (checks : ∀ i j, g.checkPair i j = true)
    (squaredLength : ℤ) (regular : ∀ i, g.checkRegular squaredLength i = true)
    (strict : 4000 * (6 * |g.periods.det|) < 4671 * g.volumeNumerator) :
    let L := Submodule.span ℤ (range (g.basis h))
    (∀ i, 0 < squaredLength ∧ (g.edgeMatrix i).det ≠ 0 ∧
      ∀ a b : Fin 4, a ≠ b →
        ∑ r, (g.realVertex i a r - g.realVertex i b r) ^ 2 = (squaredLength : ℝ)) ∧
    (Pairwise fun p q : Fin m × L =>
      Disjoint (interior ((p.2 : Fin 3 → ℝ) +ᵥ g.piece p.1))
        (interior ((q.2 : Fin 3 → ℝ) +ᵥ g.piece q.1))) ∧
    ∃ ρ : ℝ, 4000 / 4671 < ρ ∧
      Tendsto (fun R : ℝ =>
        volume.real ((⋃ p : Fin m × L, (p.2 : Fin 3 → ℝ) +ᵥ g.piece p.1) ∩ Metric.closedBall 0 R) /
          volume.real (Metric.closedBall (0 : Fin 3 → ℝ) R)) atTop (𝓝 ρ) := by
  exact ⟨fun i => g.regular_of_checkRegular squaredLength i (regular i),
    g.pairwise_disjoint_of_checks h checks, g.beats_record_of_checks h checks strict⟩

#print axioms regular_packing_beats_record

end TetrahedronPacking.IntegerCell
